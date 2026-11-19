/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.EndpointFlattening
public import PDE.Analysis.Approximation.Splines.HermiteOriginRegularity

/-!
# Singular weighted endpoint approximation of the assembled Hermite profile

Finite Hermite data with the exact interior slope equations and natural origin row
give compact odd globally `C²` endpoint flattenings. The weighted error can be made
arbitrarily small, and the first cubic and its origin slope are preserved exactly.
No condition is imposed on the final nodal slope.

Interior knot smoothing, needed for `C∞` initial data, is in `HermiteSmoothApproximation`.
-/

@[expose] public section

noncomputable section

open Set
open scoped Topology NNReal ENNReal
open PDE.Analysis.Calculus

namespace CAS.Splines.HermiteData

variable {panels : ℕ}
variable (data : HermiteData (panels + 1)) (mesh : StrictKnotMesh (panels + 1))

/-- The derivative at zero is the prescribed first nodal slope, without a condition on
the first nodal value or the natural origin row. -/
theorem deriv_compactOddProfile_zero (hmesh : mesh.knot 0 = 0) :
    deriv (data.compactOddProfile mesh) 0 = data.slope 0 := by
  let p := (data.polynomialData mesh).piece 0
  have hleft : mesh.panelLeft 0 = 0 := hmesh
  have hright : 0 < mesh.panelRight 0 := by
    simpa only [hleft] using mesh.panelLeft_lt_panelRight 0
  have hlast : mesh.panelRight 0 ≤ mesh.knot (Fin.last (panels + 1)) :=
    mesh.strictMono_knot.monotone (Fin.le_last _)
  have hpos {x : ℝ} (hx : x ∈ Icc 0 (mesh.panelRight 0)) :
      data.compactOddProfile mesh x = p.eval x - p.eval 0 := by
    rw [compactOddProfile, compactOddExtension,
      intervalTruncation_eq_min_max (last_knot_pos mesh hmesh).le,
      intervalTruncation_eq_min_max (last_knot_pos mesh hmesh).le]
    simp only [max_eq_right hx.1, min_eq_right (hx.2.trans hlast),
      max_eq_left (neg_nonpos.mpr hx.1), min_eq_right (last_knot_pos mesh hmesh).le]
    rw [data.assembledEvaluator_eq_piece mesh 0 (by simpa only [hleft] using hx),
      data.assembledEvaluator_eq_piece mesh 0 (by simpa only [hleft] using
        (show (0 : ℝ) ∈ Icc 0 (mesh.panelRight 0) from ⟨le_rfl, hright.le⟩))]
  have hs := data.slope_left mesh 0
  have hp : HasDerivAt p.eval (data.slope 0) 0 := by
    convert p.hasDerivAt 0 using 1
    simpa [p, polynomialJet, hleft] using hs.symm
  have hposDeriv : HasDerivWithinAt (data.compactOddProfile mesh)
      (data.slope 0) (Ici 0) 0 := by
    apply (hp.sub_const (p.eval 0)).hasDerivWithinAt.congr_of_eventuallyEq_of_mem
    · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hright), self_mem_nhdsWithin]
        with x hx hx0
      exact hpos ⟨hx0, hx.le⟩
    · exact le_rfl
  -- Odd reflection has the same left derivative as the right derivative.
  have hnegDeriv : HasDerivWithinAt (data.compactOddProfile mesh)
      (data.slope 0) (Iic 0) 0 := by
    have h := (hposDeriv.comp_of_eq 0 (hasDerivWithinAt_neg (0 : ℝ) (Iic 0))
      (fun x hx ↦ neg_nonneg.mpr hx) (neg_zero.symm)).neg
    simpa only [Function.comp_def, Pi.neg_def, compactOddProfile_neg, neg_neg,
      mul_neg_one] using h
  have hd : HasDerivAt (data.compactOddProfile mesh) (data.slope 0) 0 := by
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hnegDeriv.union hposDeriv
  exact hd.deriv

/-- A family of compact odd `C²` approximations in the two singular weighted
energy terms. The first physical cubic survives unchanged on a neighborhood of zero.

The only weight hypotheses are endpoint upper comparisons; the error estimate is
derived from the constructed cutoff and the proved Lipschitz property of the assembled
profile. The endpoint slopes are unrestricted. -/
theorem exists_compactOddProfile_endpoint_approximation
    (hmesh : mesh.knot 0 = 0) (hzero : data.value 0 = 0)
    (hend : data.value (Fin.last (panels + 1)) = 0)
    (heq : data.C2SlopeEquations mesh) (hnatural : data.NaturalOriginRow mesh)
    {w v : ℝ → ℝ} {r A B ε : ℝ}
    (hr : 0 < r) (hrL : r < mesh.knot (Fin.last (panels + 1)))
    (hε : 0 < ε) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hw : ∀ x ∈ Ioo (mesh.knot (Fin.last (panels + 1)) - r)
      (mesh.knot (Fin.last (panels + 1))),
      w x ≤ A / (mesh.knot (Fin.last (panels + 1)) - x) ^ 2)
    (hv : ∀ x ∈ Ioo (mesh.knot (Fin.last (panels + 1)) - r)
      (mesh.knot (Fin.last (panels + 1))), v x ≤ B) :
    ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      (∀ x, g (-x) = -g x) ∧
      tsupport g ⊆ Icc (-(mesh.knot (Fin.last (panels + 1))))
        (mesh.knot (Fin.last (panels + 1))) ∧
      g =ᶠ[𝓝 0] ((data.polynomialData mesh).piece 0).eval ∧
      deriv g 0 = data.slope 0 ∧
      singularWeightedH1Error w v (fun x ↦ g x - data.compactOddProfile mesh x)
        (mesh.knot (Fin.last (panels + 1))) < ENNReal.ofReal ε := by
  let L := mesh.knot (Fin.last (panels + 1))
  let f := data.compactOddProfile mesh
  obtain ⟨K, hK⟩ := data.exists_lipschitzWith_compactOddProfile mesh hmesh
  have hfL : f L = 0 := by
    simpa only [f, L, hend] using
      data.compactOddProfile_knot mesh hmesh hzero (Fin.last (panels + 1))
  have hregular : ContDiffOn ℝ 2 f (Ioo (-L) L) :=
    data.contDiffOn_two_compactOddProfile mesh hmesh hzero heq hnatural
  have hfd : ∀ x ∈ Ioo 0 L, DifferentiableAt ℝ f x := by
    intro x hx
    have hL : 0 < L := last_knot_pos mesh hmesh
    have hx' : x ∈ Ioo (-L) L := ⟨(neg_lt_zero.mpr hL).trans hx.1, hx.2⟩
    exact (hregular.contDiffAt (Ioo_mem_nhds hx'.1 hx'.2)).differentiableAt (by norm_num)
  obtain ⟨δ, hδ, hδr, hg, hgc, hodd, _, hslope, herror⟩ :=
    exists_flattenedProfile_error_lt hK hfL (data.compactOddProfile_neg mesh)
      hregular hfd hr hrL hε hA hB hw hv
  refine ⟨flattenedProfile f L δ, hg, hgc, hodd, ?_, ?_, ?_, herror⟩
  · apply (tsupport_flattenedProfile_subset hδ).trans
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  · exact (flattenedProfile_eventuallyEq_self hδ (hδr.trans hrL)).trans
      (data.compactOddProfile_eventuallyEq_first_piece mesh hmesh hzero hnatural)
  · exact hslope.trans (data.deriv_compactOddProfile_zero mesh hmesh)

end CAS.Splines.HermiteData
