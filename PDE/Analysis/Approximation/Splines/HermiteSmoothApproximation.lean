/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Mollification.SmoothOdd
public import PDE.Analysis.Approximation.Splines.HermiteEndpointFlattening
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-!
# Smooth initialization from finite Hermite data

The assembled compact odd profile is first flattened at its endpoints and then
mollified away from its first cubic. This gives compact smooth odd functions
with arbitrarily small singular weighted squared `H¹` error. The prescribed
backward endpoint slope is unrestricted; the comparisons for the input weights
are hypotheses.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped Topology NNReal ENNReal ContDiff
open PDE.Analysis.Calculus

namespace CAS.Splines.HermiteData

variable {panels : ℕ}
variable (data : HermiteData (panels + 1)) (mesh : StrictKnotMesh (panels + 1))

/-- Exact finite Hermite data produce smooth initial functions, preserving the first
physical cubic and its origin slope. The small-error conclusion is proved by cutoff
and convolution, not supplied as an input approximation hypothesis. -/
theorem exists_compactOddProfile_smooth_initialization
    (hmesh : mesh.knot 0 = 0) (hzero : data.value 0 = 0)
    (hend : data.value (Fin.last (panels + 1)) = 0)
    (heq : data.C2SlopeEquations mesh) (hnatural : data.NaturalOriginRow mesh)
    {w v : ℝ → ℝ} {c A B ε : ℝ}
    (hc : 0 < c) (hcL : c < mesh.knot (Fin.last (panels + 1)))
    (hε : 0 < ε) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hw : Measurable w) (hv : Measurable v)
    (hw0 : ∀ x ∈ Ioo 0 (mesh.knot (Fin.last (panels + 1))), 0 ≤ w x)
    (hv0 : ∀ x ∈ Ioo 0 (mesh.knot (Fin.last (panels + 1))), 0 ≤ v x)
    (hwc : ContinuousOn w (Ioo 0 (mesh.knot (Fin.last (panels + 1)))))
    (hvc : ContinuousOn v (Ioo 0 (mesh.knot (Fin.last (panels + 1)))))
    (hwL : ∀ x ∈ Ioo (mesh.knot (Fin.last (panels + 1)) - c)
      (mesh.knot (Fin.last (panels + 1))),
      w x ≤ A / (mesh.knot (Fin.last (panels + 1)) - x) ^ 2)
    (hvL : ∀ x ∈ Ioo (mesh.knot (Fin.last (panels + 1)) - c)
      (mesh.knot (Fin.last (panels + 1))), v x ≤ B) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      (∀ x, g (-x) = -g x) ∧
      tsupport g ⊆ Ioo (-(mesh.knot (Fin.last (panels + 1))))
        (mesh.knot (Fin.last (panels + 1))) ∧
      g =ᶠ[𝓝 0] ((data.polynomialData mesh).piece 0).eval ∧
      deriv g 0 = data.slope 0 ∧
      deriv (fun x ↦ g x - data.compactOddProfile mesh x) 0 = 0 ∧
      singularWeightedH1Error w v (fun x ↦ g x - data.compactOddProfile mesh x)
        (mesh.knot (Fin.last (panels + 1))) < ENNReal.ofReal ε := by
  obtain ⟨K, hK⟩ := data.exists_lipschitzWith_compactOddProfile mesh hmesh
  have hfL : data.compactOddProfile mesh (mesh.knot (Fin.last (panels + 1))) = 0 := by
    simpa only [hend] using
      data.compactOddProfile_knot mesh hmesh hzero (Fin.last (panels + 1))
  have hp : ContDiff ℝ ∞ ((data.polynomialData mesh).piece 0).eval := by
    simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using
      ((data.polynomialData mesh).piece 0).contDiff_aeval (𝕜 := ℝ) ∞
  obtain ⟨g, hg, hgc, hgo, hgs, hgp, hgd, hqd, hE⟩ :=
    exists_smooth_odd_initialization hK hfL (data.compactOddProfile_neg mesh)
      ((data.contDiffOn_two_compactOddProfile mesh hmesh hzero heq hnatural).of_le
        (by norm_num))
      hp (data.first_piece_odd mesh hmesh hzero hnatural)
      (data.compactOddProfile_eventuallyEq_first_piece mesh hmesh hzero hnatural)
      hc hcL hε hA hB hw hv hw0 hv0 hwc hvc hwL hvL
  exact ⟨g, hg, hgc, hgo, hgs, hgp,
    hgd.trans (data.deriv_compactOddProfile_zero mesh hmesh), hqd, hE⟩

/-- Any initializer retaining a nonzero origin slope is itself nonzero. -/
theorem ne_zero_of_deriv_eq_slope {g : ℝ → ℝ} (hg : deriv g 0 = data.slope 0)
    (hslope : data.slope 0 ≠ 0) : g ≠ 0 := by
  intro hzero
  simp [hzero] at hg
  exact hslope hg.symm

end CAS.Splines.HermiteData
