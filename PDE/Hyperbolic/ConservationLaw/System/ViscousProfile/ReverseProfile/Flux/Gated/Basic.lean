/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.Deriv.Support
public import PDE.Common.Euclidean

import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# Reflected gated fluxes in three dimensions

The scalar functions `k`, `g`, `C`, `φ` and `b` define a flux on all of
`ℝ^3`. The middle feedback uses the reflected cutoff `C (-y)`, and the last
component uses the reflected shear `-b (-y)`. The Jacobian retains both
state-dependent shear-derivative columns.

A positive gate contains the topological support of `b`, lies above the zero
plateau of `C`, and is disjoint from its negative reflection. Plateau and support
lemmas give the product identities needed for the later spectral calculation.
They impose no sign or amplitude restriction on `b`.
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System.GatedFlux

open Filter Set
open scoped ContDiff Topology

/-- The reflected three-dimensional flux with scalar fast law and gated feedback. -/
def flux (k g C φ b : ℝ → ℝ) (q : ℝ^3) : ℝ^3 :=
  !₂[-k (q 0) + b (q 1) * q 2, g (q 1) + C (-q 1) * φ (q 2) + C (q 1) * φ (q 0),
    k (q 2) - b (-q 1) * q 0]

/-- The middle diagonal entry of the flux Jacobian. -/
def middleSpeed (g C φ : ℝ → ℝ) (q : ℝ^3) : ℝ :=
  deriv g (q 1) - deriv C (-q 1) * φ (q 2) + deriv C (q 1) * φ (q 0)

/-- The scalar curvature expression for the middle flux component. -/
def middleCurvature (g C φ : ℝ → ℝ) (q : ℝ^3) : ℝ :=
  deriv (deriv g) (q 1) + deriv (deriv C) (-q 1) * φ (q 2) + deriv (deriv C) (q 1) * φ (q 0)

/-- The first flux component couples the positive gate to the third coordinate. -/
@[simp]
theorem flux_zero (k g C φ b : ℝ → ℝ) (q : ℝ^3) :
    flux k g C φ b q 0 = -k (q 0) + b (q 1) * q 2 := by
  simp [flux]

/-- The middle component contains both scalar feedbacks. -/
@[simp]
theorem flux_one (k g C φ b : ℝ → ℝ) (q : ℝ^3) :
    flux k g C φ b q 1 = g (q 1) + C (-q 1) * φ (q 2) + C (q 1) * φ (q 0) := by
  simp [flux]

/-- The last component uses the negative reflection of the same gate. -/
@[simp]
theorem flux_two (k g C φ b : ℝ → ℝ) (q : ℝ^3) :
    flux k g C φ b q 2 = k (q 2) - b (-q 1) * q 0 := by
  simp [flux]

/-- The flux inherits every differentiability order of its scalar ingredients,
including `n = ∞`. -/
theorem contDiff_flux {k g C φ b : ℝ → ℝ} {n : WithTop ℕ∞} (hk : ContDiff ℝ n k)
    (hg : ContDiff ℝ n g) (hC : ContDiff ℝ n C) (hφ : ContDiff ℝ n φ) (hb : ContDiff ℝ n b) :
    ContDiff ℝ n (flux k g C φ b) := by
  have hcoord (i : Fin 3) : ContDiff ℝ n (fun q : ℝ^3 ↦ q i) := contDiff_piLp_apply (2 : ENNReal)
  rw [contDiff_piLp]
  intro i
  fin_cases i
  · change ContDiff ℝ n (fun q : ℝ^3 ↦ -k (q 0) + b (q 1) * q 2)
    exact (hk.comp (hcoord 0)).neg.add ((hb.comp (hcoord 1)).mul (hcoord 2))
  · change ContDiff ℝ n (fun q : ℝ^3 ↦ g (q 1) + C (-q 1) * φ (q 2) + C (q 1) * φ (q 0))
    exact ((hg.comp (hcoord 1)).add ((hC.comp ((hcoord 1).neg)).mul (hφ.comp (hcoord 2)))).add
        ((hC.comp (hcoord 1)).mul (hφ.comp (hcoord 0)))
  · change ContDiff ℝ n (fun q : ℝ^3 ↦ k (q 2) - b (-q 1) * q 0)
    exact (hk.comp (hcoord 2)).sub ((hb.comp ((hcoord 1).neg)).mul (hcoord 0))

/-- The full Jacobian action uses only differentiability at the scalar arguments
being evaluated. Differentiating `-b (-y) * x` gives the positive term `b' (-y) * x`
in the middle column. -/
theorem fderiv_flux_apply {k g C φ b : ℝ → ℝ} {q v : ℝ^3} (hkx : DifferentiableAt ℝ k (q 0))
    (hkz : DifferentiableAt ℝ k (q 2)) (hg : DifferentiableAt ℝ g (q 1))
    (hCy : DifferentiableAt ℝ C (q 1)) (hCny : DifferentiableAt ℝ C (-q 1))
    (hφx : DifferentiableAt ℝ φ (q 0)) (hφz : DifferentiableAt ℝ φ (q 2))
    (hby : DifferentiableAt ℝ b (q 1)) (hbny : DifferentiableAt ℝ b (-q 1)) :
    fderiv ℝ (flux k g C φ b) q v =
      !₂[-deriv k (q 0) * v 0 + deriv b (q 1) * q 2 * v 1 + b (q 1) * v 2,
        C (q 1) * deriv φ (q 0) * v 0 + middleSpeed g C φ q * v 1 +
          C (-q 1) * deriv φ (q 2) * v 2,
        -b (-q 1) * v 0 + deriv b (-q 1) * q 0 * v 1 + deriv k (q 2) * v 2] := by
  have hx := PiLp.hasFDerivAt_apply (𝕜 := ℝ) (2 : ENNReal) q (0 : Fin 3)
  have hy := PiLp.hasFDerivAt_apply (𝕜 := ℝ) (2 : ENNReal) q (1 : Fin 3)
  have hz := PiLp.hasFDerivAt_apply (𝕜 := ℝ) (2 : ENNReal) q (2 : Fin 3)
  have hzero := (hkx.hasDerivAt.comp_hasFDerivAt q hx).neg.add
    ((hby.hasDerivAt.comp_hasFDerivAt q hy).mul hz)
  have hone := ((hg.hasDerivAt.comp_hasFDerivAt q hy).add
    ((hCny.hasDerivAt.comp_hasFDerivAt q hy.neg).mul (hφz.hasDerivAt.comp_hasFDerivAt q hz))).add
        ((hCy.hasDerivAt.comp_hasFDerivAt q hy).mul (hφx.hasDerivAt.comp_hasFDerivAt q hx))
  have htwo := (hkz.hasDerivAt.comp_hasFDerivAt q hz).sub
    ((hbny.hasDerivAt.comp_hasFDerivAt q hy.neg).mul hx)
  have hflux : DifferentiableAt ℝ (flux k g C φ b) q := by
    rw [differentiableAt_piLp]
    intro i
    fin_cases i
    · change DifferentiableAt ℝ (fun p : ℝ^3 ↦ -k (p 0) + b (p 1) * p 2) q
      exact hzero.differentiableAt
    · change DifferentiableAt ℝ (fun p : ℝ^3 ↦ g (p 1) + C (-p 1) * φ (p 2) + C (p 1) * φ (p 0)) q
      exact hone.differentiableAt
    · change DifferentiableAt ℝ (fun p : ℝ^3 ↦ k (p 2) - b (-p 1) * p 0) q
      exact htwo.differentiableAt
  ext i
  have hcoordinate : fderiv ℝ (fun p : ℝ^3 ↦ flux k g C φ b p i) q v =
        fderiv ℝ (flux k g C φ b) q v i := by
    have h := congrArg (fun L : ℝ^3 →L[ℝ] ℝ ↦ L v) (((hasFDerivWithinAt_piLp (2 : ENNReal)).mp
        (hasFDerivWithinAt_univ.mpr hflux.hasFDerivAt) i
          |>.hasFDerivAt_of_univ).fderiv)
    simpa [ContinuousLinearMap.comp_apply, PiLp.proj_apply] using h
  rw [← hcoordinate]
  fin_cases i
  · change fderiv ℝ (fun p : ℝ^3 ↦ -k (p 0) + b (p 1) * p 2) q v =
      -deriv k (q 0) * v 0 + deriv b (q 1) * q 2 * v 1 + b (q 1) * v 2
    have h := congrArg (fun L : ℝ^3 →L[ℝ] ℝ ↦ L v) hzero.fderiv
    change fderiv ℝ (fun p : ℝ^3 ↦ -k (p 0) + b (p 1) * p 2) q v = _ at h
    rw [h]
    simp only [Fin.isValue, Function.comp_apply, add_apply, neg_apply, smul_apply, PiLp.proj_apply,
      smul_eq_mul, neg_mul]
    ring
  · change fderiv ℝ (fun p : ℝ^3 ↦ g (p 1) + C (-p 1) * φ (p 2) + C (p 1) * φ (p 0)) q v =
        C (q 1) * deriv φ (q 0) * v 0 + middleSpeed g C φ q * v 1 + C (-q 1) * deriv φ (q 2) * v 2
    have h := congrArg (fun L : ℝ^3 →L[ℝ] ℝ ↦ L v) hone.fderiv
    change fderiv ℝ (fun p : ℝ^3 ↦ g (p 1) + C (-p 1) * φ (p 2) + C (p 1) * φ (p 0)) q v = _ at h
    rw [h]
    simp only [Fin.isValue, Function.comp_apply, Pi.neg_apply, smul_neg, add_apply, smul_apply,
      PiLp.proj_apply, smul_eq_mul, neg_apply, middleSpeed]
    ring
  · change fderiv ℝ (fun p : ℝ^3 ↦ k (p 2) - b (-p 1) * p 0) q v =
      -b (-q 1) * v 0 + deriv b (-q 1) * q 0 * v 1 + deriv k (q 2) * v 2
    have h := congrArg (fun L : ℝ^3 →L[ℝ] ℝ ↦ L v) htwo.fderiv
    change fderiv ℝ (fun p : ℝ^3 ↦ k (p 2) - b (-p 1) * p 0) q v = _ at h
    rw [h]
    simp only [Fin.isValue, Function.comp_apply, Pi.neg_apply, smul_neg, sub_apply, smul_apply,
      PiLp.proj_apply, smul_eq_mul, add_apply, neg_apply, neg_mul]
    ring

/-- A cutoff vanishes against a gate supported strictly inside its zero plateau. -/
theorem cutoff_mul_gate_eq_zero {C b : ℝ → ℝ} {d e : ℝ} (hC : ∀ s, d ≤ s → C s = 0)
    (hb : tsupport b ⊆ Ioo d e) (y : ℝ) :
    C y * b y = 0 := by
  by_cases hy : y ∈ tsupport b
  · rw [hC y (hb hy).1.le, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]

/-- Differentiating a gate does not enlarge its topological support. -/
theorem cutoff_mul_deriv_gate_eq_zero {C b : ℝ → ℝ} {d e : ℝ} (hC : ∀ s, d ≤ s → C s = 0)
    (hb : tsupport b ⊆ Ioo d e) (y : ℝ) :
    C y * deriv b y = 0 :=
  cutoff_mul_gate_eq_zero hC ((tsupport_deriv_subset (f := b)).trans hb) y

/-- The derivative of a cutoff also vanishes throughout the gate's support. -/
theorem deriv_cutoff_mul_gate_eq_zero {C b : ℝ → ℝ} {d e : ℝ} (hC : ∀ s, d ≤ s → C s = 0)
    (hb : tsupport b ⊆ Ioo d e) (y : ℝ) :
    deriv C y * b y = 0 := by
  by_cases hy : y ∈ tsupport b
  · have hnear : C =ᶠ[𝓝 y] fun _ ↦ (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds (hb hy).1] with s hs using hC s hs.le
    have hderiv := ((hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hnear).deriv
    rw [hderiv, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]

/-- Cutoff and gate derivatives have disjoint activity. -/
theorem deriv_cutoff_mul_deriv_gate_eq_zero {C b : ℝ → ℝ} {d e : ℝ} (hC : ∀ s, d ≤ s → C s = 0)
    (hb : tsupport b ⊆ Ioo d e) (y : ℝ) :
    deriv C y * deriv b y = 0 :=
  deriv_cutoff_mul_gate_eq_zero hC ((tsupport_deriv_subset (f := b)).trans hb) y

/-- A gate supported in the positive ray is disjoint from its negative reflection. -/
theorem gate_mul_reflection_eq_zero
    {b : ℝ → ℝ} {d e : ℝ} (hd : 0 ≤ d) (hb : tsupport b ⊆ Ioo d e) (y : ℝ) :
    b y * b (-y) = 0 := by
  by_cases hy : y ∈ tsupport b
  · have hneg : -y ∉ tsupport b := by
      intro hny
      have hypos := (hb hy).1
      have hnypos := (hb hny).1
      linarith
    rw [image_eq_zero_of_notMem_tsupport hneg, mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]

/-- A cutoff constant to the left of a positive level has disjoint derivative
activity from its reflection. -/
theorem deriv_cutoff_mul_deriv_reflection_eq_zero {C : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hC : ∀ s, s ≤ a → C s = 1) (y : ℝ) :
    deriv C y * deriv C (-y) = 0 := by
  have hderiv (s : ℝ) (hs : s < a) : deriv C s = 0 := by
    have hnear : C =ᶠ[𝓝 s] fun _ ↦ (1 : ℝ) := by
      filter_upwards [Iio_mem_nhds hs] with t ht using hC t ht.le
    exact ((hasDerivAt_const s (1 : ℝ)).congr_of_eventuallyEq hnear).deriv
  by_cases hy : y < a
  · rw [hderiv y hy, zero_mul]
  · have hny : -y < a := by
      have hay := le_of_not_gt hy
      linarith
    rw [hderiv (-y) hny, mul_zero]

/-- Every middle coordinate lies in the positive gate, its negative reflection,
or a region where both shears and both shear derivatives vanish. Plateau values
and derivatives are included in the two active cases. -/
theorem gate_partition {C b : ℝ → ℝ} {a d e : ℝ} (ha : 0 < a) (had : a < d)
    (hleft : ∀ s, s ≤ a → C s = 1) (hright : ∀ s, d ≤ s → C s = 0) (hb : tsupport b ⊆ Ioo d e)
    (y : ℝ) :
    (y ∈ Ioo d e ∧ C y = 0 ∧ deriv C y = 0 ∧ C (-y) = 1 ∧
      deriv C (-y) = 0 ∧ b (-y) = 0 ∧ deriv b (-y) = 0) ∨
    (-y ∈ Ioo d e ∧ C (-y) = 0 ∧ deriv C (-y) = 0 ∧ C y = 1 ∧
      deriv C y = 0 ∧ b y = 0 ∧ deriv b y = 0) ∨
    (b y = 0 ∧ deriv b y = 0 ∧ b (-y) = 0 ∧ deriv b (-y) = 0) := by
  have hout (s : ℝ) (hs : s ∉ Ioo d e) : b s = 0 ∧ deriv b s = 0 := by
    have hsupport : s ∉ tsupport b := fun h ↦ hs (hb h)
    exact ⟨image_eq_zero_of_notMem_tsupport hsupport, deriv_of_notMem_tsupport hsupport⟩
  have hleft_deriv (s : ℝ) (hs : s < a) : deriv C s = 0 := by
    have hnear : C =ᶠ[𝓝 s] fun _ ↦ (1 : ℝ) := by
      filter_upwards [Iio_mem_nhds hs] with t ht using hleft t ht.le
    exact ((hasDerivAt_const s (1 : ℝ)).congr_of_eventuallyEq hnear).deriv
  have hright_deriv (s : ℝ) (hs : d < s) : deriv C s = 0 := by
    have hnear : C =ᶠ[𝓝 s] fun _ ↦ (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hs] with t ht using hright t ht.le
    exact ((hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq hnear).deriv
  have hpositive (s : ℝ) (hs : s ∈ Ioo d e) :
      C s = 0 ∧ deriv C s = 0 ∧ C (-s) = 1 ∧ deriv C (-s) = 0 ∧ b (-s) = 0 ∧ deriv b (-s) = 0 := by
    have hneg_left : -s < a := by linarith [hs.1]
    have hneg_out : -s ∉ Ioo d e := by
      intro hneg
      linarith [hs.1, hneg.1]
    obtain ⟨hbneg, hdbneg⟩ := hout (-s) hneg_out
    exact ⟨hright s hs.1.le, hright_deriv s hs.1,
      hleft (-s) hneg_left.le, hleft_deriv (-s) hneg_left, hbneg, hdbneg⟩
  by_cases hy : y ∈ Ioo d e
  · exact Or.inl ⟨hy, hpositive y hy⟩
  · by_cases hny : -y ∈ Ioo d e
    · refine Or.inr (Or.inl ⟨hny, ?_⟩)
      simpa only [neg_neg] using hpositive (-y) hny
    · obtain ⟨hby, hdby⟩ := hout y hy
      obtain ⟨hbny, hdbny⟩ := hout (-y) hny
      exact Or.inr (Or.inr ⟨hby, hdby, hbny, hdbny⟩)

end PDE.Hyperbolic.ConservationLaw.System.GatedFlux
