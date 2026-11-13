/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.LocalizedPullback
public import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.PullbackBounds

/-!
# Pullback estimates for every Banach exponent

Preservation of null sets makes chart pullback decrease the essential supremum.
Together with the finite-exponent change-of-variables estimate, this supplies
a uniform bound for full-chart `Lᵖ` pullback with an arbitrary real normed target
for every `1 ≤ p ≤ ∞`. No approximation in an `L∞` or `W¹∞` norm is used.
-/

@[expose] public section

namespace SobolevSpace.WeakChangeOfVariables

open MeasureTheory
open scoped ENNReal

variable {n : ℕ} {E : OpenPartialHomeomorph ℝ^n ℝ^n}
  {F : Type*} [NormedAddCommGroup F]

/-- Essential suprema decrease under smooth chart pullback. Boundedness of the
chart domains is unnecessary for this estimate. -/
theorem eLpNorm_comp_partialHomeomorph_top_le
    (hE : ContDiff ℝ 1 E) (hSymm : ContDiff ℝ 1 E.symm)
    {f : ℝ^n → F} (hf : AEStronglyMeasurable f (domainMeasure n E.target)) :
    eLpNorm (fun x ↦ f (E x)) ∞ (domainMeasure n E.source) ≤
      eLpNorm f ∞ (domainMeasure n E.target) := by
  have hq := quasiMeasurePreserving_partialHomeomorph hE hSymm
  have hcomp : AEStronglyMeasurable (fun x ↦ f (E x)) (domainMeasure n E.source) :=
    hf.comp_quasiMeasurePreserving hq
  rw [eLpNorm_exponent_top hcomp, eLpNorm_exponent_top hf]
  exact eLpNormEssSup_le_of_ae_enorm_bound
    (hq.ae (enorm_ae_le_eLpNormEssSup f (domainMeasure n E.target)))

/-- An essentially bounded representative stays essentially bounded after chart pullback. -/
theorem memLp_top_comp_partialHomeomorph
    (hE : ContDiff ℝ 1 E) (hSymm : ContDiff ℝ 1 E.symm)
    {f : ℝ^n → F} (hf : MemLp f ∞ (domainMeasure n E.target)) :
    MemLp (fun x ↦ f (E x)) ∞ (domainMeasure n E.source) :=
  (eLpNorm_comp_partialHomeomorph_top_le hE hSymm hf.aestronglyMeasurable).trans_lt
    hf.eLpNorm_lt_top

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A bounded chart has a finite pullback bound at every Banach exponent.
At infinity the constant is one; at finite exponents it is obtained from the
inverse Jacobian on the bounded target. -/
theorem exists_eLpNorm_comp_partialHomeomorph_bound
    (hE : ContDiff ℝ 1 E) (hSymm : ContDiff ℝ 1 E.symm)
    (hTarget : Bornology.IsBounded E.target) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : ℝ^n → ℝ,
      eLpNorm (fun x ↦ f (E x)) p (domainMeasure n E.source) ≤
        C * eLpNorm f p (domainMeasure n E.target) := by
  by_cases hp : p = ∞
  · subst p
    refine ⟨1, ENNReal.one_ne_top, fun f ↦ ?_⟩
    rw [one_mul]
    by_cases hf : AEStronglyMeasurable f (domainMeasure n E.target)
    · exact eLpNorm_comp_partialHomeomorph_top_le hE hSymm hf
    · simp only [eLpNorm_of_not_aestronglyMeasurable hf, le_top]
  · exact eLpNorm_comp_partialHomeomorph_le_of_bounded_target hp hSymm hTarget

/-- The scalar change-of-variables constant, independent of the target space. Its
finite-exponent construction bounds the determinant of the inverse differential
on the closure of the target. -/
noncomputable def boundedPullbackBound
    (hE : ContDiff ℝ 1 E) (hSymm : ContDiff ℝ 1 E.symm)
    (hTarget : Bornology.IsBounded E.target) : ℝ≥0∞ :=
  (exists_eLpNorm_comp_partialHomeomorph_bound (p := p) hE hSymm hTarget).choose

/-- Bounded charts have finite pullback constants. -/
theorem boundedPullbackBound_ne_top
    (hE : ContDiff ℝ 1 E) (hSymm : ContDiff ℝ 1 E.symm)
    (hTarget : Bornology.IsBounded E.target) :
    boundedPullbackBound (p := p) hE hSymm hTarget ≠ ∞ :=
  (exists_eLpNorm_comp_partialHomeomorph_bound (p := p) hE hSymm hTarget).choose_spec.1

/-- Applying the scalar estimate to the pointwise norm gives the same chart bound
for every normed target. Strong measurability is transported by preservation of null sets. -/
theorem eLpNorm_comp_partialHomeomorph_le
    (hE : ContDiff ℝ 1 E) (hSymm : ContDiff ℝ 1 E.symm)
    (hTarget : Bornology.IsBounded E.target)
    {f : ℝ^n → F} (hf : AEStronglyMeasurable f (domainMeasure n E.target)) :
    eLpNorm (fun x ↦ f (E x)) p (domainMeasure n E.source) ≤
      boundedPullbackBound (p := p) hE hSymm hTarget *
        eLpNorm f p (domainMeasure n E.target) := by
  have hcomp := hf.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_partialHomeomorph hE hSymm)
  have hbound :=
    (exists_eLpNorm_comp_partialHomeomorph_bound (p := p) hE hSymm hTarget).choose_spec.2
      (fun x ↦ ‖f x‖)
  calc
    eLpNorm (fun x ↦ f (E x)) p (domainMeasure n E.source) =
        eLpNorm (fun x ↦ ‖f (E x)‖) p (domainMeasure n E.source) :=
      (eLpNorm_norm _ hcomp).symm
    _ ≤ _ := by simpa only [boundedPullbackBound, eLpNorm_norm _ hf] using hbound

/-- The full source of a bounded chart preserves `Lᵖ`, including `L∞`. -/
theorem memLp_comp_partialHomeomorph_on_bounded_chart
    (hE : ContDiff ℝ 1 E) (hSymm : ContDiff ℝ 1 E.symm)
    (hTarget : Bornology.IsBounded E.target)
    {f : ℝ^n → F} (hf : MemLp f p (domainMeasure n E.target)) :
    MemLp (fun x ↦ f (E x)) p (domainMeasure n E.source) :=
  (eLpNorm_comp_partialHomeomorph_le hE hSymm hTarget hf.aestronglyMeasurable).trans_lt
    (ENNReal.mul_lt_top (boundedPullbackBound_ne_top hE hSymm hTarget).lt_top
      hf.eLpNorm_lt_top)

end SobolevSpace.WeakChangeOfVariables
