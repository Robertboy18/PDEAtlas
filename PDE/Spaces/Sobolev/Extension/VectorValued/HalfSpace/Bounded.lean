/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.VectorValued.HalfSpace.Lp

/-!
# Essential bounds for weighted half-space reflection

The physical reflection used by the Sobolev extension preserves essential
boundedness even when it is constructed on `Lp` for a different exponent.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.VectorValued.HigherOrderReflection

open GraphSpace.HigherOrderReflection

variable (n k : ℕ) [Fact (0 < n)] (p : ℝ≥0∞) [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual weighted reflection operator on `Lp` preserves an essential
bound; no compatibility between independently chosen extensions is assumed. -/
theorem exists_ae_bound_weightedExtendLp (r : ℕ)
    (u : Lp F p (domainMeasure n ℝ^n₊)) {B : ℝ}
    (hB : ∀ᵐ x ∂domainMeasure n ℝ^n₊, ‖u x‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂domainMeasure n univ,
      ‖weightedExtendLp n k p r u x‖ ≤ C := by
  classical
  let R := max B 0
  let a (j : Fin (k + 1)) := reflectionCoeff k j * reflectionNode k j ^ r
  have hR : 0 ≤ R := le_max_right _ _
  have hb : ∀ᵐ x ∂domainMeasure n ℝ^n₊, ‖u x‖ ≤ R :=
    hB.mono fun _ hx ↦ hx.trans (le_max_left _ _)
  have hd (j : Fin (k + 1)) : ∀ᵐ x ∂domainMeasure n ℝ^n₋,
      ‖u (normalDilation (PDE.Common.lastIndex (n := n)) (reflectionNode k j) x)‖ ≤ R := by
    have hq : QuasiMeasurePreserving
        (normalDilation (PDE.Common.lastIndex (n := n)) (reflectionNode k j))
        (domainMeasure n ℝ^n₋) (domainMeasure n ℝ^n₊) :=
      ⟨(normalDilation _ _).continuous.measurable, by
        rw [map_lower_normalDilation n _ (reflectionNode_neg k j)]
        exact Measure.smul_absolutelyContinuous⟩
    exact hq.tendsto_ae hb
  let C := R + ∑ j : Fin (k + 1), ‖a j‖ * R
  refine ⟨C, add_nonneg hR (Finset.sum_nonneg fun _ _ ↦ mul_nonneg (norm_nonneg _) hR), ?_⟩
  have hu := (ae_restrict_iff' (HalfSpace.measurableSet_upper (n := n))).mp hb
  have hl := (ae_restrict_iff' (HalfSpace.measurableSet_lower (n := n))).mp
    (ae_all_iff.mpr hd)
  simp only [domainMeasure, Measure.restrict_univ]
  filter_upwards [weightedExtendLp_apply_ae n k p r u, hu, hl] with x hx hu hl
  rw [hx]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · by_cases h : x ∈ ℝ^n₊
    · simpa only [indicator_of_mem h] using hu h
    · simpa only [indicator_of_notMem h, norm_zero] using hR
  · by_cases h : x ∈ ℝ^n₋
    · rw [indicator_of_mem h]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hl h j) (norm_nonneg _)
    · rw [indicator_of_notMem h, norm_zero]
      exact Finset.sum_nonneg fun _ _ ↦ mul_nonneg (norm_nonneg _) hR

end SobolevSpace.VectorValued.HigherOrderReflection
