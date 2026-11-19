/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.Cutoff.Bounds

/-!
# Fréchet derivative bounds for expanding cutoffs

The derivative of the fixed bump is bounded by compactness. Rescaling its argument
by `R⁻¹` gives an operator norm bound of order `R⁻¹`, uniform in the spatial point.
This controls the product-rule error when truncating a vector-valued function.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Approximation

open PDE.Analysis (standardBump)

/-- A single constant bounds the Fréchet derivatives of all positive-scale cutoffs. -/
theorem exists_norm_fderiv_cutoff_le {n : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∀ x : ℝ^n,
      ‖fderiv ℝ (cutoff R) x‖ ≤ C / R := by
  have hb : ContDiff ℝ (⊤ : ℕ∞) (standardBump n) := (standardBump n).contDiff
  obtain ⟨C, hC⟩ := ((standardBump n).hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hb.continuous_fderiv (by simp))
  refine ⟨C, (norm_nonneg _).trans (hC 0), ?_⟩
  intro R hR x
  have hs := (hasFDerivAt_id (𝕜 := ℝ) x).const_smul R⁻¹
  change ‖fderiv ℝ ((standardBump n) ∘ (R⁻¹ • (id : ℝ^n → ℝ^n))) x‖ ≤ C / R
  rw [fderiv_comp x ((hb.differentiable (by simp)) _) hs.differentiableAt,
    hs.fderiv, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
  simpa only [div_eq_inv_mul, Pi.smul_apply, id_eq] using
    mul_le_mul_of_nonneg_left (hC (R⁻¹ • x)) (inv_nonneg.mpr hR.le)

end SobolevSpace.Approximation
