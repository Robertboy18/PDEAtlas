/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Norm bound for the normed-algebra exponential

The exponential series gives `‖exp x‖ ≤ exp ‖x‖` when the algebra unit has norm
at most one. The weak inequality on the unit includes the zero algebra.
-/

@[expose] public noncomputable section

namespace NormedSpace

section Real

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- The standard exponential norm estimate, including algebras with zero unit. The algebra need
not be complete: if the exponential series does not converge, `exp x` is `0`. -/
theorem norm_exp_le_exp_norm_of_norm_one_le (h₁ : ‖(1 : A)‖ ≤ 1) (x : A) :
    ‖exp x‖ ≤ Real.exp ‖x‖ := by
  rw [Real.exp_eq_exp_ℝ, congrFun (exp_eq_tsum ℝ) x]
  apply tsum_of_norm_bounded (exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖)
  intro n
  rw [norm_smul, Real.norm_of_nonneg (by positivity), smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  cases n with
  | zero => simpa only [pow_zero] using h₁
  | succ n => exact norm_pow_le' x (Nat.succ_pos n)

end Real

section Complex

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- An affine complex line in a normed algebra gives an exponential
with explicit exponential growth. The two algebra elements need not commute. -/
theorem norm_exp_add_smul_le (h₁ : ‖(1 : A)‖ ≤ 1) (R S : A) (z : ℂ) :
    ‖exp (R + z • S)‖ ≤
      Real.exp ‖R‖ * Real.exp (‖S‖ * (|z.re| + |z.im|)) := by
  let : NormedAlgebra ℝ A := NormedAlgebra.restrictScalars ℝ ℂ A
  apply (norm_exp_le_exp_norm_of_norm_one_le h₁ _).trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  calc
    ‖R + z • S‖ ≤ ‖R‖ + ‖z • S‖ := norm_add_le _ _
    _ = ‖R‖ + ‖S‖ * ‖z‖ := by rw [norm_smul, mul_comm ‖z‖]
    _ ≤ _ := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (Complex.norm_le_abs_re_add_abs_im z) (norm_nonneg S))

end Complex

end NormedSpace
