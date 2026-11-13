/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SmoothTransitionBounds

/-!
# Physical-coordinate bounds for scaled exponential transitions

`S_R x = S (x / R)` is the exponential transition `S = Real.smoothTransition` with radius `R`.
For `R > 0` it is increasing, vanishes on `x ≤ 0` and equals one on `x ≥ R`. The derivative
bounds retain the chain-rule factors from the radius, and the complementary factor `1 - S_R`
lies in `[0, 1]`.

## Main definitions

* `scaledSmoothTransition`: the transition `S_R x = S (x / R)` with radius `R`.

## Main results

* `contDiff_scaledSmoothTransition`: `S_R` is smooth of every finite order, also for `R = 0`.
* `scaledSmoothTransition_of_nonpos`: for `R > 0`, `S_R` vanishes on `x ≤ 0`.
* `scaledSmoothTransition_of_le`: for `R > 0`, `S_R` equals one on `x ≥ R`.
* `deriv_scaledSmoothTransition`: `S_R' x = S'(x / R) / R`.
* `abs_scaledSmoothTransition_le_factorial_mul_pow`: `|S_R x| ≤ 9 n! (x/R)ⁿ` for
  `0 ≤ x/R ≤ 1/2`.
* `abs_deriv_scaledSmoothTransition_le_factorial_mul_pow`:
  `|S_R' x| ≤ 18 (n + 2)! (x/R)ⁿ / |R|` for `0 ≤ x/R ≤ 1/2`.
* `abs_deriv_deriv_scaledSmoothTransition_le_factorial_mul_pow`: the same flatness bound for
  `S_R''`, with two inverse-radius factors.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open scoped ContDiff

/-- The exponential transition with radius `R`. -/
def scaledSmoothTransition (R x : ℝ) : ℝ :=
  Real.smoothTransition (x / R)

/-- Scaling preserves every finite order of smoothness, including radius zero. -/
theorem contDiff_scaledSmoothTransition (R : ℝ) {n : ℕ∞} :
    ContDiff ℝ (n : ℕ∞ω) (scaledSmoothTransition R) :=
  Real.smoothTransition.contDiff.comp (contDiff_id.div_const R)

/-- The scaled transition is nonnegative. -/
theorem scaledSmoothTransition_nonneg (R x : ℝ) : 0 ≤ scaledSmoothTransition R x :=
  Real.smoothTransition.nonneg _

/-- The scaled transition is at most one. -/
theorem scaledSmoothTransition_le_one (R x : ℝ) : scaledSmoothTransition R x ≤ 1 :=
  Real.smoothTransition.le_one _

/-- For a positive radius `R`, the scaled transition vanishes on `x ≤ 0`. -/
theorem scaledSmoothTransition_of_nonpos {R x : ℝ} (hR : 0 < R) (hx : x ≤ 0) :
    scaledSmoothTransition R x = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hx hR.le)

/-- For a positive radius `R`, the scaled transition equals one on `R ≤ x`. -/
theorem scaledSmoothTransition_of_le {R x : ℝ} (hR : 0 < R) (hx : R ≤ x) :
    scaledSmoothTransition R x = 1 :=
  Real.smoothTransition.one_of_one_le ((le_div_iff₀ hR).2 (by simpa using hx))

/-- For a positive radius the scaled transition is increasing, so its derivative is
nonnegative. -/
theorem deriv_scaledSmoothTransition_nonneg {R : ℝ} (hR : 0 < R) (x : ℝ) :
    0 ≤ deriv (scaledSmoothTransition R) x :=
  Monotone.deriv_nonneg fun _ _ h ↦
    Real.smoothTransition.monotone (div_le_div_of_nonneg_right h hR.le)

/-- First physical derivative, with its inverse-radius factor. -/
theorem deriv_scaledSmoothTransition (R x : ℝ) :
    deriv (scaledSmoothTransition R) x = deriv Real.smoothTransition (x / R) / R := by
  have hd : Differentiable ℝ Real.smoothTransition :=
    (show ContDiff ℝ 1 Real.smoothTransition from
      Real.smoothTransition.contDiff).differentiable (by norm_num)
  change deriv (fun y : ℝ ↦ Real.smoothTransition (y / R)) x = _
  simpa [Function.comp_def, div_eq_mul_inv] using
    ((hd (x / R)).hasDerivAt.comp x ((hasDerivAt_id x).div_const R)).deriv

/-- Second physical derivative, with the square of the inverse radius. -/
theorem deriv_deriv_scaledSmoothTransition (R x : ℝ) :
    deriv (deriv (scaledSmoothTransition R)) x =
      deriv (deriv Real.smoothTransition) (x / R) / R ^ 2 := by
  have hd : Differentiable ℝ (deriv Real.smoothTransition) :=
    (show ContDiff ℝ 1 (deriv Real.smoothTransition) from
      (show ContDiff ℝ 2 Real.smoothTransition from
        Real.smoothTransition.contDiff).deriv').differentiable (by norm_num)
  have heq : deriv (scaledSmoothTransition R) =
      fun y ↦ deriv Real.smoothTransition (y / R) / R :=
    funext (deriv_scaledSmoothTransition R)
  rw [heq]
  simpa [Function.comp_def, div_eq_mul_inv, pow_two, mul_assoc] using
    (((hd (x / R)).hasDerivAt.comp x
      ((hasDerivAt_id x).div_const R)).div_const R).deriv

/-- The complementary factor `1 - S_R` takes values in `[0, 1]` for every radius. -/
theorem abs_one_sub_scaledSmoothTransition_le_one (R x : ℝ) :
    |1 - scaledSmoothTransition R x| ≤ 1 := by
  have hlo := scaledSmoothTransition_nonneg R x
  have hhi := scaledSmoothTransition_le_one R x
  rw [abs_of_nonneg (sub_nonneg.mpr hhi)]
  linarith

/-- The value retains the quantitative flatness bound after scaling. -/
theorem abs_scaledSmoothTransition_le_factorial_mul_pow (n : ℕ) (R x : ℝ)
    (ht : 0 ≤ x / R) (ht₂ : x / R ≤ 1 / 2) :
    |scaledSmoothTransition R x| ≤ 9 * (n.factorial : ℝ) * (x / R) ^ n := by
  rw [scaledSmoothTransition, abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact smoothTransition_le_factorial_mul_pow n ht ht₂

/-- The first derivative bound includes its physical inverse-radius factor. -/
theorem abs_deriv_scaledSmoothTransition_le_factorial_mul_pow (n : ℕ) (R x : ℝ)
    (ht : 0 ≤ x / R) (ht₂ : x / R ≤ 1 / 2) :
    |deriv (scaledSmoothTransition R) x| ≤
      18 * ((n + 2).factorial : ℝ) * (x / R) ^ n / |R| := by
  rw [deriv_scaledSmoothTransition, abs_div]
  exact div_le_div_of_nonneg_right
    (abs_deriv_smoothTransition_le_factorial_mul_pow n ht ht₂) (abs_nonneg R)

/-- The second derivative bound includes two physical inverse-radius factors. -/
theorem abs_deriv_deriv_scaledSmoothTransition_le_factorial_mul_pow (n : ℕ) (R x : ℝ)
    (ht : 0 ≤ x / R) (ht₂ : x / R ≤ 1 / 2) :
    |deriv (deriv (scaledSmoothTransition R)) x| ≤
      54 * ((n + 4).factorial : ℝ) * (x / R) ^ n / |R| ^ 2 := by
  rw [deriv_deriv_scaledSmoothTransition, abs_div, abs_pow]
  exact div_le_div_of_nonneg_right
    (abs_deriv_deriv_smoothTransition_le_factorial_mul_pow n ht ht₂) (sq_nonneg |R|)

end PDE.Analysis
