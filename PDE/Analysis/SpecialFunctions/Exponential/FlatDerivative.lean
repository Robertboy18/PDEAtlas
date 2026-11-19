/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import CAS.ExactTactic

/-!
# The derivative of the flat exponential

`expNegInvGlue` is Mathlib's `exp (-1 / x)` for `x > 0`, glued to `0` for `x ≤ 0`. We prove, at
every real `x`:

* `expNegInvGlue.deriv_eq`: the derivative is `x⁻² expNegInvGlue x`;
* `expNegInvGlue.deriv_nonneg`, `expNegInvGlue.deriv_le`: `0 ≤ expNegInvGlue' x ≤ 4 e⁻²`.

The first is Mathlib's `expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul` for the constant
polynomial `1`; `expNegInvGlue.hasDerivAt_rpow_mul` is the same formula for the products with a
real power. For the bound, with `w = 1 / x > 0`, the inequality `w / 2 ≤ e^(w/2 - 1)` gives
`w² e^(-w) ≤ 4 e⁻²`. On paper the bound is attained, at `x = 1/2`; this file does not prove that.

These bounds make the gradient of the smooth bump `x ↦ expNegInvGlue (1 - |x|² / R²)` on `ℝ^n`
explicit, through the chain rule `PDE.Analysis.sum_sq_partialDeriv_profile`.
-/

@[expose] public section

namespace expNegInvGlue

/-- The derivative of `expNegInvGlue` is `x⁻² expNegInvGlue x`, at every `x`. -/
theorem deriv_eq (x : ℝ) : deriv expNegInvGlue x = x⁻¹ ^ 2 * expNegInvGlue x := by
  simpa using (hasDerivAt_polynomial_eval_inv_mul 1 x).deriv

/-- The derivative of `expNegInvGlue` is nonnegative. -/
theorem deriv_nonneg (x : ℝ) : 0 ≤ deriv expNegInvGlue x := by
  rw [deriv_eq]
  exact mul_nonneg (sq_nonneg _) (nonneg x)

/-- The derivative of `expNegInvGlue` is at most `4 e⁻²`, at every `x`. -/
theorem deriv_le (x : ℝ) : deriv expNegInvGlue x ≤ 4 * Real.exp (-2) := by
  rw [deriv_eq]
  rcases le_or_gt x 0 with hx | hx
  · rw [zero_of_nonpos hx, mul_zero]
    positivity
  · have hE : expNegInvGlue x = Real.exp (-2) / Real.exp (x⁻¹ / 2 - 1) ^ 2 := by
      simp only [expNegInvGlue, hx.not_ge, ↓reduceIte]
      rw [← Real.exp_nat_mul, ← Real.exp_sub]
      congr 1
      cas
    -- With `w = 1 / x`, `E = e^(w/2 - 1) ≥ w / 2` and `c = e⁻²`: `w² c ≤ 4 c E²`.
    have key (w E c : ℝ) (hw : 0 < w) (hwE : w / 2 ≤ E) (hc : 0 ≤ c) :
        w ^ 2 * c ≤ 4 * c * E ^ 2 := by
      have hE : 0 ≤ E := by cas using [hw, hwE]
      have h2 : w ^ 2 ≤ 4 * E ^ 2 := by
        cas using [mul_le_mul hwE hwE (by cas using [hw] : 0 ≤ w / 2) hE]
      cas using [mul_le_mul_of_nonneg_right h2 hc]
    rw [hE, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    exact key _ _ _ (inv_pos.mpr hx) (by cas using [Real.add_one_le_exp (x⁻¹ / 2 - 1)])
      (Real.exp_pos _).le

end expNegInvGlue
