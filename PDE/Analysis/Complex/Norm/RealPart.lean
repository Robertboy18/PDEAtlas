/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Complex.Norm

/-!
# Real-part comparison from shifted norms

A lower bound for every nonnegative real shift of a complex number
determines the same lower bound for its real part. Squaring the estimates
leaves an affine inequality in the shift parameter.
-/

@[expose] public section

namespace Complex

/-- Comparing all nonnegative real shifts of a complex number bounds its
real part. This is useful when positive resolvents first give modulus bounds. -/
theorem le_re_of_forall_add_le_norm_add {r : ℝ} (hr : 0 ≤ r) (z : ℂ)
    (h : ∀ s : ℝ, 0 ≤ s → r + s ≤ ‖z + (s : ℂ)‖) : r ≤ z.re := by
  by_contra hle
  have hd : 0 < r - z.re := sub_pos.mpr (lt_of_not_ge hle)
  let s := (‖z‖ ^ 2 + 1) / (r - z.re)
  have hs : 0 ≤ s := div_nonneg (by positivity) hd.le
  have hmul : s * (r - z.re) = ‖z‖ ^ 2 + 1 :=
    div_mul_cancel₀ _ hd.ne'
  have hsq : (r + s) ^ 2 ≤ ‖z + (s : ℂ)‖ ^ 2 :=
    pow_le_pow_left₀ (add_nonneg hr hs) (h s hs) 2
  have hz := Complex.sq_norm z
  have hzs := Complex.sq_norm (z + (s : ℂ))
  simp only [normSq_apply, add_re, ofReal_re, add_im, ofReal_im, add_zero] at hz hzs
  nlinarith [sq_nonneg r, sq_nonneg ‖z‖]

end Complex
