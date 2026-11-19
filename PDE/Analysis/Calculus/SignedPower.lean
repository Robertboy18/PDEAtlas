/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Odd real powers

The source `signedPower r x = |x|^(r-1) * x` agrees with `x^r` for nonnegative
arguments and positive exponents. Its oddness gives a formula in the positive and
negative parts, which avoids differentiating the absolute value at zero.

For every `r ≥ 1`, the mean value theorem bounds the difference by
`2r (|x| + |y|)^(r-1) |x-y|`. The bound includes the linear endpoint and gives
local Lipschitz continuity; its explicit constant need not be optimal.
-/

@[expose] public section

noncomputable section

open Set

namespace Real

/-- The odd real power, defined for every real exponent. The local Lipschitz
bounds below require the exponent to be at least one. -/
def signedPower (r x : ℝ) : ℝ := |x| ^ (r - 1) * x

/-- The odd power vanishes at zero for every exponent. -/
@[simp] theorem signedPower_zero (r : ℝ) : signedPower r 0 = 0 := by
  simp [signedPower]

/-- Changing the argument's sign changes the value's sign. -/
@[simp] theorem signedPower_neg (r x : ℝ) :
    signedPower r (-x) = -signedPower r x := by
  simp [signedPower]

/-- Exponent one gives the identity map. -/
@[simp] theorem signedPower_one (x : ℝ) : signedPower 1 x = x := by
  simp [signedPower]

/-- On the nonnegative half-line the odd power agrees with the real power. -/
theorem signedPower_of_nonneg {r x : ℝ} (hr : 0 < r) (hx : 0 ≤ x) :
    signedPower r x = x ^ r := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simp [hr.ne']
  · rw [signedPower, abs_of_pos hx, rpow_sub_one hx.ne']
    exact div_mul_cancel₀ _ hx.ne'

/-- Split the odd power into the powers of the positive and negative parts. -/
theorem signedPower_eq_posPart_sub_negPart {r : ℝ} (hr : 0 < r) (x : ℝ) :
    signedPower r x = x⁺ ^ r - x⁻ ^ r := by
  rcases le_total 0 x with hx | hx
  · rw [signedPower_of_nonneg hr hx]
    simp [posPart_def, negPart_def, max_eq_left hx, max_eq_right (neg_nonpos.mpr hx),
      hr.ne']
  · have hneg := signedPower_of_nonneg hr (neg_nonneg.mpr hx)
    rw [signedPower_neg] at hneg
    rw [show signedPower r x = -((-x) ^ r) by linarith]
    simp [posPart_def, negPart_def, max_eq_right hx,
      max_eq_left (neg_nonneg.mpr hx), hr.ne']

/-- The absolute value of the odd power is the power of the absolute value. -/
theorem norm_signedPower {r : ℝ} (hr : 0 < r) (x : ℝ) :
    ‖signedPower r x‖ = ‖x‖ ^ r := by
  rcases le_total 0 x with hx | hx
  · rw [signedPower_of_nonneg hr hx, Real.norm_eq_abs,
      abs_of_nonneg (rpow_nonneg hx _), Real.norm_eq_abs, abs_of_nonneg hx]
  · have hneg := signedPower_of_nonneg hr (neg_nonneg.mpr hx)
    rw [signedPower_neg] at hneg
    rw [show signedPower r x = -((-x) ^ r) by linarith]
    simp [Real.norm_eq_abs, abs_of_nonpos hx,
      abs_of_nonneg (rpow_nonneg (neg_nonneg.mpr hx) r)]

/-- Every positive exponent gives a continuous odd power, including at zero. -/
theorem continuous_signedPower {r : ℝ} (hr : 0 < r) :
    Continuous (signedPower r) := by
  have heq : signedPower r = fun x : ℝ ↦ x⁺ ^ r - x⁻ ^ r :=
    funext (signedPower_eq_posPart_sub_negPart hr)
  rw [heq]
  exact ((continuous_rpow_const hr.le).comp continuous_posPart).sub
    ((continuous_rpow_const hr.le).comp continuous_negPart)

/-- Reciprocal positive exponents undo the odd power on both half-lines. -/
@[simp] theorem signedPower_inv_signedPower {r : ℝ} (hr : 0 < r) (x : ℝ) :
    signedPower r⁻¹ (signedPower r x) = x := by
  have hnonneg (y : ℝ) (hy : 0 ≤ y) :
      signedPower r⁻¹ (signedPower r y) = y := by
    rw [signedPower_of_nonneg hr hy,
      signedPower_of_nonneg (inv_pos.mpr hr) (rpow_nonneg hy r),
      rpow_rpow_inv hy hr.ne']
  rcases le_total 0 x with hx | hx
  · exact hnonneg x hx
  · simpa only [signedPower_neg, neg_inj] using hnonneg (-x) (neg_nonneg.mpr hx)

/-- The power function is Lipschitz on a nonnegative interval, with its
derivative bound at the right endpoint. This includes exponent one and
intervals containing zero. -/
theorem norm_rpow_sub_le_on_Icc {r M a b : ℝ} (hr : 1 ≤ r)
    (ha : a ∈ Icc 0 M) (hb : b ∈ Icc 0 M) :
    ‖a ^ r - b ^ r‖ ≤ r * M ^ (r - 1) * ‖a - b‖ := by
  refine Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x _ ↦ (hasDerivAt_rpow_const (Or.inr hr)).differentiableAt)
    (fun x hx ↦ ?_) (convex_Icc 0 M) hb ha
  rw [deriv_rpow_const, norm_mul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ r),
    Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg hx.1 _)]
  exact mul_le_mul_of_nonneg_left
    (rpow_le_rpow hx.1 hx.2 (sub_nonneg.mpr hr)) (by linarith)

/-- A two-point growth estimate for the odd real power. It is valid for
all real `r ≥ 1`, including the linear endpoint. -/
theorem norm_signedPower_sub_le {r : ℝ} (hr : 1 ≤ r) (x y : ℝ) :
    ‖signedPower r x - signedPower r y‖ ≤
      (2 * r) * (‖x‖ + ‖y‖) ^ (r - 1) * ‖x - y‖ := by
  let M := ‖x‖ + ‖y‖
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hpos (z : ℝ) : z⁺ ≤ ‖z‖ := by
    simpa [posPart_def, Real.norm_eq_abs] using
      (max_le (le_abs_self z) (abs_nonneg z))
  have hneg (z : ℝ) : z⁻ ≤ ‖z‖ := by
    simpa [negPart_def, Real.norm_eq_abs] using
      (max_le (neg_le_abs z) (abs_nonneg z))
  have hxp : x⁺ ∈ Icc 0 M :=
    ⟨posPart_nonneg x, (hpos x).trans (le_add_of_nonneg_right (norm_nonneg y))⟩
  have hyp : y⁺ ∈ Icc 0 M :=
    ⟨posPart_nonneg y, (hpos y).trans (le_add_of_nonneg_left (norm_nonneg x))⟩
  have hxn : x⁻ ∈ Icc 0 M :=
    ⟨negPart_nonneg x, (hneg x).trans (le_add_of_nonneg_right (norm_nonneg y))⟩
  have hyn : y⁻ ∈ Icc 0 M :=
    ⟨negPart_nonneg y, (hneg y).trans (le_add_of_nonneg_left (norm_nonneg x))⟩
  have hp : ‖x⁺ - y⁺‖ ≤ ‖x - y‖ := by
    simpa [dist_eq_norm] using lipschitzWith_posPart.dist_le_mul x y
  have hn : ‖x⁻ - y⁻‖ ≤ ‖x - y‖ := by
    simpa [dist_eq_norm] using lipschitzWith_negPart.dist_le_mul x y
  have hC : 0 ≤ r * M ^ (r - 1) :=
    mul_nonneg hr0.le (rpow_nonneg (add_nonneg (norm_nonneg x) (norm_nonneg y)) _)
  rw [signedPower_eq_posPart_sub_negPart hr0 x,
    signedPower_eq_posPart_sub_negPart hr0 y]
  calc
    ‖(x⁺ ^ r - x⁻ ^ r) - (y⁺ ^ r - y⁻ ^ r)‖ =
        ‖(x⁺ ^ r - y⁺ ^ r) - (x⁻ ^ r - y⁻ ^ r)‖ := by congr 1; ring
    _ ≤ ‖x⁺ ^ r - y⁺ ^ r‖ + ‖x⁻ ^ r - y⁻ ^ r‖ := norm_sub_le _ _
    _ ≤ r * M ^ (r - 1) * ‖x⁺ - y⁺‖ +
        r * M ^ (r - 1) * ‖x⁻ - y⁻‖ :=
      add_le_add (norm_rpow_sub_le_on_Icc hr hxp hyp)
        (norm_rpow_sub_le_on_Icc hr hxn hyn)
    _ ≤ r * M ^ (r - 1) * ‖x - y‖ +
        r * M ^ (r - 1) * ‖x - y‖ :=
      add_le_add (mul_le_mul_of_nonneg_left hp hC) (mul_le_mul_of_nonneg_left hn hC)
    _ = (2 * r) * (‖x‖ + ‖y‖) ^ (r - 1) * ‖x - y‖ := by dsimp [M]; ring

end Real
