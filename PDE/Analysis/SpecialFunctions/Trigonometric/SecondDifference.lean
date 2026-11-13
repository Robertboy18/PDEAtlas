/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Second differences of cosine and sine waves

The second difference `f (t + h) - 2 f t + f (t - h)` of `f = cos (w ·)` or `sin (w ·)` is
`2 (cos (w h) - 1) f t`, so it differs from `h ^ 2 f'' t = -(w h) ^ 2 f t` by at most
`(5 / 48) (w h) ^ 4` when `|w h| ≤ 1` (`abs_cos_secondDifference_sub_le`,
`abs_sin_secondDifference_sub_le`). A second difference with step `h` therefore bounds the
second derivative of a trigonometric sum up to a fourth-moment term.
-/

@[expose] public section

namespace PDE.Analysis

/-- The second derivative of `s ↦ cos (w s)`. -/
theorem iteratedDeriv_two_cos_mul (w t : ℝ) :
    iteratedDeriv 2 (fun s ↦ Real.cos (w * s)) t = -(w ^ 2 * Real.cos (w * t)) := by
  rw [congrFun (iteratedDeriv_comp_const_mul (Real.contDiff_cos (n := 2)) w) t]
  simp [iteratedDeriv_succ]

/-- The second derivative of `s ↦ sin (w s)`. -/
theorem iteratedDeriv_two_sin_mul (w t : ℝ) :
    iteratedDeriv 2 (fun s ↦ Real.sin (w * s)) t = -(w ^ 2 * Real.sin (w * t)) := by
  rw [congrFun (iteratedDeriv_comp_const_mul (Real.contDiff_sin (n := 2)) w) t]
  simp [iteratedDeriv_succ]

theorem abs_two_mul_cos_sub_le {x : ℝ} (hx : |x| ≤ 1) :
    |2 * (Real.cos x - 1) + x ^ 2| ≤ 5 / 48 * x ^ 4 := by
  have h := Real.cos_bound hx
  have e : 2 * (Real.cos x - 1) + x ^ 2 = 2 * (Real.cos x - (1 - x ^ 2 / 2)) := by ring
  have h4 : |x| ^ 4 = x ^ 4 := by
    rw [pow_abs]
    exact abs_of_nonneg (by positivity)
  rw [h4] at h
  rw [e, abs_mul, abs_two]
  linarith

/-- **Second difference of a cosine wave.** -/
theorem abs_cos_secondDifference_sub_le {w h : ℝ} (hwh : |w * h| ≤ 1) (t : ℝ) :
    |Real.cos (w * (t + h)) - 2 * Real.cos (w * t) + Real.cos (w * (t - h)) -
        h ^ 2 * iteratedDeriv 2 (fun s ↦ Real.cos (w * s)) t| ≤ 5 / 48 * (w * h) ^ 4 := by
  rw [iteratedDeriv_two_cos_mul]
  have e : Real.cos (w * (t + h)) - 2 * Real.cos (w * t) + Real.cos (w * (t - h)) -
      h ^ 2 * -(w ^ 2 * Real.cos (w * t)) =
      Real.cos (w * t) * (2 * (Real.cos (w * h) - 1) + (w * h) ^ 2) := by
    rw [show w * (t + h) = w * t + w * h by ring, show w * (t - h) = w * t - w * h by ring,
      Real.cos_add, Real.cos_sub]
    ring
  rw [e, abs_mul]
  calc _ ≤ 1 * (5 / 48 * (w * h) ^ 4) :=
        mul_le_mul (Real.abs_cos_le_one _) (abs_two_mul_cos_sub_le hwh) (abs_nonneg _)
          (by norm_num)
    _ = _ := one_mul _

/-- **Second difference of a sine wave.** -/
theorem abs_sin_secondDifference_sub_le {w h : ℝ} (hwh : |w * h| ≤ 1) (t : ℝ) :
    |Real.sin (w * (t + h)) - 2 * Real.sin (w * t) + Real.sin (w * (t - h)) -
        h ^ 2 * iteratedDeriv 2 (fun s ↦ Real.sin (w * s)) t| ≤ 5 / 48 * (w * h) ^ 4 := by
  rw [iteratedDeriv_two_sin_mul]
  have e : Real.sin (w * (t + h)) - 2 * Real.sin (w * t) + Real.sin (w * (t - h)) -
      h ^ 2 * -(w ^ 2 * Real.sin (w * t)) =
      Real.sin (w * t) * (2 * (Real.cos (w * h) - 1) + (w * h) ^ 2) := by
    rw [show w * (t + h) = w * t + w * h by ring, show w * (t - h) = w * t - w * h by ring,
      Real.sin_add, Real.sin_sub]
    ring
  rw [e, abs_mul]
  calc _ ≤ 1 * (5 / 48 * (w * h) ^ 4) :=
        mul_le_mul (Real.abs_sin_le_one _) (abs_two_mul_cos_sub_le hwh) (abs_nonneg _)
          (by norm_num)
    _ = _ := one_mul _

end PDE.Analysis
