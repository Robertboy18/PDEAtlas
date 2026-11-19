/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.MeanValue

/-!
# A Lipschitz coordinate quotient from linear derivative growth

A differentiable function vanishing at zero has a Lipschitz quotient by the coordinate
when its derivative is bounded by a constant times the distance to zero. The quotient
uses the total value zero at the origin; no second derivative is assumed.
-/

@[expose] public noncomputable section

open Set
open scoped NNReal

namespace PDE.Analysis

/-- A linear bound on the derivative makes the coordinate quotient Lipschitz,
including its total value zero at the origin. No second derivative is needed. -/
theorem lipschitzWith_div_id_of_deriv_le_mul_abs
    {q : ℝ → ℝ} {K : ℝ≥0} (hq : Differentiable ℝ q) (hq0 : q 0 = 0)
    (hb : ∀ x, ‖deriv q x‖ ≤ K * |x|) :
    LipschitzWith (2 * K) (fun x ↦ q x / x) := by
  have hd {R x y : ℝ} (hx : |x| ≤ R) (hy : |y| ≤ R) :
      ‖q x - q y‖ ≤ (K * R) * |x - y| := by
    exact (convex_Icc (-R) R).norm_image_sub_le_of_norm_deriv_le
      (fun z _ ↦ hq z)
      (fun z hz ↦ (hb z).trans
        (mul_le_mul_of_nonneg_left (abs_le.mpr hz) K.coe_nonneg))
      (abs_le.mp hy) (abs_le.mp hx)
  have hval (x : ℝ) : ‖q x‖ ≤ K * |x| ^ 2 := by
    simpa only [hq0, sub_zero, sq, mul_assoc] using
      hd (x := x) (y := 0) le_rfl (by simp)
  have hquot (x : ℝ) : ‖q x / x‖ ≤ K * |x| := by
    by_cases hx : x = 0
    · simp [hx]
    · rw [norm_div, Real.norm_eq_abs x]
      exact (div_le_iff₀ (abs_pos.mpr hx)).mpr (by simpa [sq, mul_assoc] using hval x)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖q x / x - q y / y‖ ≤ (2 * (K : ℝ)) * ‖x - y‖
  wlog hxy : |x| ≤ |y| generalizing x y
  · simpa only [norm_sub_rev] using this y x (le_of_not_ge hxy)
  by_cases hy : y = 0
  · have hx : x = 0 := abs_eq_zero.mp
      (le_antisymm (by simpa only [hy, abs_zero] using hxy) (abs_nonneg x))
    simp [hx, hy]
  by_cases hx : x = 0
  · simpa only [hx, div_zero, zero_sub, norm_neg, Real.norm_eq_abs] using
      (hquot y).trans (by nlinarith [K.coe_nonneg, abs_nonneg y])
  have he : q x / x - q y / y =
      (q x - q y) / y + (q x / x) * ((y - x) / y) := by
    field_simp
    ring
  rw [he]
  have hfirst : ‖(q x - q y) / y‖ ≤ K * |x - y| := by
    rw [norm_div, Real.norm_eq_abs y]
    apply (div_le_iff₀ (abs_pos.mpr hy)).mpr
    simpa only [mul_assoc, mul_comm |y| |x - y|] using hd hxy le_rfl
  have hsecond : ‖(q x / x) * ((y - x) / y)‖ ≤ K * |x - y| := by
    rw [norm_mul, norm_div (y - x) y, Real.norm_eq_abs (y - x),
      Real.norm_eq_abs y, abs_sub_comm y x]
    calc
      _ ≤ (K * |y|) * (|x - y| / |y|) :=
        mul_le_mul_of_nonneg_right
          ((hquot x).trans (mul_le_mul_of_nonneg_left hxy K.coe_nonneg)) (by positivity)
      _ = _ := by field_simp
  calc
    _ ≤ ‖(q x - q y) / y‖ + ‖(q x / x) * ((y - x) / y)‖ := norm_add_le _ _
    _ ≤ K * |x - y| + K * |x - y| := add_le_add hfirst hsecond
    _ = _ := by rw [Real.norm_eq_abs]; ring

end PDE.Analysis
