/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Exit of a ray from the unit ball

For an interior point `c` and another point `x`, the positive quadratic root gives the
intersection of the ray from `c` through `x` with the unit sphere. Both the discriminant
and the denominator are strictly positive when `x ≠ c`. Consequently this construction
preserves classical smoothness, including at points where `x` is on the sphere.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ContDiff

namespace PDE.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The positive root of the ray's unit-sphere equation. -/
def ballRayExitTime (c x : H) : ℝ :=
  (-⟪c, x - c⟫_ℝ +
    √(⟪c, x - c⟫_ℝ ^ 2 + ‖x - c‖ ^ 2 * (1 - ‖c‖ ^ 2))) / ‖x - c‖ ^ 2

/-- The intersection of the ray from `c` through `x` with the unit sphere. -/
def ballRayExit (c x : H) : H :=
  c + ballRayExitTime c x • (x - c)

/-- The ray discriminant is positive for an interior starting point and nonzero direction. -/
theorem ballRayExit_discriminant_pos {c x : H} (hc : ‖c‖ < 1) (hne : x ≠ c) :
    0 < ⟪c, x - c⟫_ℝ ^ 2 + ‖x - c‖ ^ 2 * (1 - ‖c‖ ^ 2) := by
  have ha : 0 < ‖x - c‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  have hb : 0 < 1 - ‖c‖ ^ 2 := by nlinarith [norm_nonneg c]
  exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos ha hb)

/-- The ray meets the sphere in the positive direction. -/
theorem ballRayExitTime_pos {c x : H} (hc : ‖c‖ < 1) (hne : x ≠ c) :
    0 < ballRayExitTime c x := by
  have ha : 0 < ‖x - c‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  have hb : 0 < 1 - ‖c‖ ^ 2 := by nlinarith [norm_nonneg c]
  have hlt := Real.sqrt_lt_sqrt (sq_nonneg ⟪c, x - c⟫_ℝ)
    (lt_add_of_pos_right (⟪c, x - c⟫_ℝ ^ 2) (mul_pos ha hb))
  rw [Real.sqrt_sq_eq_abs] at hlt
  exact div_pos (by linarith [le_abs_self ⟪c, x - c⟫_ℝ]) ha

/-- The ray exit has norm one. -/
theorem norm_ballRayExit {c x : H} (hc : ‖c‖ < 1) (hne : x ≠ c) :
    ‖ballRayExit c x‖ = 1 := by
  let a := ‖x - c‖ ^ 2
  let b := ⟪c, x - c⟫_ℝ
  let d := 1 - ‖c‖ ^ 2
  let t := ballRayExitTime c x
  have ha : a ≠ 0 := ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)))
  have ht : a * t + b = √(b ^ 2 + a * d) := by
    dsimp [t, ballRayExitTime]
    rw [mul_div_cancel₀ _ ha]
    ring
  have hs : (a * t + b) ^ 2 = b ^ 2 + a * d := by
    rw [ht, Real.sq_sqrt (ballRayExit_discriminant_pos hc hne).le]
  have hroot : a * t ^ 2 + 2 * b * t = d := by
    have hz : a * (a * t ^ 2 + 2 * b * t - d) = 0 := by nlinarith only [hs]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left ha)
  have hnorm : ‖ballRayExit c x‖ ^ 2 = 1 := by
    rw [ballRayExit, norm_add_sq_real, inner_smul_right, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    change ‖c‖ ^ 2 + 2 * (t * b) + t ^ 2 * a = 1
    dsimp [d] at hroot
    nlinarith only [hroot]
  nlinarith [norm_nonneg (ballRayExit c x)]

/-- Starting with a point already on the sphere leaves it fixed. -/
theorem ballRayExit_eq_self_of_norm_eq_one {c x : H} (hc : ‖c‖ < 1)
    (hx : ‖x‖ = 1) : ballRayExit c x = x := by
  have hne : x ≠ c := by rintro rfl; linarith
  let a := ‖x - c‖ ^ 2
  let b := ⟪c, x - c⟫_ℝ
  have ha : a ≠ 0 := ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)))
  have hab : a + 2 * b = 1 - ‖c‖ ^ 2 := by
    dsimp [a, b]
    rw [norm_sub_sq_real, inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_comm x c, hx]
    ring
  have hpositive : 0 < a + b := by
    have hi := real_inner_le_norm c x
    rw [hx, mul_one] at hi
    have heq : a + b = 1 - ⟪c, x⟫_ℝ := by
      dsimp [a, b]
      rw [norm_sub_sq_real, inner_sub_right, real_inner_self_eq_norm_sq,
        real_inner_comm x c, hx]
      ring
    rw [heq]
    linarith
  have hd : b ^ 2 + a * (1 - ‖c‖ ^ 2) = (a + b) ^ 2 := by
    rw [← hab]
    ring
  have ht : ballRayExitTime c x = 1 := by
    change (-b + √(b ^ 2 + a * (1 - ‖c‖ ^ 2))) / a = 1
    rw [hd, Real.sqrt_sq hpositive.le]
    have heq : -b + (a + b) = a := by ring
    rw [heq, div_self ha]
  simp [ballRayExit, ht]

/-- Smoothly varying interior starting points and nonzero directions give smooth ray exits. -/
theorem _root_.ContDiff.ballRayExit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℕ∞ω} {u v : E → H} (hu : ContDiff ℝ r u) (hv : ContDiff ℝ r v)
    (hunit : ∀ x, ‖u x‖ < 1) (hne : ∀ x, v x ≠ u x) :
    ContDiff ℝ r (fun x ↦ ballRayExit (u x) (v x)) := by
  have ha := (hv.sub hu).norm_sq ℝ
  have hb := hu.inner ℝ (hv.sub hu)
  have hd := (hb.pow 2).add (ha.mul ((contDiff_const (c := (1 : ℝ))).sub (hu.norm_sq ℝ)))
  have hs := hd.sqrt (fun x ↦ (ballRayExit_discriminant_pos (hunit x) (hne x)).ne')
  have ht := (hb.neg.add hs).div ha
    (fun x ↦ ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hne x)))))
  exact hu.add (ht.smul (hv.sub hu))

end PDE.Analysis
