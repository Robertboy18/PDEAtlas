/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Affine.Convex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Hölder bounds from homogeneous value and gradient bounds

A function with `‖H y‖ ≤ A ‖y‖^α` and `‖DH(y)‖ ≤ K ‖y‖^(α - 1)` on a convex set is `α`-Hölder
there with constant `2 · 3^α A + K`, for `0 < α ≤ 1`. The gradient may blow up at the origin:
pairs of points close to the origin compared with their distance are compared through the value
bound, and all other pairs through the mean value inequality on the segment between them, which
stays away from the origin. This is the form in which singularly weighted functions vanishing to
the right order are Hölder continuous, as in Chen and Hou, Part I, Remark 4.8
(`W₁ (|x|^{-5/2} + 1) ∈ C^{1/2}`).

## Main results

* `HolderSpace.norm_sub_le_of_rpow_bounds`: the Hölder estimate.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Remark 4.8.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

open Set

namespace HolderSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Hölder estimate from homogeneous bounds.** On a convex set `S`, if `H` is differentiable at
every point of `S`, `‖H y‖ ≤ A ‖y‖^α` and `‖DH(y)‖ ≤ K ‖y‖^(α - 1)` for `y ≠ 0`, with `0 < α ≤ 1`,
then `‖H x - H z‖ ≤ (2 · 3^α A + K) ‖x - z‖^α` for `x, z ∈ S`. -/
theorem norm_sub_le_of_rpow_bounds {H : E → F} {S : Set E} (hS : Convex ℝ S) {α A K : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hd : ∀ y ∈ S, DifferentiableAt ℝ H y) (hH : ∀ y ∈ S, ‖H y‖ ≤ A * ‖y‖ ^ α)
    (hH' : ∀ y ∈ S, y ≠ 0 → ‖fderiv ℝ H y‖ ≤ K * ‖y‖ ^ (α - 1)) {x z : E} (hx : x ∈ S)
    (hz : z ∈ S) : ‖H x - H z‖ ≤ (2 * 3 ^ α * A + K) * ‖x - z‖ ^ α := by
  set h := ‖x - z‖ with hh
  have hh0 : 0 ≤ h := norm_nonneg _
  have h3 : 0 ≤ (3 : ℝ) ^ α := Real.rpow_nonneg (by norm_num) α
  have hhα : 0 ≤ h ^ α := Real.rpow_nonneg hh0 α
  rcases hh0.eq_or_lt with h0 | hpos
  · have hxz0 : x = z := sub_eq_zero.1 (norm_eq_zero.1 h0.symm)
    rw [← h0, Real.zero_rpow hα.ne', mul_zero, hxz0, sub_self, norm_zero]
  -- the constants are nonnegative: one of the two distinct points is nonzero
  obtain ⟨y, hyS, hy0⟩ : ∃ y ∈ S, y ≠ 0 := by
    by_cases hx0 : x = 0
    · refine ⟨z, hz, fun hz0 ↦ ?_⟩
      simp [hh, hx0, hz0] at hpos
    · exact ⟨x, hx, hx0⟩
  have hA : 0 ≤ A := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hH y hyS))
    (Real.rpow_pos_of_pos (norm_pos_iff.mpr hy0) α)
  have hK : 0 ≤ K := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hH' y hyS hy0))
    (Real.rpow_pos_of_pos (norm_pos_iff.mpr hy0) (α - 1))
  have hxz : ‖x‖ ≤ ‖z‖ + h := by
    have := norm_sub_norm_le x z; linarith
  have hzx : ‖z‖ ≤ ‖x‖ + h := by
    have := norm_sub_norm_le z x; rw [norm_sub_rev] at this; linarith
  by_cases hm : min ‖x‖ ‖z‖ ≤ 2 * h
  · -- both points lie within `3 h` of the origin
    have hx3 : ‖x‖ ≤ 3 * h := by
      rcases min_le_iff.1 hm with hm | hm <;> linarith
    have hz3 : ‖z‖ ≤ 3 * h := by
      rcases min_le_iff.1 hm with hm | hm <;> linarith
    have hpow : ∀ y : E, ‖y‖ ≤ 3 * h → ‖y‖ ^ α ≤ 3 ^ α * h ^ α := fun y hy ↦ by
      rw [← Real.mul_rpow (by norm_num) hh0]
      exact Real.rpow_le_rpow (norm_nonneg _) hy hα.le
    calc ‖H x - H z‖ ≤ ‖H x‖ + ‖H z‖ := norm_sub_le _ _
      _ ≤ A * ‖x‖ ^ α + A * ‖z‖ ^ α := add_le_add (hH x hx) (hH z hz)
      _ ≤ A * (3 ^ α * h ^ α) + A * (3 ^ α * h ^ α) := by
        gcongr
        · exact hpow x hx3
        · exact hpow z hz3
      _ = 2 * 3 ^ α * A * h ^ α := by ring
      _ ≤ (2 * 3 ^ α * A + K) * h ^ α := by nlinarith
  · -- the segment between the points stays at distance at least `h` from the origin
    push Not at hm
    have hfar : ∀ w ∈ segment ℝ x z, h ≤ ‖w‖ := by
      intro w hw
      have hsum := dist_add_dist_of_mem_segment hw
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at hsum
      have h1 := norm_sub_norm_le x w
      have h2 := norm_sub_norm_le z w
      rw [norm_sub_rev z w] at h2
      have hmx := (lt_min_iff.1 hm).1
      have hmz := (lt_min_iff.1 hm).2
      linarith
    have hseg : segment ℝ x z ⊆ S := hS.segment_subset hx hz
    have hdiff : ∀ w ∈ segment ℝ x z, HasFDerivWithinAt H (fderiv ℝ H w) (segment ℝ x z) w :=
      fun w hw ↦ (hd w (hseg hw)).hasFDerivAt.hasFDerivWithinAt
    have hbound : ∀ w ∈ segment ℝ x z, ‖fderiv ℝ H w‖ ≤ K * h ^ (α - 1) := by
      intro w hw
      have hw0 : w ≠ 0 := by
        intro h0; have := hfar w hw; rw [h0, norm_zero] at this; linarith
      exact (hH' w (hseg hw) hw0).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hpos (hfar w hw) (by linarith)) hK)
    have hmv := (convex_segment x z).norm_image_sub_le_of_norm_hasFDerivWithin_le hdiff hbound
      (right_mem_segment ℝ x z) (left_mem_segment ℝ x z)
    calc ‖H x - H z‖ ≤ K * h ^ (α - 1) * ‖x - z‖ := hmv
      _ = K * h ^ α := by
        rw [← hh, mul_assoc, ← Real.rpow_add_one hpos.ne']
        ring_nf
      _ ≤ (2 * 3 ^ α * A + K) * h ^ α := by
        rw [add_mul]; exact le_add_of_nonneg_left (by positivity)

end HolderSpace
