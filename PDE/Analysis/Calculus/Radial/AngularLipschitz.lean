/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Lipschitz radial angular fields through the origin

A Lipschitz radial factor vanishing at zero cancels the discontinuity of vector
normalization. The angular factor only needs a Lipschitz bound on the closed unit ball.
Normalization maps into that ball, so in a proper space a continuous field of the direction
is bounded.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Radial

open Metric NormedSpace
open scoped NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Normalization takes values in the closed unit ball, with zero retained. -/
theorem norm_normalize_le_one (x : E) : ‖normalize x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [norm_normalize hx]

/-- A continuous field composed with normalization is bounded. -/
theorem exists_norm_comp_normalize_le [ProperSpace E] {G : Type*} [NormedAddCommGroup G]
    {H : E → G} (hH : Continuous H) :
    ∃ C > 0, ∀ x : E, ‖H (normalize x)‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    ((isCompact_closedBall (0 : E) 1).image hH).isBounded.exists_pos_norm_le
  refine ⟨C, hC, fun x ↦ hbound _ ?_⟩
  apply Set.mem_image_of_mem
  simpa only [mem_closedBall, dist_zero_right] using norm_normalize_le_one x

/-- The singularity in the difference of normalized vectors is canceled by either radius. -/
theorem norm_mul_norm_normalize_sub_le (x y : E) :
    ‖y‖ * ‖normalize x - normalize y‖ ≤ 2 * ‖x - y‖ := by
  have heq : ‖y‖ • (normalize x - normalize y) =
      (x - y) + (‖y‖ - ‖x‖) • normalize x := by
    rw [smul_sub, sub_smul, norm_smul_normalize, norm_smul_normalize]
    abel
  calc
    _ = ‖‖y‖ • (normalize x - normalize y)‖ := by
      rw [norm_smul, Real.norm_of_nonneg (norm_nonneg _)]
    _ ≤ ‖x - y‖ + ‖(‖y‖ - ‖x‖) • normalize x‖ := by rw [heq]; exact norm_add_le _ _
    _ ≤ ‖x - y‖ + ‖‖y‖ - ‖x‖‖ := by
      rw [norm_smul]
      exact add_le_add le_rfl
        (mul_le_of_le_one_right (norm_nonneg _) (norm_normalize_le_one x))
    _ ≤ ‖x - y‖ + ‖x - y‖ := by
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact add_le_add le_rfl (abs_norm_sub_norm_le x y)
    _ = _ := by ring

/-- A radial factor vanishing at zero makes a Lipschitz angular evaluator Lipschitz
on every radius ball where the radial bound is valid. -/
theorem lipschitzOnWith_radial_smul_normalize {A K : ℝ≥0} {R : ℝ} (hR : 0 ≤ R)
    {f : ℝ → ℝ} {H : E → F}
    (hf : LipschitzOnWith A f (Set.Icc 0 R)) (hf0 : f 0 = 0)
    (hH : LipschitzOnWith K H (closedBall 0 1)) :
    LipschitzOnWith (A * (‖H 0‖₊ + 3 * K))
      (fun x ↦ f ‖x‖ • H (normalize x)) (closedBall 0 R) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hxR : ‖x‖ ∈ Set.Icc 0 R :=
    ⟨norm_nonneg _, by simpa [mem_closedBall, dist_zero_right] using hx⟩
  have hyR : ‖y‖ ∈ Set.Icc 0 R :=
    ⟨norm_nonneg _, by simpa [mem_closedBall, dist_zero_right] using hy⟩
  have hn (z : E) : normalize z ∈ closedBall 0 1 := by
    simpa [mem_closedBall, dist_zero_right] using norm_normalize_le_one z
  have hzero : (0 : E) ∈ closedBall 0 1 := by simp
  have hangular : ‖H (normalize x)‖ ≤ ‖H 0‖ + (K : ℝ) := by
    have h := hH.dist_le_mul (normalize x) (hn x) 0 hzero
    rw [dist_eq_norm, dist_zero_right] at h
    calc
      _ ≤ ‖H (normalize x) - H 0‖ + ‖H 0‖ := norm_le_norm_sub_add _ _
      _ ≤ (K : ℝ) * ‖normalize x‖ + ‖H 0‖ := add_le_add h le_rfl
      _ ≤ (K : ℝ) + ‖H 0‖ := add_le_add
        (mul_le_of_le_one_right K.coe_nonneg (norm_normalize_le_one x)) le_rfl
      _ = _ := add_comm _ _
  have hradial : ‖f ‖x‖ - f ‖y‖‖ ≤ (A : ℝ) * ‖x - y‖ := by
    have h := hf.dist_le_mul ‖x‖ hxR ‖y‖ hyR
    rw [dist_eq_norm, Real.dist_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) A.coe_nonneg)
  have hradial0 : ‖f ‖y‖‖ ≤ (A : ℝ) * ‖y‖ := by
    simpa [hf0, dist_zero_right, Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using
      hf.dist_le_mul ‖y‖ hyR 0 (show (0 : ℝ) ∈ Set.Icc 0 R from ⟨le_rfl, hR⟩)
  have hkernel := hH.dist_le_mul (normalize x) (hn x) (normalize y) (hn y)
  rw [dist_eq_norm, dist_eq_norm] at hkernel
  have hsplit : f ‖x‖ • H (normalize x) - f ‖y‖ • H (normalize y) =
      (f ‖x‖ - f ‖y‖) • H (normalize x) +
        f ‖y‖ • (H (normalize x) - H (normalize y)) := by
    rw [sub_smul, smul_sub]
    abel
  rw [dist_eq_norm, hsplit]
  calc
    _ ≤ ‖(f ‖x‖ - f ‖y‖) • H (normalize x)‖ +
        ‖f ‖y‖ • (H (normalize x) - H (normalize y))‖ := norm_add_le _ _
    _ ≤ ((A : ℝ) * ‖x - y‖) * (‖H 0‖ + K) +
        ((A : ℝ) * ‖y‖) * ((K : ℝ) * ‖normalize x - normalize y‖) := by
      simp only [norm_smul]
      exact add_le_add (mul_le_mul hradial hangular (norm_nonneg _) (by positivity))
        (mul_le_mul hradial0 hkernel (norm_nonneg _) (by positivity))
    _ ≤ ((A : ℝ) * ‖x - y‖) * (‖H 0‖ + K) +
        ((A : ℝ) * K) * (2 * ‖x - y‖) := by
      have h := mul_le_mul_of_nonneg_left (norm_mul_norm_normalize_sub_le x y)
        (mul_nonneg A.coe_nonneg K.coe_nonneg)
      nlinarith only [h]
    _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_ofNat,
      coe_nnnorm, dist_eq_norm]; ring

end PDE.Analysis.Radial
