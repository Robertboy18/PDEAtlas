/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# Support and agreement for a rescaled bump product

Rescaling a bump at the origin multiplies both radii by the scale. Multiplication by
an arbitrary vector-valued map preserves the support bound and agrees with that map
on the smaller closed ball.
-/

@[expose] public section

open Function Metric Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [HasContDiffBump E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A rescaled bump product is supported in the rescaled outer closed ball. -/
theorem ContDiffBump.tsupport_rescaled_smul_subset (b : ContDiffBump (0 : E))
    (N : E → F) {s : ℝ} (hs : 0 < s) :
    tsupport (fun x ↦ b (s⁻¹ • x) • N x) ⊆ closedBall 0 (s * b.rOut) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  rw [mem_closedBall_zero_iff]
  by_contra h
  have hb : b (s⁻¹ • x) = 0 := by
    apply b.zero_of_le_dist
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs,
      ← div_eq_inv_mul, le_div_iff₀ hs]
    exact (mul_comm s b.rOut ▸ (lt_of_not_ge h)).le
  exact hx (by simp only [hb, zero_smul])

/-- A rescaled bump product equals the original map on the rescaled inner closed ball. -/
theorem ContDiffBump.rescaled_smul_eqOn (b : ContDiffBump (0 : E))
    (N : E → F) {s : ℝ} (hs : 0 < s) :
    EqOn (fun x ↦ b (s⁻¹ • x) • N x) N (closedBall 0 (s * b.rIn)) := by
  intro x hx
  have hb : b (s⁻¹ • x) = 1 := by
    apply b.one_of_mem_closedBall
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs,
      ← div_eq_inv_mul, div_le_iff₀ hs]
    simpa only [mul_comm] using mem_closedBall_zero_iff.mp hx
  simp only [hb, one_smul]
