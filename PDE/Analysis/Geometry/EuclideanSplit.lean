/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean

/-!
# Euclidean norms under the time-space split

These estimates use the Euclidean norm, rather than the maximum norm on a
product. Projection contracts distances, and the zero-time embedding is an
isometry.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open PDE.Common

variable {n : ℕ}

/-- Pythagoras for the zeroth coordinate and the remaining coordinates. -/
theorem norm_sq_eq_time_add_spatial (p : ℝ^(n + 1)) :
    ‖p‖ ^ 2 = (p 0) ^ 2 + ‖spatialPart p‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ, PiLp.norm_sq_eq_of_L2]
  simp only [Real.norm_eq_abs, sq_abs, spatialPart_apply]

/-- The spatial projection contracts the Euclidean norm. -/
theorem norm_spatialPart_le (p : ℝ^(n + 1)) : ‖spatialPart p‖ ≤ ‖p‖ := by
  have h := norm_sq_eq_time_add_spatial p
  nlinarith [sq_nonneg (p 0), norm_nonneg p, norm_nonneg (spatialPart p)]

/-- The norm of an assembled point is at most the sum of its component norms. -/
theorem norm_timeSpaceCons_le (t : ℝ) (x : ℝ^n) :
    ‖timeSpaceCons t x‖ ≤ |t| + ‖x‖ := by
  have h := norm_sq_eq_time_add_spatial (timeSpaceCons t x)
  simp only [timeSpaceCons_zero, spatialPart_timeSpaceCons] at h
  nlinarith [sq_abs t, abs_nonneg t, norm_nonneg x, norm_nonneg (timeSpaceCons t x)]

/-- The zero-time embedding preserves the Euclidean norm. -/
theorem norm_timeSpaceCons_zero (x : ℝ^n) : ‖timeSpaceCons 0 x‖ = ‖x‖ := by
  have h := norm_sq_eq_time_add_spatial (timeSpaceCons 0 x)
  simp only [timeSpaceCons_zero, spatialPart_timeSpaceCons, zero_pow (by decide : 2 ≠ 0),
    zero_add] at h
  nlinarith [norm_nonneg x, norm_nonneg (timeSpaceCons 0 x)]

/-- Spatial projection contracts distances. -/
theorem dist_spatialPart_le (p q : ℝ^(n + 1)) :
    dist (spatialPart p) (spatialPart q) ≤ dist p q := by
  have hsub : spatialPart (p - q) = spatialPart p - spatialPart q := by
    simp only [← spatialPartCLM_eq_spatialPart, map_sub]
  simpa only [dist_eq_norm, hsub] using norm_spatialPart_le (p - q)

/-- Distances between zero-time points are their spatial distances. -/
theorem dist_timeSpaceCons_zero (x y : ℝ^n) :
    dist (timeSpaceCons 0 x) (timeSpaceCons 0 y) = dist x y := by
  have hsub : timeSpaceCons 0 x - timeSpaceCons 0 y = timeSpaceCons 0 (x - y) := by
    ext i
    cases i using Fin.cases <;> simp
  rw [dist_eq_norm, hsub, norm_timeSpaceCons_zero, dist_eq_norm]

end PDE.Analysis
