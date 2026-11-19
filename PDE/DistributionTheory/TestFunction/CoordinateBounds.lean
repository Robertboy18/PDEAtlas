/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import PDE.Common.Euclidean

/-!
# Coordinate bounds for compact tests

A test supported in a ball remains bounded after multiplication by any coordinate.
The bound is its supremum norm times the ball radius.
-/

@[expose] public section

open TopologicalSpace
open scoped Distributions BoundedContinuousFunction

namespace TestFunction

/-- Multiplication by a coordinate costs at most the support radius, in every
Euclidean dimension. -/
theorem norm_mul_coordinate_le_of_tsupport_subset_closedBall {n : ℕ}
    (χ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (R : ℝ) (hR : 0 ≤ R)
    (hsupp : tsupport (χ : ℝ^n → ℝ) ⊆ Metric.closedBall 0 R)
    (i : Fin n) (x : ℝ^n) :
    ‖χ x * x i‖ ≤ ‖(χ : ℝ^n →ᵇ ℝ)‖ * R := by
  by_cases hx : x ∈ tsupport (χ : ℝ^n → ℝ)
  · have hxR : ‖x‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hsupp hx
    rw [norm_mul]
    exact mul_le_mul ((χ : ℝ^n →ᵇ ℝ).norm_coe_le_norm x)
      ((PiLp.norm_apply_le x i).trans hxR) (norm_nonneg _) (norm_nonneg _)
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, norm_zero]
    exact mul_nonneg (norm_nonneg _) hR

end TestFunction
