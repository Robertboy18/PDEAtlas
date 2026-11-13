/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Forward intersections of lines with the unit sphere

For a unit direction, the positive root of the norm-squared equation is the exit time
from the unit ball. At a sphere point where the direction points outward, that root is
zero and varies continuously. Consequently the entire exit segment from a nearby point
stays in any prescribed neighborhood of the sphere point.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Set Metric Filter
open scoped Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The forward exit time from the unit ball in a unit direction. Its formula is defined
everywhere; the geometric interpretation requires an interior starting point. -/
def unitBallExitTime (e y : E) : ℝ :=
  -⟪y, e⟫ + √(⟪y, e⟫ ^ 2 + 1 - ‖y‖ ^ 2)

/-- The quadratic exit-time formula is continuous, including at the sphere. -/
theorem continuous_unitBallExitTime (e : E) : Continuous (unitBallExitTime e) := by
  unfold unitBallExitTime
  fun_prop

/-- The forward exit time is strictly positive from every interior point. -/
theorem unitBallExitTime_pos (e : E) {y : E} (hy : ‖y‖ < 1) :
    0 < unitBallExitTime e y := by
  have hsq : ‖y‖ ^ 2 < 1 := by nlinarith [norm_nonneg y]
  have hrad : 0 ≤ ⟪y, e⟫ ^ 2 + 1 - ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg ⟪y, e⟫]
  have hs := Real.sq_sqrt hrad
  have hn := Real.sqrt_nonneg (⟪y, e⟫ ^ 2 + 1 - ‖y‖ ^ 2)
  unfold unitBallExitTime
  nlinarith [sq_nonneg ⟪y, e⟫]

/-- The exit-time formula reaches the sphere when the direction has unit norm. -/
theorem norm_add_unitBallExitTime_smul {e y : E} (he : ‖e‖ = 1) (hy : ‖y‖ < 1) :
    ‖y + unitBallExitTime e y • e‖ = 1 := by
  have ht := unitBallExitTime_pos e hy
  have hrad : 0 ≤ ⟪y, e⟫ ^ 2 + 1 - ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg ⟪y, e⟫, norm_nonneg y]
  have hs := Real.sq_sqrt hrad
  have hn := norm_add_sq_real y (unitBallExitTime e y • e)
  simp only [real_inner_smul_right, norm_smul, he, mul_one, Real.norm_eq_abs,
    abs_of_pos ht] at hn
  have hroot : (unitBallExitTime e y) ^ 2 + 2 * unitBallExitTime e y * ⟪y, e⟫ =
      1 - ‖y‖ ^ 2 := by
    dsimp [unitBallExitTime]
    nlinarith
  nlinarith [norm_nonneg (y + unitBallExitTime e y • e)]

/-- At an outward-pointing sphere point, the forward root is zero. -/
theorem unitBallExitTime_eq_zero {e x : E} (hx : ‖x‖ = 1) (he : 0 ≤ ⟪x, e⟫) :
    unitBallExitTime e x = 0 := by
  simp [unitBallExitTime, hx, Real.sqrt_sq he]

/-- Near an outward-pointing sphere point the entire forward exit segment remains
in any given ball around that point. No compactness or dimension assumption is needed. -/
theorem eventually_exit_segment_mem_ball {e x : E} (he : ‖e‖ = 1)
    (hx : ‖x‖ = 1) (hxe : 0 ≤ ⟪x, e⟫) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc 0 (unitBallExitTime e y), y + t • e ∈ ball x r := by
  have htime : ∀ᶠ y in 𝓝 x, unitBallExitTime e y < r / 2 :=
    (continuous_unitBallExitTime e).continuousAt.eventually_lt_const
      (by rw [unitBallExitTime_eq_zero hx hxe]; exact half_pos hr)
  filter_upwards [Metric.ball_mem_nhds x (half_pos hr), htime] with y hy ht t htrange
  rw [Metric.mem_ball] at hy ⊢
  calc
    dist (y + t • e) x = ‖(y - x) + t • e‖ := by
      rw [dist_eq_norm]
      congr 1
      abel
    _ ≤ ‖y - x‖ + ‖t • e‖ := norm_add_le _ _
    _ = dist y x + t := by
      rw [dist_eq_norm, norm_smul, he, mul_one, Real.norm_eq_abs,
        abs_of_nonneg htrange.1]
    _ < r := by linarith [htrange.2]

end PDE.Analysis
