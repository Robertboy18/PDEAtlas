/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MeanValue.Formulas

/-!
# Integral bounds from the mean-value formula

The value at the center of a ball is its average. Taking absolute values gives
a pointwise bound by the average of the absolute value. If that ball sits in
a larger integration set, positivity lets us use the larger integral instead.
These two observations supply the function bounds used in interior derivative
estimates.
-/

@[expose] public section

open MeasureTheory Metric Set
open PDE.Analysis

namespace LaplacianEquation

/-- The mean-value formula bounds the value at the center by the average of `|u|`.
Integrability is explicit because a continuous function on an open ball need not
be integrable up to its boundary. -/
theorem HasSphereMeanValueProperty.abs_le_integral_abs
    {n : ℕ} [Fact (0 < n)] {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : HasSphereMeanValueProperty n u U) {x : ℝ^n} {r : ℝ}
    (hr : 0 < r) (hball : closedBall x r ⊆ U)
    (hint : IntegrableOn u (ball x r) volume) :
    |u x| ≤ (∫ y in ball x r, |u y|) / (unitBallVolume n * r ^ n) := by
  have hvolume : ballVolume n r = unitBallVolume n * r ^ n :=
    ballVolume_eq_unitBallVolume_mul_pow n r hr.le
  have hα : 0 < unitBallVolume n := unitBallVolume_pos n
  have hvolume_pos : 0 < ballVolume n r := by
    rw [hvolume]
    positivity
  have hmean : u x = (∫ y in ball x r, u y) / ballVolume n r := by
    simpa [ballAverage, ballIntegral, hr] using
      hu.eq_ballAverage x (hball (mem_closedBall_self hr.le)) r hr hball hint
  calc
    |u x| = |∫ y in ball x r, u y| / ballVolume n r := by
      rw [hmean, abs_div, abs_of_pos hvolume_pos]
    _ ≤ (∫ y in ball x r, |u y|) / ballVolume n r :=
      (div_le_div_iff_of_pos_right hvolume_pos).2 abs_integral_le_integral_abs
    _ = (∫ y in ball x r, |u y|) / (unitBallVolume n * r ^ n) := by
      rw [hvolume]

/-- A mean-value bound can use the integral over any larger integration region.
The estimate still spends only the radius of the ball centered at the point. -/
theorem HasSphereMeanValueProperty.abs_le_integral_abs_of_subset
    {n : ℕ} [Fact (0 < n)] {u : ℝ^n → ℝ} {U s : Set (ℝ^n)}
    (hu : HasSphereMeanValueProperty n u U) {x : ℝ^n} {r : ℝ}
    (hr : 0 < r) (hball : closedBall x r ⊆ U)
    (hsubset : ball x r ⊆ s) (hint : IntegrableOn u s volume) :
    |u x| ≤ (∫ y in s, |u y|) / (unitBallVolume n * r ^ n) := by
  have hα : 0 < unitBallVolume n := unitBallVolume_pos n
  refine (hu.abs_le_integral_abs hr hball (hint.mono_set hsubset)).trans ?_
  apply (div_le_div_iff_of_pos_right (by positivity)).2
  exact setIntegral_mono_set hint.abs
    (Filter.Eventually.of_forall fun y ↦ abs_nonneg (u y))
    (Filter.Eventually.of_forall fun y hy ↦ hsubset hy)

end LaplacianEquation
