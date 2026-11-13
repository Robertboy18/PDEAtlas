/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.SphereProjection.Scaling

/-!
# Spherical averages of coordinate lifts

The average of a lifted function depends on the entire ambient center only
through its projection. At positive radius, its weighted profile is a weighted
ball average with the volume normalization.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace PDE.Analysis

variable {n : ℕ}

/-- The fixed-sphere average of lifted data is independent of the last center coordinate,
including at zero and negative radii and without a regularity hypothesis. -/
theorem unitSphereAverage_coordinateProjection_center (f : ℝ^n → ℝ)
    (z : ℝ^(n + 1)) (r : ℝ) :
    unitSphereAverage (n + 1) (f ∘ coordinateProjection) z r =
      unitSphereAverage (n + 1) (f ∘ coordinateProjection)
        (coordinateInclusion (coordinateProjection z)) r := by
  simp only [unitSphereAverage, Function.comp_apply, map_add, map_smul,
    coordinateProjection_coordinateInclusion]

/-- The fixed-sphere average of continuous lifted data is a weighted unit-ball integral
for every signed radius. -/
theorem unitSphereAverage_coordinateProjection {f : ℝ^n → ℝ} (hf : Continuous f)
    (z : ℝ^(n + 1)) (r : ℝ) :
    unitSphereAverage (n + 1) (f ∘ coordinateProjection) z r =
      (2 / unitSphereArea (n + 1)) * ∫ y in Metric.ball (0 : ℝ^n) 1,
        f (coordinateProjection z + r • y) / √(1 - ‖y‖ ^ 2) := by
  have hc : Continuous (fun y : ℝ^n ↦ f (coordinateProjection z + r • y)) :=
    hf.comp (by fun_prop)
  simp only [unitSphereAverage, Function.comp_apply, map_add, map_smul]
  rw [integral_sphere_eq_ball_weight hc]
  ring

/-- At positive radius, the weighted spherical profile equals the weighted ball
average with normalization `2α_n/s_(n+1)`. -/
theorem pow_mul_unitSphereAverage_coordinateProjection [Fact (0 < n)]
    {f : ℝ^n → ℝ} (hf : Continuous f) (z : ℝ^(n + 1)) {r : ℝ} (hr : 0 < r) :
    r ^ (n - 1) * unitSphereAverage (n + 1) (f ∘ coordinateProjection) z r =
      (2 * unitBallVolume n / unitSphereArea (n + 1)) *
        (r ^ n * ballAverage n
          (fun y ↦ f y / √(r ^ 2 - ‖y - coordinateProjection z‖ ^ 2))
          (coordinateProjection z) r) := by
  rw [unitSphereAverage_coordinateProjection hf, ballAverage, ite_eq_left hr,
    ballIntegral, ballVolume_eq_unitBallVolume_mul_pow n r hr.le,
    integral_ball_sqrt_scale _ _ hr]
  have hα : unitBallVolume n ≠ 0 := (unitBallVolume_pos n).ne'
  have hs : unitSphereArea (n + 1) ≠ 0 := unitSphereArea_pos.ne'
  field_simp

end PDE.Analysis
