/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Geometry.EuclideanBall.Dimension
import CAS.ExactTactic

/-!
# Sphere-to-ball normalization

Projection from the unit sphere in one higher dimension contributes twice
the base-ball integral. In even base dimension, the ratio of its normalized
averages is an odd double factorial divided by an even double factorial.
The one-dimensional ratio contains `π`.
-/

@[expose] public noncomputable section

open scoped Nat

namespace PDE.Analysis

/-- Exact normalization for projection onto an even-dimensional ball. -/
theorem two_mul_unitBallVolume_div_unitSphereArea_even (k : ℕ) :
    2 * unitBallVolume (2 * k + 2) / unitSphereArea (2 * k + 3) =
      ((2 * k + 1)‼ : ℝ) / (2 * k + 2)‼ := by
  have he : 2 * k + 2 = 2 * (k + 1) := by omega
  have ho : 2 * k + 3 = 2 * (k + 1) + 1 := by omega
  rw [unitSphereArea_eq, he, ho, unitBallVolume_two_mul,
    unitBallVolume_two_mul_add_one, Nat.doubleFactorial_two_mul]
  rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
    Nat.doubleFactorial_add_two]
  push_cast
  have hp : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hf : (k + 1 : ℝ) ≠ 0 := by positivity
  have hd : ((2 * k + 1)‼ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos (2 * k + 1)).ne'
  field_simp
  ring

/-- Projection from a circle to an interval has ratio `2 / π`. -/
theorem two_mul_unitBallVolume_div_unitSphereArea_one :
    2 * unitBallVolume 1 / unitSphereArea 2 = 2 / Real.pi := by
  rw [unitBallVolume_one, unitSphereArea_two]
  cas using Real.pi_pos

/-- The planar sphere-to-ball ratio is one half. -/
theorem two_mul_unitBallVolume_div_unitSphereArea_two :
    2 * unitBallVolume 2 / unitSphereArea 3 = 1 / 2 := by
  simpa using two_mul_unitBallVolume_div_unitSphereArea_even 0

/-- The four-dimensional sphere-to-ball ratio is three eighths. -/
theorem two_mul_unitBallVolume_div_unitSphereArea_four :
    2 * unitBallVolume 4 / unitSphereArea 5 = 3 / 8 := by
  simpa [Nat.doubleFactorial] using two_mul_unitBallVolume_div_unitSphereArea_even 1

end PDE.Analysis
