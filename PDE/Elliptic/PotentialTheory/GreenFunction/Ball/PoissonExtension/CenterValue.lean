/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.Ball.Definitions
import PDE.Elliptic.PotentialTheory.FundamentalSolution -- shake: keep

/-!
# Center value of the ball Poisson extension

At the center of a ball, the Poisson extension reduces to the spherical average of its boundary
data.
-/

@[expose] public section

namespace GreenFunction

open PDE.Analysis
open PotentialTheory
open MeasureTheory

/-- At the center of the ball, the Poisson extension is the spherical average of its boundary
data. -/
theorem poissonBallExtension_zero_eq_sphereAverage {n : ℕ} [Fact (0 < n)]
    {r : ℝ} (hr : 0 < r) (g : ℝ^n → ℝ) :
    poissonBallExtension (n := n) r g 0 = sphereAverage n g 0 r := by
  classical
  unfold poissonBallExtension
  simp only [dist_eq_norm, norm_zero, sphereAverage, ite_eq_left hr]
  unfold sphereIntegral sphereArea
  rw [unitSphereArea_eq]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
    abs_of_pos hr, zero_add, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs,
    norm_eq_of_mem_sphere, mul_one]
  rw [integral_div]
  have hn : 1 ≤ n := Nat.succ_le_of_lt Fact.out
  have hp : r * r ^ (n - 1) = r ^ n := by
    rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hn]
  have hden : (n : ℝ) * unitBallVolume n ≠ 0 := by
    rw [← unitSphereArea_eq]
    exact ne_of_gt unitSphereArea_pos
  field_simp [hr.ne', hden]
  rw [hp]
  ring

end GreenFunction
