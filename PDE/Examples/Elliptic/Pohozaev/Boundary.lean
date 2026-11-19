/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.Pohozaev.Nonexistence
public import PDE.Spaces.Sobolev.Boundary.Atlas.UnitBall.SmoothGraph

/-!
# Nonexistence for a supercritical power on the ball

On the three-dimensional unit ball the exponent `11/2` is strictly above the
critical exponent `5`. The Pohozaev identity, through
`eq_zero_on_closure_of_supercritical_power`, rules out nonzero classical solutions of
`-Δu = |u|^(11/2 - 1) u` that are `C²` up to the boundary and vanish on it.
-/

@[expose] public noncomputable section

namespace PDE.Examples.Pohozaev

open Set Metric SobolevSpace

/-- A `C²` solution of `-Δu = |u|^{9/2} u` on the three-dimensional unit ball that vanishes
on the sphere is identically zero. The solution may change sign. -/
theorem unitBall_three_eq_zero_of_power_eleven_halves
    {u : ℝ^3 → ℝ} (hu : ContDiffUpToBoundary 2 u (ball 0 1))
    (hc : ContinuousOn u (closure (ball 0 1)))
    (hzero : ∀ x ∈ frontier (ball 0 1), u x = 0)
    (hpde : ∀ x ∈ ball 0 1, -laplacian u x = |u x| ^ ((11 : ℝ) / 2 - 1) * u x) :
    EqOn u 0 (closure (ball 0 1)) := by
  apply Elliptic.Semilinear.eq_zero_on_closure_of_supercritical_power
    (m := 2) (c := (0 : ℝ^3)) (p := (11 : ℝ) / 2) (by norm_num)
    isOpen_ball isBounded_ball
    ((Boundary.Atlas.UnitBall.hasContDiffGraphBoundary 3 1).hasC1GraphBoundary le_rfl)
    ?_ (by norm_num) hu hc hzero hpde
  rw [closure_ball (0 : ℝ^3) one_ne_zero]
  exact (convex_closedBall (0 : ℝ^3) 1).starConvex (mem_closedBall_self zero_le_one)

end PDE.Examples.Pohozaev
