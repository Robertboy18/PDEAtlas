/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.BackwardUniqueness.Classical
public import PDE.Parabolic.Symbolic.Heat.Polynomial
public import PDE.Parabolic.Heat.SeparationOfVariables
public import PDE.Spaces.Sobolev.Boundary.Atlas.UnitBall.SmoothGraph
import PDE.Symbolic.PDEDerivatives

import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Nonzero boundary data in backwards heat uniqueness

The disk polynomial `|x|² + 4t` determines arbitrary classical competitors from
lateral and terminal values.
-/

@[expose] public noncomputable section

namespace PDE.Examples.Parabolic.BackwardUniqueness

open HeatEquation

open PDE.Common PDE.Representations Set SobolevSpace
open Boundary.Atlas.UnitBall
open Symbolic.Space2

/-- The certified polynomial `|x|² + 4t`, in time-first coordinates. -/
theorem polynomialHeat2DAnsatz_eval (p : ℝ^3) :
    polynomialHeat2DAnsatz.eval p = p 1 ^ 2 + p 2 ^ 2 + 4 * p 0 := by
  rfl

/-- Any classical disk solution with the polynomial's lateral and terminal
values is that polynomial at all earlier times, including the initial time. -/
theorem disk_polynomial_unique {T : ℝ} (hT : 0 < T) {u : ℝ^3 → ℝ}
    (hu : ContDiffUpToBoundary 2 u (spaceTimeCylinder (domain 2) (Ioo 0 T)))
    (hc : ContinuousOn u (closure (spaceTimeCylinder (domain 2) (Ioo 0 T))))
    (hPDE : ∀ x ∈ domain 2, ∀ t ∈ Ioo 0 T, heatOperator u (timeSpaceCons t x) = 0)
    (hb : ∀ x ∈ frontier (domain 2), ∀ t ∈ Icc 0 T,
      u (timeSpaceCons t x) = polynomialHeat2DAnsatz.eval (timeSpaceCons t x))
    (hterminal : ∀ x ∈ domain 2,
      u (timeSpaceCons T x) = polynomialHeat2DAnsatz.eval (timeSpaceCons T x)) :
    ∀ x ∈ closure (domain 2), ∀ t ∈ Icc 0 T,
      u (timeSpaceCons t x) = polynomialHeat2DAnsatz.eval (timeSpaceCons t x) := by
  have hpoly : ContDiff ℝ 2 (fun p : ℝ^3 ↦ polynomialHeat2DAnsatz.eval p) := by
    simp only [polynomialHeat2DAnsatz_eval]
    fun_prop
  apply eq_on_closedCylinder_of_terminal_eq (isOpen_domain 2) Metric.isBounded_ball
    ((hasContDiffGraphBoundary 2 1).hasC1GraphBoundary le_rfl) hT hu
    (ContDiffUpToBoundary.of_contDiff hpoly
      (isBounded_spaceTimeCylinder Metric.isBounded_ball (Metric.isBounded_Ioo 0 T)))
    hc hpoly.continuous.continuousOn hb hPDE _ hterminal
  exact fun _ _ _ _ ↦ heatEquation.residual_eq polynomialHeat2D_satisfiesPDEProblem_univ trivial

/-- The disk model has nonzero lateral values. -/
theorem disk_polynomial_lateral {x : ℝ^2} (hx : x ∈ frontier (domain 2)) (t : ℝ) :
    polynomialHeat2DAnsatz.eval (timeSpaceCons t x) = 1 + 4 * t := by
  have hn : ‖x‖ = 1 := by
    simpa [domain, frontier_ball (0 : ℝ^2) one_ne_zero,
      Metric.mem_sphere, dist_zero_right] using hx
  have hs := EuclideanSpace.real_norm_sq_eq x
  simp only [Fin.sum_univ_two, hn, one_pow] at hs
  change x 0 ^ 2 + x 1 ^ 2 + 4 * t = 1 + 4 * t
  rw [← hs]

end PDE.Examples.Parabolic.BackwardUniqueness
