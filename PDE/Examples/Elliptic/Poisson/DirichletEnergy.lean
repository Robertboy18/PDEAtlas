/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Poisson.Variational.Principle
import PDE.Spaces.Sobolev.Calculus.Differentiation.LocalSobolev
import PDE.Spaces.Sobolev.Boundary.Atlas.UnitBall.SmoothGraph
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# Nonzero affine boundary data for the Dirichlet energy

On `(-1,1)`, the quadratic `x² + x + 2` minimizes the energy with forcing
`-2` and boundary values `2,4`. The affine interpolant `x + 3` has the same
boundary values but is not a minimizer. Both directions of Dirichlet's principle
`poisson_iff_isMinOn_classicalEnergy_of_continuousOn_closure` are used, with a nonzero
source and nonconstant boundary data.
-/

@[expose] public noncomputable section

namespace PDE.Examples.Poisson

open Set MeasureTheory SobolevSpace PoissonEquation

local notation "Ω" => Metric.ball (0 : ℝ^1) 1

/-- The quadratic solution, with unequal nonzero endpoint values. -/
def profile (x : ℝ^1) : ℝ := x 0 ^ 2 + x 0 + 2

/-- The affine interpolation of the same endpoint values. -/
def boundaryLine (x : ℝ^1) : ℝ := x 0 + 3

/-- `profile` is `C²`. -/
theorem profile_contDiff : ContDiff ℝ 2 profile := by
  cas

/-- `boundaryLine` is `C²`. -/
theorem boundaryLine_contDiff : ContDiff ℝ 2 boundaryLine := by
  cas

/-- The Laplacian of the quadratic is `2`, so it solves `-Δu = -2`. -/
theorem profile_laplacian (x : ℝ^1) : laplacian profile x = 2 := by
  simp only [laplacian, Fin.sum_univ_one]
  cas

/-- The Laplacian of the affine interpolant is `0`, so it does not solve `-Δu = -2`. -/
theorem boundaryLine_laplacian (x : ℝ^1) : laplacian boundaryLine x = 0 := by
  simp only [laplacian, Fin.sum_univ_one]
  cas

/-- `profile` and `boundaryLine` agree at the endpoints `±1`. -/
theorem profile_eq_boundaryLine : EqOn profile boundaryLine (frontier Ω) := by
  intro x hx
  have hn : ‖x‖ = 1 := by
    simpa [frontier_ball (0 : ℝ^1) one_ne_zero] using hx
  have hsq : x 0 ^ 2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq x
    simpa [hn, Fin.sum_univ_one] using h.symm
  dsimp [profile, boundaryLine]
  rw [hsq]
  ring

private theorem closure_class {u : ℝ^1 → ℝ} (hu : ContDiff ℝ 2 u)
    (hbd : EqOn u boundaryLine (frontier Ω)) :
    u ∈ classicalDirichletClass Ω boundaryLine :=
  ⟨contDiffUpToBoundary_of_contDiffOn isOpen_univ hu.contDiffOn
      Metric.isBounded_ball.isCompact_closure (subset_univ _),
    hu.continuous.continuousOn, hbd⟩

/-- `profile` minimizes the energy with forcing `-2` among all classical functions with the
boundary values of `boundaryLine`. -/
theorem profile_minimizes :
    IsMinOn (classicalEnergy Ω (fun _ ↦ -2))
      (classicalDirichletClass Ω boundaryLine) profile := by
  apply (poisson_iff_isMinOn_classicalEnergy_of_continuousOn_closure
    Metric.isOpen_ball Metric.isBounded_ball
    ((Boundary.Atlas.UnitBall.hasContDiffGraphBoundary 1 1).hasC1GraphBoundary le_rfl)
    (closure_class profile_contDiff profile_eq_boundaryLine) continuousOn_const).mp
  intro x _
  rw [profile_laplacian]

/-- The affine interpolant does not minimize the energy, since it does not solve the
Poisson equation. -/
theorem boundaryLine_not_minimizes :
    ¬IsMinOn (classicalEnergy Ω (fun _ ↦ -2))
      (classicalDirichletClass Ω boundaryLine) boundaryLine := by
  intro hmin
  have hpde := (poisson_iff_isMinOn_classicalEnergy_of_continuousOn_closure
    Metric.isOpen_ball Metric.isBounded_ball
    ((Boundary.Atlas.UnitBall.hasContDiffGraphBoundary 1 1).hasC1GraphBoundary le_rfl)
    (closure_class boundaryLine_contDiff (fun _ _ ↦ rfl)) continuousOn_const).mpr hmin
  have h := hpde 0 (by simp)
  rw [boundaryLine_laplacian] at h
  norm_num at h

/-- The endpoint values are unequal and both nonzero. -/
theorem profile_endpoints :
    profile (EuclideanSpace.single 0 (-1)) = 2 ∧
      profile (EuclideanSpace.single 0 1) = 4 := by
  norm_num [profile]

end PDE.Examples.Poisson
