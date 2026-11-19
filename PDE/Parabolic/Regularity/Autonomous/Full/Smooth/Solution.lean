/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean.SpaceTime
public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.Classical

/-!
# Smooth classical solutions of the full parabolic equation

The solution is one scalar function on spacetime. Its ordinary partial
derivatives satisfy the signed full equation, and its pointwise values attain
the initial and lateral data. Smoothness means that every finite derivative extends
continuously to the closed cylinder.
-/

@[expose] public section

namespace PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.Smooth

open Set PDE.Common SobolevSpace SobolevSpace.GraphSpace.BoundaryRegularity

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The classical homogeneous Dirichlet problem for the autonomous full
divergence-form operator, including smoothness on the entire closed cylinder. -/
structure IsClassicalSolution (P : SmoothFullCoefficients n Ω)
    (f : SpaceTime n → ℝ) (g : ℝ^n → ℝ) (a b : ℝ) (U : SpaceTime n → ℝ) : Prop where
  continuous : ContinuousOn U (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b))
  smooth : ∀ k : ℕ, ContDiffUpToBoundary k U (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b))
  equation : ∀ t ∈ Ioo a b, ∀ x ∈ Ω,
    (∂[0] U) (timeSpaceCons t x) +
      P.classicalLoad (fun y ↦ U (timeSpaceCons t y)) x = f (timeSpaceCons t x)
  initial : ∀ x ∈ closure Ω, U (timeSpaceCons a x) = g x
  lateral : ∀ t ∈ Icc a b, ∀ x ∈ frontier Ω, U (timeSpaceCons t x) = 0

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.Smooth
