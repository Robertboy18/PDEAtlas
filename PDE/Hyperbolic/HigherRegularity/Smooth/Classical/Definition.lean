/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Smooth.Compatibility.BoundaryValues
public import PDE.Spaces.Sobolev.Evolution.Classical.Representative.Identification

/-!
# Smooth classical Dirichlet waves

A classical wave is one function continuous on the closed cylinder and smooth
to every finite order up to its boundary. Its canonical mixed fields are the
continuous extensions of its interior derivatives. The equation includes
both time endpoints; the prescribed initial values are the canonical closure
values of the given spatial data.

This formulation does not require smooth extensions outside the domain or the
time interval. Derivatives of the canonical fields inside the interval, including the
original value function, come from the representative theorems.
-/

@[expose] public section

open PDE (SpaceTime)

namespace Hyperbolic.HigherRegularity.SmoothWave

open Set PDE.Common SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity SobolevSpace.Evolution.Classical

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- A single smooth classical wave with the full signed operator, homogeneous
lateral boundary values, and the two prescribed initial data. -/
structure IsClassicalSolution
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    {f : SpaceTime n → ℝ} {g h : ℝ^n → ℝ}
    (hf : ∀ k, ContDiffUpToBoundary k f (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b)))
    (hg : ∀ k, ContDiffUpToBoundary k g Ω)
    (hh : ∀ k, ContDiffUpToBoundary k h Ω) (U : SpaceTime n → ℝ) : Prop where
  /-- Literal values are continuous on the entire closed cylinder. -/
  continuous : ContinuousOn U (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b))
  /-- All finite orders belong to the same joint representative. -/
  smooth : ∀ k, ContDiffUpToBoundary k U (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b))
  /-- The full pointwise wave equation, with canonical endpoint forcing. -/
  equation : ∀ t ∈ Icc a b, ∀ x ∈ Ω,
    derivativeSlice hopen smooth [0, 0] t x +
      P.classicalLoad (fun y ↦ U (timeSpaceCons t y)) x =
        derivativeSlice hopen hf [] t x
  /-- The homogeneous lateral boundary condition includes both time endpoints. -/
  boundary : ∀ t ∈ Icc a b, ∀ x ∈ frontier Ω, U (timeSpaceCons t x) = 0
  /-- The initial displacement is the canonical closure value of `g`. -/
  initial_value : ∀ x ∈ closure Ω,
    U (timeSpaceCons a x) = (hg 0).continuousRepresentative x
  /-- The initial velocity is the canonical closure value of `h`. -/
  initial_velocity : ∀ x ∈ closure Ω,
    derivativeSlice hopen smooth [0] a x = (hh 0).continuousRepresentative x

end Hyperbolic.HigherRegularity.SmoothWave
