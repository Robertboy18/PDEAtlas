/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GlobalGraphChart
import Mathlib.Geometry.Manifold.SmoothApprox

/-!
# Global smooth representatives of the spherical graph

The positive sphere height `sqrt (1 - ‖x'‖²)` is smooth only for `‖x'‖ < 1`.
Mathlib's relative smooth approximation theorem produces a globally smooth function
agreeing with it on every closed tangential cylinder of radius below one. The concrete
unit-ball atlas applies the generic graph-flattening maps to this representative.

Generic triangular maps and their restricted charts are defined in
`PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GlobalGraphChart`.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Extension.GraphChart

open Metric Set

variable (n : ℕ)

section PositiveDimension

variable [Fact (0 < n)]

/-!
## Global smooth extension of the spherical graph

The natural height `sqrt (1 - ‖x'‖²)` is smooth only while `‖x'‖ < 1`.
For a boundary cap whose tangential projection stays in a smaller closed
ball, Mathlib's relative smooth-approximation theorem supplies a globally
smooth function agreeing *exactly* with that height on the entire cap.
-/

/-- Radicand of the unit-sphere graph over the tangential hyperplane. -/
def sphereRadicand (x : ℝ^n) : ℝ :=
  1 - ‖HalfSpace.boundaryProjection n x‖ ^ 2

/-- Continuous, globally defined square-root height.  It agrees with the
positive sphere graph wherever the radicand is positive. -/
def sphereHeight (x : ℝ^n) : ℝ :=
  Real.sqrt (sphereRadicand n x)

/-- Closed tangential cylinder on which a global smooth representative will
agree with `sphereHeight`. -/
def tangentialCylinder (r : ℝ) : Set (ℝ^n) :=
  {x | ‖HalfSpace.boundaryProjection n x‖ ≤ r}

/-- Open region where the spherical height is smooth. -/
def sphereGraphRegion : Set (ℝ^n) :=
  {x | 0 < sphereRadicand n x}

/-- The polynomial radicand of the spherical graph is smooth. -/
theorem sphereRadicand_contDiff (m : ℕ∞) :
    ContDiff ℝ m (sphereRadicand n) := by
  exact
    (contDiff_const : ContDiff ℝ m fun _ : ℝ^n ↦ (1 : ℝ)).sub <|
      (contDiff_norm_sq ℝ).comp (HalfSpace.contDiff_boundaryProjection n m)

/-- The globally defined square-root height of the sphere is continuous. -/
theorem sphereHeight_continuous :
    Continuous (sphereHeight n) := by
  exact Real.continuous_sqrt.comp (sphereRadicand_contDiff n 0).continuous

/-- Every closed tangential cylinder is a closed subset of Euclidean space. -/
theorem isClosed_tangentialCylinder (r : ℝ) :
    IsClosed (tangentialCylinder n r) := by
  exact isClosed_Iic.preimage (HalfSpace.contDiff_boundaryProjection n 0).continuous.norm

/-- Positivity of the spherical radicand defines an open region. -/
theorem isOpen_sphereGraphRegion :
    IsOpen (sphereGraphRegion n) := by
  exact isOpen_Ioi.preimage (sphereRadicand_contDiff n 0).continuous

/-- A tangential cylinder of radius below one lies in the smooth spherical region. -/
theorem tangentialCylinder_subset_sphereGraphRegion
    {r : ℝ} (hr1 : r < 1) :
    tangentialCylinder n r ⊆ sphereGraphRegion n := by
  intro x hx
  have hnorm0 : 0 ≤ ‖HalfSpace.boundaryProjection n x‖ := norm_nonneg _
  have hnorm1 : ‖HalfSpace.boundaryProjection n x‖ < 1 := lt_of_le_of_lt hx hr1
  change 0 < 1 - ‖HalfSpace.boundaryProjection n x‖ ^ 2
  nlinarith

/-- The spherical height is smooth wherever its radicand is positive. -/
theorem sphereHeight_contDiffOn :
    ContDiffOn ℝ (⊤ : ℕ∞) (sphereHeight n) (sphereGraphRegion n) := by
  exact
    (sphereRadicand_contDiff n (⊤ : ℕ∞)).contDiffOn.sqrt <| by
      intro x hx
      exact ne_of_gt hx

/-- A globally smooth total representative of the positive unit-sphere
height exists on every strictly smaller tangential cylinder.

The equality is exact, not an approximation.  Approximation is used only
outside the closed cylinder to extend the local smooth function globally. -/
theorem exists_globalSphereHeight_contDiff_eqOn
    {r : ℝ} (hr1 : r < 1) :
    ∃ height : ℝ^n → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) height ∧
      Set.EqOn height (sphereHeight n) (tangentialCylinder n r) := by
  obtain ⟨g, hg, -, heq, -⟩ :=
    (sphereHeight_continuous n).exists_contDiff_approx_and_eqOn
      (⊤ : ℕ∞)
      (f := sphereHeight n)
      (ε := fun _ : ℝ^n ↦ (1 : ℝ))
      continuous_const
      (fun _ ↦ zero_lt_one)
      (isClosed_tangentialCylinder n r)
      ((isOpen_sphereGraphRegion n).mem_nhdsSet.2
        (tangentialCylinder_subset_sphereGraphRegion n hr1))
      (sphereHeight_contDiffOn n)
  exact ⟨g, hg, heq⟩

end PositiveDimension

end SobolevSpace.Extension.GraphChart
