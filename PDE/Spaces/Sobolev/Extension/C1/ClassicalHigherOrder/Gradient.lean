/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.C1.ClassicalHigherOrder.VectorValued
public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Gradient

/-!
# Extending the completed gradient across a C¹ boundary

Raw C² closure data give raw C¹ data for each completed gradient component.
The first-order vector extension theorem applies on a C¹ graph domain.
This extends the gradient as an independent vector field and requires no
C² flattening charts or ambient C² extension of the scalar field.
-/

@[expose] public noncomputable section

namespace SobolevSpace.ContDiffUpToBoundary

open Set

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {u : ℝ^n → ℝ}

/-- The completed gradient of raw C² data admits a C¹ extension on a raw
bounded C¹ graph domain. -/
theorem exists_contDiff_one_gradient_extension (hu : ContDiffUpToBoundary 2 u Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) :
    ∃ G : ℝ^n → ℝ^n, ContDiff ℝ 1 G ∧
      EqOn G (hu.of_le (show 1 ≤ 2 by omega)).completedGradient (closure Ω) :=
  exists_contDiff_succ_extension_vector 0
    (hu.contDiffUpToBoundary_completedGradient hopen)
    (hu.of_le (show 1 ≤ 2 by omega)).continuous_completedGradient.continuousOn
    hopen hbounded (Boundary.hasContDiffGraphBoundary_one_iff.mpr hgraph)

end SobolevSpace.ContDiffUpToBoundary
