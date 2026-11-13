/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Boundary.Geometry.TangentialNormal

/-!
# The tangential inclusion

Adding a zero normal coordinate preserves Euclidean length. The same inclusion is used
for boundary restriction, surface measure, and differentiation along horizontal slices.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Trace.HalfSpace

variable {n : ℕ}

/-- Include a tangent vector by giving it zero normal component. -/
def tangentialEmbedding : ℝ^n →ₗᵢ[ℝ] ℝ^(n + 1) where
  toLinearMap := ((tangentialNormalContinuousLinearEquiv (n := n)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ (ℝ^n) ℝ)).toLinearMap
  norm_map' v := by
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_castSucc, joinTangentialNormal]

/-- A tangent vector has zero normal coordinate. -/
@[simp]
theorem tangentialEmbedding_apply (v : ℝ^n) :
    tangentialEmbedding v = joinTangentialNormal (v, 0) :=
  rfl

end SobolevSpace.Trace.HalfSpace
