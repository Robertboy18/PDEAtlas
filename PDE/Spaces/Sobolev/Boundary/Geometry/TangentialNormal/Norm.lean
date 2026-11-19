/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Geometry.TangentialNormal

/-!
# Euclidean norm in tangential and normal coordinates

The coordinate split is equipped with the product topology, whose default norm is
not the Euclidean product norm. The squared-norm identity records the precise metric
relation needed when describing spheres as local graphs.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.HalfSpace

/-- Pythagoras for the tangential/normal coordinate split. -/
theorem norm_sq_eq_splitTangentialNormal {n : ℕ} (x : ℝ^(n + 1)) :
    ‖x‖ ^ 2 = ‖(splitTangentialNormal x).1‖ ^ 2 + (splitTangentialNormal x).2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc,
    EuclideanSpace.real_norm_sq_eq]
  simp

end SobolevSpace.Trace.HalfSpace
