/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean.SpaceTime

/-!
# Scalar space and time coordinates

For a single spatial variable, the product coordinates are ordinary real
pairs `(x, t)`. The equivalence `scalarSpaceTimeEquiv` combines the general spacetime split
with Mathlib's one-dimensional Euclidean equivalence. It lets scalar PDEs
reuse analysis stated on `ℝ × ℝ` while keeping time in coordinate zero of `ℝ^2`.
`pointPairEquiv` is the identification `x ↦ (x 0, x 1)` in the coordinate order. Both are
continuous linear equivalences, not isometries: `ℝ × ℝ` carries the sup norm.
-/

@[expose] public noncomputable section

namespace PDE.Common

/-- Reorder scalar Euclidean spacetime into space × time. -/
def scalarSpaceTimeEquiv : ℝ^2 ≃L[ℝ] ℝ × ℝ :=
  (spaceTimeContinuousLinearEquiv 1).trans
    ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ))

/-- The product coordinates are `(x, t)`, in that order. -/
@[simp] theorem scalarSpaceTimeEquiv_apply (z : ℝ^2) :
    scalarSpaceTimeEquiv z = (z 1, z 0) := by
  simp [scalarSpaceTimeEquiv, splitSpaceTime, spatialPart, time, Matrix.vecTail]

/-- The inverse puts time in Euclidean coordinate zero. -/
@[simp] theorem scalarSpaceTimeEquiv_symm_apply (z : ℝ × ℝ) :
    scalarSpaceTimeEquiv.symm z = !₂[z.2, z.1] := by
  apply scalarSpaceTimeEquiv.injective
  simp

/-- The plane as coordinate pairs, `x ↦ (x 0, x 1)`. -/
def pointPairEquiv : ℝ^2 ≃L[ℝ] ℝ × ℝ :=
  (EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)

@[simp] theorem pointPairEquiv_apply (x : ℝ^2) : pointPairEquiv x = (x 0, x 1) := by
  simp [pointPairEquiv]

@[simp] theorem pointPairEquiv_symm_apply (s z : ℝ) : pointPairEquiv.symm (s, z) = !₂[s, z] := by
  simp [pointPairEquiv]

end PDE.Common
