/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.LinearAlgebra.Determinant

/-!
# Block elimination for determinants of linear maps

Triangular block maps have determinant equal to the product of their diagonal
determinants. Subtracting a multiple of the first block row from the second
preserves that determinant, without invertibility of either diagonal block.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

variable {R E F : Type*} [CommRing R]
    [AddCommGroup E] [Module R E] [Module.Free R E] [Module.Finite R E]
    [AddCommGroup F] [Module R F] [Module.Free R F] [Module.Finite R F]

/-- The determinant of an upper triangular block map is the product of its
diagonal determinants, also for zero-dimensional factors. -/
theorem det_prod_coprod_snd (A : E →ₗ[R] E) (B : F →ₗ[R] E) (D : F →ₗ[R] F) :
    ((A.coprod B).prod (D.comp (LinearMap.snd R E F))).det = A.det * D.det := by
  classical
  let e := Module.Free.chooseBasis R E
  let f := Module.Free.chooseBasis R F
  have hmatrix : LinearMap.toMatrix (e.prod f) (e.prod f)
      ((A.coprod B).prod (D.comp (LinearMap.snd R E F))) =
      Matrix.fromBlocks (LinearMap.toMatrix e e A) (LinearMap.toMatrix f e B)
        0 (LinearMap.toMatrix f f D) := by
    ext (i | i) (j | j) <;> simp [LinearMap.toMatrix]
  rw [← LinearMap.det_toMatrix (e.prod f), hmatrix, Matrix.det_fromBlocks_zero₂₁,
    LinearMap.det_toMatrix, LinearMap.det_toMatrix]

/-- The analogous formula for a lower triangular block map. -/
theorem det_prod_fst_coprod (A : E →ₗ[R] E) (C : E →ₗ[R] F) (D : F →ₗ[R] F) :
    ((A.comp (LinearMap.fst R E F)).prod (C.coprod D)).det = A.det * D.det := by
  classical
  let e := Module.Free.chooseBasis R E
  let f := Module.Free.chooseBasis R F
  have hmatrix : LinearMap.toMatrix (e.prod f) (e.prod f)
      ((A.comp (LinearMap.fst R E F)).prod (C.coprod D)) =
      Matrix.fromBlocks (LinearMap.toMatrix e e A) 0
        (LinearMap.toMatrix e f C) (LinearMap.toMatrix f f D) := by
    ext (i | i) (j | j) <;> simp [LinearMap.toMatrix]
  rw [← LinearMap.det_toMatrix (e.prod f), hmatrix, Matrix.det_fromBlocks_zero₁₂,
    LinearMap.det_toMatrix, LinearMap.det_toMatrix]

/-- Eliminating a block row introduces no inverse and therefore remains valid
when the spatial Jacobian is singular. -/
theorem det_prod_sub_comp (A : E × F →ₗ[R] E) (C : E →ₗ[R] F) (D : F →ₗ[R] F) :
    (A.prod (D.comp (LinearMap.snd R E F) - C.comp A)).det =
      (A.comp (LinearMap.inl R E F)).det * D.det := by
  let S := (LinearMap.id : E →ₗ[R] E).comp (LinearMap.fst R E F) |>.prod
    (C.coprod (LinearMap.id : F →ₗ[R] F))
  have hS : S.det = 1 := by
    rw [det_prod_fst_coprod]
    simp
  have hcomp : S.comp (A.prod (D.comp (LinearMap.snd R E F) - C.comp A)) =
      ((A.comp (LinearMap.inl R E F)).coprod
        (A.comp (LinearMap.inr R E F))).prod (D.comp (LinearMap.snd R E F)) := by
    ext p <;> simp [S]
  have h := congrArg LinearMap.det hcomp
  rw [LinearMap.det_comp, hS, one_mul, det_prod_coprod_snd] at h
  exact h

end PDE.Analysis
