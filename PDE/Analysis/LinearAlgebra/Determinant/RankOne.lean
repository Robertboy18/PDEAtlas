/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Determinant of a rank-one perturbation of the identity

The determinant of `x ↦ x + ℓ(x)v` is `1 + ℓ(v)`. In particular a shear
parallel to the kernel of its defining covector has determinant one.
-/

@[expose] public section

namespace LinearMap

variable {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The determinant formula for a rank-one perturbation of the identity,
including the zero-dimensional case. -/
theorem det_id_add_smulRight (ℓ : E →ₗ[𝕜] 𝕜) (v : E) :
    (LinearMap.id + ℓ.smulRight v).det = 1 + ℓ v := by
  classical
  let b := Module.finBasis 𝕜 E
  rw [← LinearMap.det_toMatrix b, map_add, LinearMap.toMatrix_id,
    LinearMap.toMatrix_smulRight]
  have hmatrix : Matrix.vecMulVec (b.repr v) (ℓ ∘ b) =
      Matrix.replicateCol Unit (b.repr v) * Matrix.replicateRow Unit (ℓ ∘ b) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.vecMulVec_apply]
  rw [hmatrix, Matrix.det_one_add_replicateCol_mul_replicateRow]
  congr 1
  have h := congrArg ℓ (b.sum_repr v)
  simpa only [dotProduct, Function.comp_apply, map_sum, map_smul, smul_eq_mul,
    mul_comm] using h

/-- A rank-one shear parallel to the covector kernel preserves determinant. -/
theorem det_id_add_smulRight_eq_one {ℓ : E →ₗ[𝕜] 𝕜} {v : E} (h : ℓ v = 0) :
    (LinearMap.id + ℓ.smulRight v).det = 1 := by
  rw [det_id_add_smulRight, h, add_zero]

end LinearMap
