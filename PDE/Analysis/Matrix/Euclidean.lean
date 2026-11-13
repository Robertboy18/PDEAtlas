/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Matrix.Normed
public import PDE.Common.Euclidean

/-!
# Matrices as Euclidean vectors

Flattening a real matrix identifies its Frobenius norm with the Euclidean norm.
The continuous linear equivalence also uses the usual finite-product topology
on matrices, so differentiability and convexity transport without extra hypotheses.
-/

@[expose] public noncomputable section

namespace Matrix

variable {m n : ℕ}

/-- Row-major Euclidean coordinates of a real matrix, including empty matrices. -/
def euclideanEquiv : Matrix (Fin m) (Fin n) ℝ ≃L[ℝ] ℝ^(m * n) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun A ↦ WithLp.toLp 2 fun k ↦
        A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
      invFun := fun v i j ↦ v (finProdFinEquiv (i, j))
      left_inv := by intro A; funext i j; simp
      right_inv := by
        intro v
        apply PiLp.ext
        intro k
        change v (finProdFinEquiv (finProdFinEquiv.symm k)) = v k
        rw [Equiv.apply_symm_apply]
      map_add' := by intro A B; rfl
      map_smul' := by intro c A; rfl }

/-- Unflattening selects precisely the corresponding row and column. -/
@[simp]
theorem euclideanEquiv_symm_apply (v : ℝ^(m * n))
    (i : Fin m) (j : Fin n) :
    euclideanEquiv.symm v i j = v (finProdFinEquiv (i, j)) := rfl

/-- The squared Euclidean norm is the sum of the squares of all matrix entries. -/
theorem norm_euclideanEquiv_sq (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖euclideanEquiv A‖ ^ 2 = ∑ i, ∑ j, (A i j) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ k : Fin (m * n), (A (finProdFinEquiv.symm k).1
    (finProdFinEquiv.symm k).2) ^ 2) = _
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp [Fintype.sum_prod_type]

open scoped Matrix.Norms.Frobenius in
/-- Flattening preserves the Frobenius norm, including zero target dimension. -/
theorem norm_euclideanEquiv (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖euclideanEquiv A‖ = ‖A‖ := by
  rw [frobenius_norm_def]
  simp_rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [← norm_euclideanEquiv_sq, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]

end Matrix
