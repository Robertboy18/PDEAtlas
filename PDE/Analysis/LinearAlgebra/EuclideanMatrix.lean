/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.Matrix.Hermitian
public import PDE.Common.Euclidean

/-!
# Traces and quadratic forms of Euclidean matrices

For a square real matrix `A`, the trace of `Matrix.toEuclideanLin A` is the trace of `A`,
and `⟪v, A v⟫ = ∑ i, ∑ j, A i j * v i * v j`.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open scoped Matrix RealInnerProductSpace

variable {n : ℕ}

/-- The Euclidean linear map represented by a matrix has the same trace. -/
theorem trace_toEuclideanLin (A : Matrix (Fin n) (Fin n) ℝ) :
    LinearMap.trace ℝ (ℝ^n) A.toEuclideanLin = A.trace := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis,
    Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]

/-- The quadratic form of a Euclidean matrix is its coordinate contraction. -/
theorem inner_toEuclideanLin_self (A : Matrix (Fin n) (Fin n) ℝ) (v : ℝ^n) :
    ⟪v, A.toEuclideanLin v⟫ =
      ∑ i : Fin n, ∑ j : Fin n, A i j * v i * v j := by
  change (∑ i : Fin n, (A *ᵥ ⇑v) i * v i) = _
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end PDE.Analysis
