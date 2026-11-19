/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.LinearAlgebra.EuclideanMatrix
public import PDE.Analysis.Geometry.EuclideanSplit
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Prepending a scalar block to a Euclidean matrix

Mathlib's block matrix is reindexed by `Fin (n + 1)`, with the scalar at index zero as in
the time-space convention.
Its trace and quadratic form split into their scalar and spatial parts.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open PDE.Common
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- The block matrix `diag(d,A)`, with the scalar block at coordinate zero. -/
def prependScalarBlock (d : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (Matrix.fromBlocks (fun _ _ : Fin 1 ↦ d) 0 0 A).submatrix
    (Fin.cases (Sum.inl 0) Sum.inr) (Fin.cases (Sum.inl 0) Sum.inr)

@[simp]
theorem prependScalarBlock_zero_zero (d : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    prependScalarBlock d A 0 0 = d := rfl

@[simp]
theorem prependScalarBlock_zero_succ (d : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    prependScalarBlock d A 0 j.succ = 0 := rfl

@[simp]
theorem prependScalarBlock_succ_zero (d : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    prependScalarBlock d A i.succ 0 = 0 := rfl

@[simp]
theorem prependScalarBlock_succ_succ (d : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    prependScalarBlock d A i.succ j.succ = A i j := rfl

/-- The trace gains the scalar block. -/
theorem trace_prependScalarBlock (d : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    (prependScalarBlock d A).trace = d + A.trace := by
  simp [Matrix.trace, Fin.sum_univ_succ]

/-- The quadratic form splits orthogonally. -/
theorem inner_prependScalarBlock (d : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (v : ℝ^(n + 1)) :
    ⟪v, (prependScalarBlock d A).toEuclideanLin v⟫ =
      d * (v 0) ^ 2 + ⟪spatialPart v, A.toEuclideanLin (spatialPart v)⟫ := by
  rw [inner_toEuclideanLin_self, inner_toEuclideanLin_self]
  simp [Fin.sum_univ_succ, pow_two, mul_assoc]

/-- Positive semidefiniteness of the two diagonal blocks gives that of the extension. -/
theorem posSemidef_prependScalarBlock {d : ℝ} (hd : 0 ≤ d)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) :
    (prependScalarBlock d A).PosSemidef := by
  have hscalar : Matrix.IsHermitian (fun _ _ : Fin 1 ↦ d) :=
    Matrix.IsHermitian.ext fun _ _ ↦ star_trivial d
  have hsymm : (prependScalarBlock d A).IsHermitian :=
    (hscalar.fromBlocks (by simp) hA.isHermitian).submatrix _
  apply Matrix.isPositive_toEuclideanLin_iff.mp
  refine ⟨Matrix.isSymmetric_toEuclideanLin_iff.mpr hsymm, ?_⟩
  intro v
  have hpos := (Matrix.isPositive_toEuclideanLin_iff.mpr hA).re_inner_nonneg_right
    (spatialPart v)
  change 0 ≤ ⟪(prependScalarBlock d A).toEuclideanLin v, v⟫
  rw [real_inner_comm, inner_prependScalarBlock]
  exact add_nonneg (mul_nonneg hd (sq_nonneg _)) hpos

/-- The smaller ellipticity bound of the two blocks controls the full norm. -/
theorem elliptic_prependScalarBlock
    {d α : ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ v : ℝ^n, α * ‖v‖ ^ 2 ≤ ⟪v, A.toEuclideanLin v⟫)
    (v : ℝ^(n + 1)) :
    min d α * ‖v‖ ^ 2 ≤ ⟪v, (prependScalarBlock d A).toEuclideanLin v⟫ := by
  rw [norm_sq_eq_time_add_spatial, inner_prependScalarBlock, mul_add]
  exact add_le_add
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _))
    ((mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans (hA _))

end PDE.Analysis
