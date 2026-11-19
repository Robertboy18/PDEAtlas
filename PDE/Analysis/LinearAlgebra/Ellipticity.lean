/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.LinearAlgebra.EuclideanMatrix
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Matrix.Normed

/-!
# Ellipticity and matrix norm bounds

A symmetric matrix with a nonnegative quadratic lower bound is positive
semidefinite. Its elementwise norm bounds its trace by dimension times norm.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open scoped RealInnerProductSpace Matrix.Norms.Elementwise

variable {n : ℕ}

/-- Symmetry and a nonnegative ellipticity lower bound imply positive
semidefiniteness, with no coefficient differentiability assumption. -/
theorem posSemidef_of_elliptic {A : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : A.IsSymm) {α : ℝ} (hα : 0 ≤ α)
    (hell : ∀ v : ℝ^n, α * ‖v‖ ^ 2 ≤ ⟪v, A.toEuclideanLin v⟫) :
    A.PosSemidef := by
  apply Matrix.isPositive_toEuclideanLin_iff.mp
  refine ⟨Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (Matrix.isHermitian_iff_isSymm.mpr hsymm), ?_⟩
  intro v
  change 0 ≤ ⟪A.toEuclideanLin v, v⟫
  rw [real_inner_comm]
  exact (mul_nonneg hα (sq_nonneg _)).trans (hell v)

/-- A bound on the matrix norm controls its trace. -/
theorem trace_le_dim_mul_of_norm_le {A : Matrix (Fin n) (Fin n) ℝ}
    {M : ℝ} (hA : ‖A‖ ≤ M) : A.trace ≤ (n : ℝ) * M := by
  calc
    A.trace ≤ ∑ _ : Fin n, M := by
      apply Finset.sum_le_sum
      intro i _
      exact (le_abs_self _).trans
        ((norm_le_pi_norm (A i) i).trans ((norm_le_pi_norm A i).trans hA))
    _ = (n : ℝ) * M := by simp

end PDE.Analysis
