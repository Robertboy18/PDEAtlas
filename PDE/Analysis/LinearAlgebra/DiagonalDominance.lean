/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-!
# Exact solutions of strictly diagonally dominant systems

Mathlib's determinant criterion `det_ne_zero_of_sum_row_lt_diag` and the
invertible-matrix lemmas give a unique solution for each right-hand side.
-/

@[expose] public section

namespace PDE.Analysis

/-- If `∑_{j ≠ i} |A i j| < |A i i|` for every row `i`, then `A x = b` has a unique solution
for every right-hand side `b`. -/
theorem existsUnique_mulVec_of_strict_row_dominance
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hdominant : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ < ‖A i i‖) (b : ι → ℝ) :
    ∃! x : ι → ℝ, A.mulVec x = b := by
  have hdet : A.det ≠ 0 := det_ne_zero_of_sum_row_lt_diag hdominant
  have hunit : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨x, hx⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hunit b
  exact ⟨x, hx, fun y hy ↦ Matrix.mulVec_injective_of_det_ne_zero hdet (hy.trans hx.symm)⟩

end PDE.Analysis
