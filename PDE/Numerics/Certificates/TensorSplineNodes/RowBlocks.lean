/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.TensorSplineNodes.RowEnclosure

/-!
# Rows of cells evaluated block by block

The evaluation `rowEval` of a cell row computes each block of cells from the tangential table of
that block and from data shared by the whole row (`rowPass`); no block reads the table of another
block. So two evaluations whose tables agree on a block agree on that block
(`rowEval_getD_congr`), and the corner data of the cells of the block agree
(`rowCorners_congr`). A row can thus be evaluated with the tangential tables of a range of blocks
only, for the cells of that range.

## Main results

* `rowEval_getD_congr`: evaluations of a row with tangential tables that agree on the block `b`
  agree on `b`.
* `rowCorners_congr`: the corner data of the cell `p` depend on the row only through the block
  of `p`.
-/

@[expose] public section

namespace CAS.Numerics.TensorSpline

variable (ly : Layout) (g : Grid ly.n) (L : ℕ) (lv : ℕ → Level) (bd : Bounds)

/-- Evaluations of a row with tangential tables that agree on the block `b` agree on `b`. -/
theorem rowEval_getD_congr (xw : ℕ → ℕ → ℕ × ℕ) (yw : ℕ → ℕ × ℕ) {T₁ T₂ : ℕ → ℕ → Array ℕ}
    (nBlocks q : ℕ) {b : ℕ} (h : T₁ b = T₂ b) (i : ℕ) :
    ((rowEval ly g L lv bd xw yw T₁ nBlocks q).getD i #[]).getD b (0, 0) =
      ((rowEval ly g L lv bd xw yw T₂ nBlocks q).getD i #[]).getD b (0, 0) := by
  simp only [rowEval]
  by_cases hi : i < 2 * ly.ord
  · rw [getD_toArray_map_range _ _ _ hi, getD_toArray_map_range _ _ _ hi]
    simp only [rowPass]
    by_cases hb : b < nBlocks
    · rw [getD_toArray_map_range _ _ _ hb, getD_toArray_map_range _ _ _ hb, h]
    · simp [Array.getD_eq_getD_getElem?, hb]
  · simp [Array.getD_eq_getD_getElem?, hi]

/-- The corner data of the cell `p` depend on the row only through the block of `p`. -/
theorem rowCorners_congr {R₁ R₂ : Array (Array (ℕ × ℕ))} {p : ℕ}
    (h : ∀ i, (R₁.getD i #[]).getD (p / ly.block) (0, 0) =
      (R₂.getD i #[]).getD (p / ly.block) (0, 0)) :
    rowCorners ly R₁ p = rowCorners ly R₂ p := by
  unfold rowCorners
  simp only [h]

end CAS.Numerics.TensorSpline
