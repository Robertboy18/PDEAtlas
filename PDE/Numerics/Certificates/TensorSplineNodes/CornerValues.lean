/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.TensorSplineNodes.RowEnclosure

/-!
# The corner values of a tensor spline field on a cell of a row

The row evaluation stores, for every cell of a row, integer approximations `val e f k l` with
error bounds `err e f k l` of the scaled mixed derivatives of the cell polynomial at the four
corners (`rowCorners_sound`). When no knot of any mode lies inside the cell, the cell polynomial
and the field agree with all their mixed derivatives on the closed cell (`mixedDeriv_field_eq`),
so the corner data approximate the mixed derivatives of the field itself at the corners
(`abs_rowCorners_val_sub_le_field`): point values, much sharper than the cell enclosures
`lower`/`upper`.

## Main results

* `abs_rowCorners_val_sub_le_field`: under the checks of the evaluation and the separation of
  the cell from the knots, `val e f k l` approximates `2 ^ (pa + pr + pt) h₁ᵏ h₂ˡ ∂ₓᵏ ∂ᵧˡ F` of
  the unweighted field at the corner `(e, f)` within `err e f k l`, for `k, l ≤ n`.
-/

@[expose] public section

namespace CAS.Numerics.TensorSpline

open Finset Set

variable (ly : Layout)

/-- **The corner values of the field.** Under the checks of the evaluation and the separation of
the cell from the knots, `val e f k l` approximates `2 ^ (pa + pr + pt) h₁ᵏ h₂ˡ ∂ₓᵏ ∂ᵧˡ F` of the
unweighted field at the corner `(e, f)` within `err e f k l`, for `k, l ≤ n`. -/
theorem abs_rowCorners_val_sub_le_field {g : Grid ly.n} {L : ℕ} {lv : ℕ → Level}
    (hg : g.Sound L lv) (bd : Bounds) (xw : ℕ → ℕ → ℕ × ℕ) (yw : ℕ → ℕ × ℕ)
    (tables : ℕ → ℕ → Array ℕ) {nBlocks nCells q p : ℕ} (hblock : 0 < ly.block)
    (htab : tableCheck ly g L lv bd xw nBlocks nCells = true)
    (hterm : termCheck L lv bd = true) (hrow : rowCheck ly g L lv bd yw q = true)
    (hcoeff : ∀ m < L, ∀ t < (yw m).2, ∀ i < (lv m).rows,
      (coeffEntry ly lv m i ((yw m).1 + t)).natAbs ≤ bd.coeff)
    (htables : ∀ b < nBlocks, ∀ m < L, ∀ u < (xw b m).2,
      (tables b m).getD u 0 = xTable ly g lv m b ((xw b m).1 + u))
    (hp : p < nCells) (hpb : p / ly.block < nBlocks) (hX : g.X p < g.X (p + 1))
    (hY : g.Y q < g.Y (q + 1))
    (hsx : ∀ m < L, ∀ i < (lv m).rows, ∀ τ ∈ (lv m).xModes i,
      τ.Separated ly.n (lv m).xKnots (((g.X p : ℚ) / g.D : ℚ) : ℝ)
        (((g.X (p + 1) : ℚ) / g.D : ℚ) : ℝ))
    (hsy : ∀ m < L, ∀ j < (lv m).cols, ∀ τ ∈ (lv m).yModes j,
      τ.Separated ly.n (lv m).yKnots (((g.Y q : ℚ) / g.D : ℚ) : ℝ)
        (((g.Y (q + 1) : ℚ) / g.D : ℚ) : ℝ))
    (e f : Bool) {k l : ℕ} (hk : k ≤ ly.n) (hl : l ≤ ly.n) :
    |((rowCorners ly (rowEval ly g L lv bd xw yw tables nBlocks q) p).val e f k l : ℝ) -
      2 ^ (ly.pa + ly.pr + ly.pt) *
        (((((g.X (p + 1) : ℚ) / g.D : ℚ) : ℝ) - (((g.X p : ℚ) / g.D : ℚ) : ℝ)) ^ k *
          ((((g.Y (q + 1) : ℚ) / g.D : ℚ) : ℝ) - (((g.Y q : ℚ) / g.D : ℚ) : ℝ)) ^ l *
          mixedDeriv k l (field ly.n L lv (fun _ ↦ 1))
            (if e then (((g.X (p + 1) : ℚ) / g.D : ℚ) : ℝ) else (((g.X p : ℚ) / g.D : ℚ) : ℝ))
            (if f then (((g.Y (q + 1) : ℚ) / g.D : ℚ) : ℝ)
              else (((g.Y q : ℚ) / g.D : ℚ) : ℝ)))| ≤
      ((rowCorners ly (rowEval ly g L lv bd xw yw tables nBlocks q) p).err e f k l : ℝ) := by
  have hD : (0 : ℚ) < g.D := by exact_mod_cast hg.D_pos
  have hab : (((g.X p : ℚ) / g.D : ℚ) : ℝ) < (((g.X (p + 1) : ℚ) / g.D : ℚ) : ℝ) :=
    Rat.cast_lt.mpr (div_lt_div_of_pos_right (by exact_mod_cast hX) hD)
  have hcd : (((g.Y q : ℚ) / g.D : ℚ) : ℝ) < (((g.Y (q + 1) : ℚ) / g.D : ℚ) : ℝ) :=
    Rat.cast_lt.mpr (div_lt_div_of_pos_right (by exact_mod_cast hY) hD)
  have hxe : (if e then (((g.X (p + 1) : ℚ) / g.D : ℚ) : ℝ) else (((g.X p : ℚ) / g.D : ℚ) : ℝ)) ∈
      Icc (((g.X p : ℚ) / g.D : ℚ) : ℝ) (((g.X (p + 1) : ℚ) / g.D : ℚ) : ℝ) := by
    cases e
    · exact ⟨le_rfl, hab.le⟩
    · exact ⟨hab.le, le_rfl⟩
  have hyf : (if f then (((g.Y (q + 1) : ℚ) / g.D : ℚ) : ℝ) else (((g.Y q : ℚ) / g.D : ℚ) : ℝ)) ∈
      Icc (((g.Y q : ℚ) / g.D : ℚ) : ℝ) (((g.Y (q + 1) : ℚ) / g.D : ℚ) : ℝ) := by
    cases f
    · exact ⟨le_rfl, hcd.le⟩
    · exact ⟨hcd.le, le_rfl⟩
  have heq := mixedDeriv_field_eq (contDiff_const (c := (1 : ℝ))) hab hcd hsx hsy hk hl hxe hyf
  have h := rowCorners_sound ly hg bd xw yw tables hblock htab hterm hrow hcoeff htables hp hpb
    e f (k := k) (l := l) (by unfold Layout.ord; omega) (by unfold Layout.ord; omega)
  unfold scaledCellDeriv at h
  rw [heq]
  exact h

end CAS.Numerics.TensorSpline
