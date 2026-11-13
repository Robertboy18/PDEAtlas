/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.TensorSplineNodes.CellEnclosure
public import PDE.Numerics.Certificates.TensorSplineNodes.Evaluation

/-!
# Cell enclosures of a whole cell row

`rowEval` runs the checked evaluation of `Evaluation.lean` on the cell row `q` for every normal
order `l < n + 2` and end `f`, block by block, and records for every block the merged row and its
error. `rowCorners` reads the corner data of the cell `p` from it, and `rowCorners_sound` proves,
under the checks of the evaluation, that these data approximate `2 ^ (pa + pr + pt)` times the
scaled corner derivatives of the cell function within the recorded errors. With
`CellCorners.mem_Icc_of_corners` the cell bounds `CellCorners.lower`, `CellCorners.upper` then
enclose the scaled derivatives on the whole cell (`mem_Icc_rowCorners`).

## Main definitions

* `rowEval`: the checked evaluation of a cell row for all normal orders and both ends.
* `rowCorners`: the corner data of one cell of the row, read from `rowEval`.
* `tableBlockCheck`: the table check of one block, whose conjunction is `tableCheck`.

## Main results

* `rowCorners_sound`: under the checks, `rowCorners` approximates `2 ^ (pa + pr + pt)` times the
  scaled corner derivatives of the cell function within the recorded errors.
* `mem_Icc_rowCorners`: under the checks, `lower` and `upper` of the corner data enclose the
  scaled mixed derivatives of order `(k, l)`, `k, l ≤ n + 1`, on the whole cell.
* `mem_Icc_rowCorners_field`: with no knot inside the cell, the enclosures hold for the mixed
  derivatives of order `k, l ≤ n` of the field itself on the closed cell.
* `tableCheck_eq_all`: `tableCheck` is the conjunction of `tableBlockCheck` over the blocks.
* `rowCheck_congr`: `rowCheck` depends on the levels only through their normal modes and numbers
  of columns.
-/

@[expose] public section

namespace CAS.Numerics.TensorSpline

open Finset Set

variable (ly : Layout) (g : Grid ly.n) (L : ℕ) (lv : ℕ → Level) (bd : Bounds)

/-- The window columns of the coefficients of every level for the normal window `yw`. -/
def rowColumns (yw : ℕ → ℕ × ℕ) : Array (Array ℕ) :=
  ((List.range L).map fun m ↦
    ((List.range (yw m).2).map fun t ↦ column ly lv m ((yw m).1 + t)).toArray).toArray

/-- The column `j` of the level `m` from the cached window columns. -/
def rowColumn (yw : ℕ → ℕ × ℕ) (cA : Array (Array ℕ)) (m j : ℕ) : ℕ :=
  (cA.getD m #[]).getD (j - (yw m).1) 0

/-- The slots of the cached window columns. -/
def rowColumnSlots (yw : ℕ → ℕ × ℕ) (cA : Array (Array ℕ)) : Array (Array (Array ℕ)) :=
  ((List.range L).map fun m ↦ ((List.range (yw m).2).map fun t ↦
    (slotList ly.w₁ ly.depth (lv m).rows (rowColumn yw cA m ((yw m).1 + t))).toArray).toArray
    ).toArray

/-- One pass of the evaluation of the cell row `q` for the normal order `l` and end `f`: for
every block below `nBlocks` the merged row and its error, from the tangential tables
`tables b m` and their scaled sums. -/
def rowPass (xw : ℕ → ℕ → ℕ × ℕ) (yw : ℕ → ℕ × ℕ) (tables : ℕ → ℕ → Array ℕ)
    (nBlocks q : ℕ) (cA : Array (Array ℕ)) (cS : Array (Array (Array ℕ))) (l : ℕ) (f : Bool) :
    Array (ℕ × ℕ) :=
  let coefs : Array (Array ℕ) := ((List.range L).map fun m ↦ (slotList ly.w₁ ly.depth (lv m).rows
    (rowStageOne ly g lv (rowColumn yw cA m) m q l f (yw m))).toArray).toArray
  let Rs : Array (Array ℕ) := ((List.range L).map fun m ↦
    ((List.range (yw m).2).map (rowJets ly g lv m q l f (yw m).1)).toArray).toArray
  let eOnes : Array (Array ℕ) := ((List.range L).map fun m ↦
    stageOneErrors ly ((ly.n + 3) * bd.yTerms) (lv m).rows (yw m).2 (cS.getD m #[])
      (fun t ↦ (Rs.getD m #[]).getD t 0)).toArray
  ((List.range nBlocks).map fun b ↦
    (blockEval ly L (biasRow ly.w₂ ly.slots) (fun m ↦ coefs.getD m #[]) (tables b)
        (fun m ↦ Nat.mul (slotBias ly.w₁) (natSum (xw b m).2 fun u ↦ (tables b m).getD u 0))
        (xw b),
      blockError ly L bd (fun m ↦ coefs.getD m #[]) (fun m ↦ eOnes.getD m #[]) (xw b))).toArray

/-- The evaluation of the cell row `q`: the passes for all normal orders `l < n + 2` and both
ends, the pass `(l, f)` at index `2 l + f`. -/
def rowEval (xw : ℕ → ℕ → ℕ × ℕ) (yw : ℕ → ℕ × ℕ) (tables : ℕ → ℕ → Array ℕ)
    (nBlocks q : ℕ) : Array (Array (ℕ × ℕ)) :=
  let cA := rowColumns ly L lv yw
  let cS := rowColumnSlots ly L lv yw cA
  ((List.range (2 * ly.ord)).map fun i ↦
    rowPass ly g L lv bd xw yw tables nBlocks q cA cS (i / 2) (i % 2 == 1)).toArray

/-- The slot of the derivative of order `k` at the end `e` of the cell `c` of a block. -/
def slotIndex (c : ℕ) (e : Bool) (k : ℕ) : ℕ :=
  c * (2 * ly.ord) + (if e then ly.ord else 0) + k

/-- The corner data of the cell `p` of a row from its evaluation `R`. -/
def rowCorners (R : Array (Array (ℕ × ℕ))) (p : ℕ) : CellCorners where
  val e f k l := signedSlot ly.w₂ (slotIndex ly (p % ly.block) e k)
    ((R.getD (2 * l + if f then 1 else 0) #[]).getD (p / ly.block) (0, 0)).1
  err _ f _ l := ((R.getD (2 * l + if f then 1 else 0) #[]).getD (p / ly.block) (0, 0)).2

/-- For an order `k < ord` the slot of the derivative of order `k` at an end of the cell `c` belongs
to the cell `c`. -/
theorem cellOf_slotIndex (c : ℕ) (e : Bool) {k : ℕ}
    (hk : k < ly.ord) : ly.cellOf (slotIndex ly c e k) = c := by
  unfold Layout.cellOf slotIndex
  have : (if e then ly.ord else 0) + k < 2 * ly.ord := by split_ifs <;> omega
  rw [show c * (2 * ly.ord) + (if e then ly.ord else 0) + k =
    (if e then ly.ord else 0) + k + 2 * ly.ord * c by ring]
  rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt this, zero_add]

/-- For `k < ord` the slot of the derivative of order `k` at an end of a cell holds the order
`k`. -/
theorem orderOf_slotIndex (c : ℕ) (e : Bool) {k : ℕ} (hk : k < ly.ord) :
    ly.orderOf (slotIndex ly c e k) = k := by
  unfold Layout.orderOf slotIndex
  cases e
  · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
    rw [show c * (2 * ly.ord) + k = k + ly.ord * (2 * c) by ring, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hk]
  · simp only [↓reduceIte]
    rw [show c * (2 * ly.ord) + ly.ord + k = k + ly.ord * (2 * c + 1) by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]

/-- For `k < ord` the slot of the derivative at the end `e` of a cell holds the end `e`. -/
theorem cornerOf_slotIndex (c : ℕ) (e : Bool) {k : ℕ} (hk : k < ly.ord) :
    ly.cornerOf (slotIndex ly c e k) = e := by
  unfold Layout.cornerOf slotIndex
  cases e
  · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
    rw [show c * (2 * ly.ord) + k = k + ly.ord * (2 * c) by ring,
      Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hk]
    simp
  · simp only [↓reduceIte]
    rw [show c * (2 * ly.ord) + ly.ord + k = k + ly.ord * (2 * c + 1) by ring,
      Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hk]
    simp [Nat.add_mod]

/-- The slots of the cells `c < block` and orders `k < ord` lie below the number of slots of a
block. -/
theorem slotIndex_lt {c : ℕ} (hc : c < ly.block) (e : Bool) {k : ℕ} (hk : k < ly.ord) :
    slotIndex ly c e k < ly.slots := by
  unfold slotIndex Layout.slots
  have : (if e then ly.ord else 0) + k < 2 * ly.ord := by split_ifs <;> omega
  nlinarith

/-- For `l < ord` the entry `2 l + f` of the row evaluation is the pass of normal order `l` and end
`f`. -/
theorem getD_rowEval (xw : ℕ → ℕ → ℕ × ℕ) (yw : ℕ → ℕ × ℕ) (tables : ℕ → ℕ → Array ℕ)
    (nBlocks q : ℕ) {l : ℕ} (hl : l < ly.ord) (f : Bool) (d : Array (ℕ × ℕ)) :
    (rowEval ly g L lv bd xw yw tables nBlocks q).getD (2 * l + if f then 1 else 0) d =
      rowPass ly g L lv bd xw yw tables nBlocks q (rowColumns ly L lv yw)
        (rowColumnSlots ly L lv yw (rowColumns ly L lv yw)) l f := by
  unfold rowEval
  rw [getD_toArray_map_range _ _ _ (by split <;> omega)]
  congr 1
  · split <;> omega
  · cases f <;> simp [Nat.add_mod]

/-- **Soundness of the corner data of a row.** Under the checks of the evaluation, the corner data
`rowCorners` of the cell `p` of the row `q` approximate `2 ^ (pa + pr + pt)` times the scaled
mixed derivatives `(x_{p+1} - x_p)ᵏ (y_{q+1} - y_q)ˡ ∂ₓᵏ ∂ᵧˡ` of the unweighted cell function at
the corners, within the recorded errors, for all orders `k, l < n + 2`. -/
theorem rowCorners_sound {g : Grid ly.n} {L : ℕ} {lv : ℕ → Level} (hg : g.Sound L lv)
    (bd : Bounds) (xw : ℕ → ℕ → ℕ × ℕ) (yw : ℕ → ℕ × ℕ) (tables : ℕ → ℕ → Array ℕ)
    {nBlocks nCells q p : ℕ} (hblock : 0 < ly.block)
    (htab : tableCheck ly g L lv bd xw nBlocks nCells = true)
    (hterm : termCheck L lv bd = true) (hrow : rowCheck ly g L lv bd yw q = true)
    (hcoeff : ∀ m < L, ∀ t < (yw m).2, ∀ i < (lv m).rows,
      (coeffEntry ly lv m i ((yw m).1 + t)).natAbs ≤ bd.coeff)
    (htables : ∀ b < nBlocks, ∀ m < L, ∀ u < (xw b m).2,
      (tables b m).getD u 0 = xTable ly g lv m b ((xw b m).1 + u))
    (hp : p < nCells) (hpb : p / ly.block < nBlocks) (e f : Bool) {k l : ℕ} (hk : k < ly.ord)
    (hl : l < ly.ord) :
    |((rowCorners ly (rowEval ly g L lv bd xw yw tables nBlocks q) p).val e f k l : ℝ) -
      scaledCellDeriv ly.n L lv (2 ^ (ly.pa + ly.pr + ly.pt))
        (((g.X p : ℚ) / g.D : ℚ) : ℝ) (((g.X (p + 1) : ℚ) / g.D : ℚ) : ℝ)
        (((g.Y q : ℚ) / g.D : ℚ) : ℝ) (((g.Y (q + 1) : ℚ) / g.D : ℚ) : ℝ) k l
        (if e then (((g.X (p + 1) : ℚ) / g.D : ℚ) : ℝ) else (((g.X p : ℚ) / g.D : ℚ) : ℝ))
        (if f then (((g.Y (q + 1) : ℚ) / g.D : ℚ) : ℝ) else (((g.Y q : ℚ) / g.D : ℚ) : ℝ))| ≤
      ((rowCorners ly (rowEval ly g L lv bd xw yw tables nBlocks q) p).err e f k l : ℝ) := by
  set b := p / ly.block
  set c := p % ly.block
  have hc : c < ly.block := Nat.mod_lt _ hblock
  have hpbc : b * ly.block + c = p := by
    simp only [b, c]; rw [mul_comm]; exact Nat.div_add_mod p ly.block
  set s := slotIndex ly c e k
  have hs : s < ly.slots := slotIndex_lt ly hc e hk
  have hcell : ly.cellOf s = c := cellOf_slotIndex ly c e hk
  have hord : ly.orderOf s = k := orderOf_slotIndex ly c e hk
  have hcorner : ly.cornerOf s = e := cornerOf_slotIndex ly c e hk
  set cA := rowColumns ly L lv yw
  set cS := rowColumnSlots ly L lv yw cA
  have hcols : ∀ m < L, ∀ t < (yw m).2, rowColumn yw cA m ((yw m).1 + t) =
      column ly lv m ((yw m).1 + t) := by
    intro m hm t ht
    unfold rowColumn
    simp only [cA, rowColumns]
    rw [getD_toArray_map_range _ _ _ hm, Nat.add_sub_cancel_left, getD_toArray_map_range _ _ _ ht]
  set coefs : Array (Array ℕ) := ((List.range L).map fun m ↦ (slotList ly.w₁ ly.depth (lv m).rows
    (rowStageOne ly g lv (rowColumn yw cA m) m q l f (yw m))).toArray).toArray
  set Rs : Array (Array ℕ) := ((List.range L).map fun m ↦
    ((List.range (yw m).2).map (rowJets ly g lv m q l f (yw m).1)).toArray).toArray
  set eOnes : Array (Array ℕ) := ((List.range L).map fun m ↦
    stageOneErrors ly ((ly.n + 3) * bd.yTerms) (lv m).rows (yw m).2 (cS.getD m #[])
      (fun t ↦ (Rs.getD m #[]).getD t 0)).toArray
  have hpass : ((rowEval ly g L lv bd xw yw tables nBlocks q).getD
      (2 * l + if f then 1 else 0) #[]).getD b (0, 0) =
      (blockEval ly L (biasRow ly.w₂ ly.slots) (fun m ↦ coefs.getD m #[]) (tables b)
        (fun m ↦ Nat.mul (slotBias ly.w₁) (natSum (xw b m).2 fun u ↦ (tables b m).getD u 0))
        (xw b),
      blockError ly L bd (fun m ↦ coefs.getD m #[]) (fun m ↦ eOnes.getD m #[]) (xw b)) := by
    rw [getD_rowEval ly g L lv bd xw yw tables nBlocks q hl f]
    unfold rowPass
    exact getD_toArray_map_range _ _ _ hpb
  have hsound := abs_signedSlot_blockEval_sub_le ly hg bd xw yw f htab hterm hrow hpb hl hcoeff
    (rowColumn yw cA) hcols (fun m ↦ coefs.getD m #[]) (tables b)
    (fun m ↦ Nat.mul (slotBias ly.w₁) (natSum (xw b m).2 fun u ↦ (tables b m).getD u 0))
    (fun m hm ↦ by simp only [coefs]; rw [getD_toArray_map_range _ _ _ hm])
    (fun m hm u hu ↦ htables b hpb m hm u hu) (fun m _ ↦ rfl) hs
    (by rw [hcell, hpbc]; exact hp)
  rw [cellRowError_eq_blockError (g := g) (L := L) (lv := lv) (q := q) (l := l) (f := f) ly bd
    (xw b) yw (fun m hm ↦ (tableCheck_spec htab hpb hm).1) (rowColumn yw cA)
    (fun m ↦ coefs.getD m #[]) (fun m ↦ eOnes.getD m #[]) (fun m ↦ cS.getD m #[])
    (fun m t ↦ (Rs.getD m #[]).getD t 0)
    (fun m hm ↦ by simp only [coefs]; rw [getD_toArray_map_range _ _ _ hm])
    (fun m hm ↦ by simp only [cS, rowColumnSlots]; rw [getD_toArray_map_range _ _ _ hm])
    (fun m hm t ht ↦ by
      simp only [Rs]; rw [getD_toArray_map_range _ _ _ hm, getD_toArray_map_range _ _ _ ht])
    (fun m hm ↦ by simp only [eOnes]; rw [getD_toArray_map_range _ _ _ hm])] at hsound
  rw [hcell, hord, hcorner, hpbc] at hsound
  unfold rowCorners scaledCellDeriv
  simp only
  rw [hpass]
  exact hsound

/-- **Enclosures of the cell function on a cell of a row.** Under the checks of the evaluation,
`lower` and `upper` of the corner data of the cell `p` of the row `q` enclose
`2 ^ (pa + pr + pt)` times the scaled mixed derivative of order `(k, l)`, `k, l ≤ n + 1`, of the
unweighted cell function on the whole closed cell. -/
theorem mem_Icc_rowCorners {g : Grid ly.n} {L : ℕ} {lv : ℕ → Level} (hg : g.Sound L lv)
    (bd : Bounds) (xw : ℕ → ℕ → ℕ × ℕ) (yw : ℕ → ℕ × ℕ) (tables : ℕ → ℕ → Array ℕ)
    {nBlocks nCells q p : ℕ} (hblock : 0 < ly.block)
    (htab : tableCheck ly g L lv bd xw nBlocks nCells = true)
    (hterm : termCheck L lv bd = true) (hrow : rowCheck ly g L lv bd yw q = true)
    (hcoeff : ∀ m < L, ∀ t < (yw m).2, ∀ i < (lv m).rows,
      (coeffEntry ly lv m i ((yw m).1 + t)).natAbs ≤ bd.coeff)
    (htables : ∀ b < nBlocks, ∀ m < L, ∀ u < (xw b m).2,
      (tables b m).getD u 0 = xTable ly g lv m b ((xw b m).1 + u))
    (hp : p < nCells) (hpb : p / ly.block < nBlocks) (hX : g.X p < g.X (p + 1))
    (hY : g.Y q < g.Y (q + 1)) {k l : ℕ} (hk : k ≤ ly.n + 1) (hl : l ≤ ly.n + 1) {x y : ℝ}
    (hx : x ∈ Icc (((g.X p : ℚ) / g.D : ℚ) : ℝ) (((g.X (p + 1) : ℚ) / g.D : ℚ) : ℝ))
    (hy : y ∈ Icc (((g.Y q : ℚ) / g.D : ℚ) : ℝ) (((g.Y (q + 1) : ℚ) / g.D : ℚ) : ℝ)) :
    (((rowCorners ly (rowEval ly g L lv bd xw yw tables nBlocks q) p).lower (ly.n + 1) k l : ℤ) :
        ℝ) ≤ scaledCellDeriv ly.n L lv (2 ^ (ly.pa + ly.pr + ly.pt))
          (((g.X p : ℚ) / g.D : ℚ) : ℝ) (((g.X (p + 1) : ℚ) / g.D : ℚ) : ℝ)
          (((g.Y q : ℚ) / g.D : ℚ) : ℝ) (((g.Y (q + 1) : ℚ) / g.D : ℚ) : ℝ) k l x y ∧
      scaledCellDeriv ly.n L lv (2 ^ (ly.pa + ly.pr + ly.pt))
          (((g.X p : ℚ) / g.D : ℚ) : ℝ) (((g.X (p + 1) : ℚ) / g.D : ℚ) : ℝ)
          (((g.Y q : ℚ) / g.D : ℚ) : ℝ) (((g.Y (q + 1) : ℚ) / g.D : ℚ) : ℝ) k l x y ≤
        (((rowCorners ly (rowEval ly g L lv bd xw yw tables nBlocks q) p).upper (ly.n + 1) k l :
          ℤ) : ℝ) := by
  have hD : (0 : ℚ) < g.D := by exact_mod_cast hg.D_pos
  have hX' : ((g.X p : ℚ) / g.D : ℚ) < ((g.X (p + 1) : ℚ) / g.D : ℚ) :=
    div_lt_div_of_pos_right (by exact_mod_cast hX) hD
  have hY' : ((g.Y q : ℚ) / g.D : ℚ) < ((g.Y (q + 1) : ℚ) / g.D : ℚ) :=
    div_lt_div_of_pos_right (by exact_mod_cast hY) hD
  have hab : (((g.X p : ℚ) / g.D : ℚ) : ℝ) < (((g.X (p + 1) : ℚ) / g.D : ℚ) : ℝ) :=
    Rat.cast_lt.mpr hX'
  have hcd : (((g.Y q : ℚ) / g.D : ℚ) : ℝ) < (((g.Y (q + 1) : ℚ) / g.D : ℚ) : ℝ) :=
    Rat.cast_lt.mpr hY'
  refine CellCorners.mem_Icc_of_corners
    (G := scaledCellDeriv ly.n L lv (2 ^ (ly.pa + ly.pr + ly.pt))
      (((g.X p : ℚ) / g.D : ℚ) : ℝ) (((g.X (p + 1) : ℚ) / g.D : ℚ) : ℝ)
      (((g.Y q : ℚ) / g.D : ℚ) : ℝ) (((g.Y (q + 1) : ℚ) / g.D : ℚ) : ℝ))
    (fun k l _ _ c₀ B M₁ M₂ hc h₁ h₂ x hx y hy ↦
      abs_scaledCellDeriv_sub_le ly.n L lv hab hcd hc h₁ h₂ hx hy)
    (fun k l hkl x _ y _ ↦ by
      unfold scaledCellDeriv
      rw [mixedDeriv_cellField_eq_zero ly.n L lv _ _ _ _ (by omega) x y]
      ring)
    (fun e f k l hk hl ↦ rowCorners_sound ly hg bd xw yw tables hblock htab hterm hrow hcoeff
      htables hp hpb e f (by unfold Layout.ord; omega) (by unfold Layout.ord; omega))
    hk hl hx hy

/-- **Enclosures of the field on a cell of a row.** When in addition no knot of any mode lies inside
the cell, the enclosures hold for the mixed derivatives of order `(k, l)`, `k, l ≤ n`, of the
unweighted field itself on the closed cell. -/
theorem mem_Icc_rowCorners_field {g : Grid ly.n} {L : ℕ} {lv : ℕ → Level} (hg : g.Sound L lv)
    (bd : Bounds) (xw : ℕ → ℕ → ℕ × ℕ) (yw : ℕ → ℕ × ℕ) (tables : ℕ → ℕ → Array ℕ)
    {nBlocks nCells q p : ℕ} (hblock : 0 < ly.block)
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
    {k l : ℕ} (hk : k ≤ ly.n) (hl : l ≤ ly.n) {x y : ℝ}
    (hx : x ∈ Icc (((g.X p : ℚ) / g.D : ℚ) : ℝ) (((g.X (p + 1) : ℚ) / g.D : ℚ) : ℝ))
    (hy : y ∈ Icc (((g.Y q : ℚ) / g.D : ℚ) : ℝ) (((g.Y (q + 1) : ℚ) / g.D : ℚ) : ℝ)) :
    (((rowCorners ly (rowEval ly g L lv bd xw yw tables nBlocks q) p).lower (ly.n + 1) k l : ℤ) :
        ℝ) ≤ 2 ^ (ly.pa + ly.pr + ly.pt) *
          (((((g.X (p + 1) : ℚ) / g.D : ℚ) : ℝ) - (((g.X p : ℚ) / g.D : ℚ) : ℝ)) ^ k *
            ((((g.Y (q + 1) : ℚ) / g.D : ℚ) : ℝ) - (((g.Y q : ℚ) / g.D : ℚ) : ℝ)) ^ l *
            mixedDeriv k l (field ly.n L lv (fun _ ↦ 1)) x y) ∧
      2 ^ (ly.pa + ly.pr + ly.pt) *
          (((((g.X (p + 1) : ℚ) / g.D : ℚ) : ℝ) - (((g.X p : ℚ) / g.D : ℚ) : ℝ)) ^ k *
            ((((g.Y (q + 1) : ℚ) / g.D : ℚ) : ℝ) - (((g.Y q : ℚ) / g.D : ℚ) : ℝ)) ^ l *
            mixedDeriv k l (field ly.n L lv (fun _ ↦ 1)) x y) ≤
        (((rowCorners ly (rowEval ly g L lv bd xw yw tables nBlocks q) p).upper (ly.n + 1) k l :
          ℤ) : ℝ) := by
  have hD : (0 : ℚ) < g.D := by exact_mod_cast hg.D_pos
  have hab : (((g.X p : ℚ) / g.D : ℚ) : ℝ) < (((g.X (p + 1) : ℚ) / g.D : ℚ) : ℝ) :=
    Rat.cast_lt.mpr (div_lt_div_of_pos_right (by exact_mod_cast hX) hD)
  have hcd : (((g.Y q : ℚ) / g.D : ℚ) : ℝ) < (((g.Y (q + 1) : ℚ) / g.D : ℚ) : ℝ) :=
    Rat.cast_lt.mpr (div_lt_div_of_pos_right (by exact_mod_cast hY) hD)
  have heq := mixedDeriv_field_eq (contDiff_const (c := (1 : ℝ))) hab hcd hsx hsy hk hl hx hy
  have h := mem_Icc_rowCorners ly hg bd xw yw tables hblock htab hterm hrow hcoeff htables hp hpb
    hX hY (by omega : k ≤ ly.n + 1) (by omega : l ≤ ly.n + 1) hx hy
  unfold scaledCellDeriv at h
  rw [heq]
  exact h

/-! ### The table check by blocks -/

/-- The table check of the block `b`: the tangential windows within range and complete on the cells
of the block below `nCells`, and the table entries bounded. -/
def tableBlockCheck (ly : Layout) (g : Grid ly.n) (L : ℕ) (lv : ℕ → Level) (bd : Bounds)
    (xw : ℕ → ℕ → ℕ × ℕ) (nCells b : ℕ) : Bool :=
  (List.range L).all fun m ↦
    decide ((xw b m).1 + (xw b m).2 ≤ (lv m).rows) && decide ((xw b m).2 ≤ bd.tangentialWindow) &&
    ((List.range ly.block).all fun c ↦ !decide (b * ly.block + c < nCells) ||
      (List.range (lv m).rows).all fun i ↦
        decide ((xw b m).1 ≤ i ∧ i < (xw b m).1 + (xw b m).2) ||
        ((lv m).xModes i).all fun τ ↦
          inactiveB ly.n (g.xNum m) τ (g.X (b * ly.block + c)) (g.X (b * ly.block + c + 1))) &&
    (List.range (xw b m).2).all fun u ↦ (List.range ly.slots).all fun s ↦
      decide ((xEntry ly g lv m b ((xw b m).1 + u) s).natAbs ≤ bd.table)

/-- `tableCheck` is the conjunction of the block checks `tableBlockCheck` over the blocks. -/
theorem tableCheck_eq_all (ly : Layout) (g : Grid ly.n) (L : ℕ) (lv : ℕ → Level) (bd : Bounds)
    (xw : ℕ → ℕ → ℕ × ℕ) (nBlocks nCells : ℕ) :
    tableCheck ly g L lv bd xw nBlocks nCells =
      (List.range nBlocks).all (tableBlockCheck ly g L lv bd xw nCells) := rfl

/-- `List.range n` checked in two parts. -/
theorem all_range_eq_and (p : ℕ → Bool) {k n : ℕ} (hk : k ≤ n) :
    (List.range n).all p = ((List.range k).all p && (List.range' k (n - k)).all p) := by
  rw [← List.all_append]
  congr 1
  rw [List.range_eq_range', List.range_eq_range']
  have h := List.range'_append_1 (s := 0) (m := k) (n := n - k)
  rw [zero_add, Nat.add_sub_cancel' hk] at h
  exact h.symm

/-- `List.range' a (b + c)` checked in two parts. -/
theorem all_range'_add (p : ℕ → Bool) (a b c : ℕ) :
    (List.range' a (b + c)).all p = ((List.range' a b).all p && (List.range' (a + b) c).all p) := by
  rw [← List.all_append, List.range'_append_1]

/-! ### The checks do not depend on the coefficients -/

section Congruence

variable {ly : Layout} {g : Grid ly.n} {L : ℕ} {lv lv' : ℕ → Level} {bd : Bounds}

/-- The tangential tables depend on the levels only through their tangential modes. -/
theorem xTable_congr (hxM : ∀ m, (lv m).xModes = (lv' m).xModes) (m b i : ℕ) :
    xTable ly g lv m b i = xTable ly g lv' m b i := by
  unfold xTable xEntry
  simp only [hxM]

/-- `tableCheck` depends on the levels only through their tangential modes and numbers of rows. -/
theorem tableCheck_congr (hxM : ∀ m, (lv m).xModes = (lv' m).xModes)
    (hrows : ∀ m, (lv m).rows = (lv' m).rows) (xw : ℕ → ℕ → ℕ × ℕ) (nBlocks nCells : ℕ) :
    tableCheck ly g L lv bd xw nBlocks nCells = tableCheck ly g L lv' bd xw nBlocks nCells := by
  unfold tableCheck xEntry
  simp only [hxM, hrows]

/-- `termCheck` depends on the levels only through their modes and their numbers of rows and
columns. -/
theorem termCheck_congr (hxM : ∀ m, (lv m).xModes = (lv' m).xModes)
    (hyM : ∀ m, (lv m).yModes = (lv' m).yModes) (hrows : ∀ m, (lv m).rows = (lv' m).rows)
    (hcols : ∀ m, (lv m).cols = (lv' m).cols) : termCheck L lv bd = termCheck L lv' bd := by
  unfold termCheck
  simp only [hxM, hyM, hrows, hcols]

/-- `rowCheck` depends on the levels only through their normal modes and numbers of columns. -/
theorem rowCheck_congr (hyM : ∀ m, (lv m).yModes = (lv' m).yModes)
    (hcols : ∀ m, (lv m).cols = (lv' m).cols) (yw : ℕ → ℕ × ℕ) (q : ℕ) :
    rowCheck ly g L lv bd yw q = rowCheck ly g L lv' bd yw q := by
  unfold rowCheck yEntry
  simp only [hyM, hcols]

end Congruence

end CAS.Numerics.TensorSpline
