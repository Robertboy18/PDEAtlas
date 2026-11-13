/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.TensorSplineNodes.CellRows
public import CAS.Numerics.TwoStageRowBounds

/-!
# Checked evaluation of the corner derivatives of a row of cells

The standard construction of the node engine from integer mesh data: knot numerators over a
common denominator, the cell boundaries of the finest mesh, and the levels. The tables of the
tangential modes (`xTable`, one packed row per block of cells and mode, with the slots
`(cell, end, order)`) do not depend on the row of cells and are built once; for a row of cells
the first stage combines the coefficient columns (`column`, the floors of `2 ^ pa` times the
coefficients) with the integer normal jets (`yEntry`), and `blockEval` gives the merged block
row, with the bias row and the scaled row sums supplied once.

`tableCheck` (once per family of tables) and `rowCheck` (per row of cells) are the finite checks:
the windows of active modes are complete, every table entry, normal jet and coefficient is
bounded by the stated `Bounds`, and the bounds make every packed sum fit its slots.
`abs_signedSlot_blockEval_sub_le` then places every slot of a block within `cellRowError` of
`2 ^ (pa + pr + pt)` times the scaled mixed derivative of the cell function at the corner the
slot holds. The field has the unit weight in the second variable; a weight such as `ρ_p` enters
through `abs_signedSlot_mergeRows_sub_le` with weighted normal jets.

## Main definitions

* `Layout`: the order, the scales of coefficients and jets, the slot widths and the block size.
* `Grid`: integer mesh data, with knot numerators and divided-difference denominators per level.
* `Bounds`: the bounds of coefficients, normal jets, table entries, windows and term counts.
* `xTable`: the packed table row of a tangential mode on a block of cells.
* `blockEval`: the merged block row of a row of cells.
* `tableCheck`, `rowCheck`: the finite checks of the tables and of one row of cells.

## Main results

* `tableCheck_spec`: a passed `tableCheck` gives the tangential window bounds, the inactivity of
  the modes outside the window and the bounds of the table entries.
* `rowCheck_spec`: a passed `rowCheck` gives the slot width inequalities and, for every level, the
  normal window bounds, the inactivity outside the window and the bounds of the normal jets.
* `abs_signedSlot_blockEval_sub_le`: under the checks every slot of a merged block row is within
  `cellRowError` of `2 ^ (pa + pr + pt)` times the scaled mixed derivative at its corner.
* `cellRowError_eq_blockError`: with cached first-stage data, `blockError` is `cellRowError`.
-/

@[expose] public section

namespace CAS.Numerics.TensorSpline

open Finset

/-- Layout and precisions: order `n + 2`, scales `2 ^ pa`, `2 ^ pr`, `2 ^ pt` of the coefficients,
normal jets and tangential jets, slot widths `w₁`, `w₂` of the two stages, the bias `α₁` of the
normal jets, the number of cells of a block, and the halving depth for reading slots. -/
structure Layout where
  /-- The order is `n + 2`; derivatives of orders `0, …, n + 1` are evaluated. -/
  n : ℕ
  /-- The scale exponent of the coefficients. -/
  pa : ℕ
  /-- The scale exponent of the normal jets. -/
  pr : ℕ
  /-- The scale exponent of the tangential jets. -/
  pt : ℕ
  /-- The slot width of the first stage. -/
  w₁ : ℕ
  /-- The slot width of the second stage. -/
  w₂ : ℕ
  /-- The bias of the normal jets. -/
  α₁ : ℕ
  /-- The number of cells of a block. -/
  block : ℕ
  /-- The halving depth of `slotList`. -/
  depth : ℕ

namespace Layout

variable (ly : Layout)

/-- The number of derivative orders. -/
def ord : ℕ := ly.n + 2

/-- The number of slots of a block row: cells, two ends, orders. -/
def slots : ℕ := ly.block * (2 * ly.ord)

/-- The cell of slot `s` within its block. -/
def cellOf (s : ℕ) : ℕ := s / (2 * ly.ord)

/-- The end of the cell of slot `s`: `false` for the left end, `true` for the right end. -/
def cornerOf (s : ℕ) : Bool := s / ly.ord % 2 == 1

/-- The order of the derivative of slot `s`. -/
def orderOf (s : ℕ) : ℕ := s % ly.ord

end Layout

/-- Integer mesh data: the common denominator, the cell boundaries of both variables, and for each
level the knot numerators and the divided-difference denominators of both variables. -/
structure Grid (n : ℕ) where
  /-- The common denominator. -/
  D : ℕ
  /-- The cell boundaries of the first variable. -/
  X : ℕ → ℤ
  /-- The cell boundaries of the second variable. -/
  Y : ℕ → ℤ
  /-- The knot numerators of the first variable of each level. -/
  xNum : ℕ → ℕ → ℤ
  /-- The knot numerators of the second variable of each level. -/
  yNum : ℕ → ℕ → ℤ
  /-- The divided-difference denominators of the first variable of each level. -/
  xP : ℕ → ℕ → Fin (n + 3) → ℤ
  /-- The divided-difference denominators of the second variable of each level. -/
  yP : ℕ → ℕ → Fin (n + 3) → ℤ

/-- The grid describes the first `L` levels. -/
structure Grid.Sound {n : ℕ} (g : Grid n) (L : ℕ) (lv : ℕ → Level) : Prop where
  /-- The common denominator is positive. -/
  D_pos : 0 < g.D
  /-- The knot numerators of the first variable increase. -/
  xNum_strictMono : ∀ m < L, StrictMono (g.xNum m)
  /-- The knot numerators of the second variable increase. -/
  yNum_strictMono : ∀ m < L, StrictMono (g.yNum m)
  /-- The knots of the first variable are the numerators over the denominator. -/
  xKnots_eq : ∀ m < L, (lv m).xKnots = ratKnots (g.xNum m) g.D
  /-- The knots of the second variable are the numerators over the denominator. -/
  yKnots_eq : ∀ m < L, (lv m).yKnots = ratKnots (g.yNum m) g.D
  /-- The denominators of the first variable are the divided-difference denominators. -/
  xP_eq : ∀ m < L, ∀ r t, g.xP m r t = denomNum n (g.xNum m) r t
  /-- The denominators of the second variable are the divided-difference denominators. -/
  yP_eq : ∀ m < L, ∀ r t, g.yP m r t = denomNum n (g.yNum m) r t

/-- Bounds checked by `tableCheck` and `rowCheck`: of the coefficient entries, the normal jets,
the table entries, the window lengths, and the numbers of terms of the modes. -/
structure Bounds where
  /-- The bound of the coefficient entries. -/
  coeff : ℕ
  /-- The bound of the integer normal jets. -/
  normal : ℕ
  /-- The bound of the table entries. -/
  table : ℕ
  /-- The bound of the normal window lengths. -/
  normalWindow : ℕ
  /-- The bound of the tangential window lengths. -/
  tangentialWindow : ℕ
  /-- The bound of the numbers of terms of the tangential modes. -/
  xTerms : ℕ
  /-- The bound of the numbers of terms of the normal modes. -/
  yTerms : ℕ

/-! ### The standard construction -/

/-- The table entry of the tangential mode `i` of level `m` in slot `s` of block `b`. -/
def xEntry (ly : Layout) (g : Grid ly.n) (lv : ℕ → Level) (m b i s : ℕ) : ℤ :=
  modeTable ly.pt ly.n (g.xNum m) g.D (g.xP m) ((lv m).xModes i)
    (g.X (b * ly.block + ly.cellOf s)) (g.X (b * ly.block + ly.cellOf s + 1)) (ly.orderOf s)
    (ly.cornerOf s)

/-- The table row of the tangential mode `i` of level `m` on block `b`. -/
def xTable (ly : Layout) (g : Grid ly.n) (lv : ℕ → Level) (m b i : ℕ) : ℕ :=
  biasedPack ly.w₂ ly.slots (xEntry ly g lv m b i)

/-- The integer normal jet of order `l` at the end `f` of the cell row `q` of the normal mode
`j` of level `m`. -/
def yEntry (ly : Layout) (g : Grid ly.n) (lv : ℕ → Level) (m q j l : ℕ) (f : Bool) : ℤ :=
  modeTable ly.pr ly.n (g.yNum m) g.D (g.yP m) ((lv m).yModes j) (g.Y q) (g.Y (q + 1)) l f

/-- The floor of `2 ^ pa` times a coefficient. -/
def coeffEntry (ly : Layout) (lv : ℕ → Level) (m i j : ℕ) : ℤ :=
  ⌊(2 : ℚ) ^ ly.pa * (lv m).coeff i j⌋

/-- The packed coefficient column `j` of level `m`, over the tangential index. -/
def column (ly : Layout) (lv : ℕ → Level) (m j : ℕ) : ℕ :=
  biasedPack ly.w₁ (lv m).rows fun i ↦ coeffEntry ly lv m i j

/-- The biased normal jets of the normal window `j₀, …, j₀ + n₁ - 1`. -/
def rowJets (ly : Layout) (g : Grid ly.n) (lv : ℕ → Level) (m q l : ℕ) (f : Bool) (j₀ : ℕ) :
    ℕ → ℕ :=
  fun t ↦ (yEntry ly g lv m q (j₀ + t) l f + ly.α₁).toNat

/-- The first stage of level `m` for the cell row `q`, order `l` and end `f`, with the columns
`cols` and the normal window `(j₀, n₁)`. -/
def rowStageOne (ly : Layout) (g : Grid ly.n) (lv : ℕ → Level) (cols : ℕ → ℕ) (m q l : ℕ)
    (f : Bool) (yw : ℕ × ℕ) : ℕ :=
  stageOne ly.w₁ ly.α₁ (lv m).rows cols (rowJets ly g lv m q l f yw.1) yw.1 yw.2

/-- The merged block row from the first-stage slots `coefs m`, the table rows `rows m` of the
tangential window `xw m`, the bias row `H` and the scaled row sums `sums m`. -/
def blockEval (ly : Layout) (L H : ℕ) (coefs rows : ℕ → Array ℕ) (sums : ℕ → ℕ)
    (xw : ℕ → ℕ × ℕ) : ℕ :=
  Nat.sub (natSum L fun m ↦ packedRowCombinationWith (xw m).2 (slotBias ly.w₁)
      (fun u ↦ (coefs m).getD ((xw m).1 + u) 0) (fun u ↦ (rows m).getD u 0) H (sums m))
    (Nat.mul (L - 1) H)

/-! ### Checks -/

/-- A term is inactive on the cell `[A, B]` (numerators), for increasing knots. -/
def inactiveB (n : ℕ) (N : ℕ → ℤ) (τ : Term) (A B : ℤ) : Bool :=
  let c := if τ.reflect then -B else A
  decide (N (τ.index + (n + 2)) ≤ c) || decide (c < N τ.index)

/-- The tables of all blocks below `nBlocks`: tangential windows within range and complete on the
cells below `nCells`, and table entries bounded. -/
def tableCheck (ly : Layout) (g : Grid ly.n) (L : ℕ) (lv : ℕ → Level) (bd : Bounds)
    (xw : ℕ → ℕ → ℕ × ℕ) (nBlocks nCells : ℕ) : Bool :=
  (List.range nBlocks).all fun b ↦ (List.range L).all fun m ↦
    decide ((xw b m).1 + (xw b m).2 ≤ (lv m).rows) && decide ((xw b m).2 ≤ bd.tangentialWindow) &&
    ((List.range ly.block).all fun c ↦ !decide (b * ly.block + c < nCells) ||
      (List.range (lv m).rows).all fun i ↦
        decide ((xw b m).1 ≤ i ∧ i < (xw b m).1 + (xw b m).2) ||
        ((lv m).xModes i).all fun τ ↦
          inactiveB ly.n (g.xNum m) τ (g.X (b * ly.block + c)) (g.X (b * ly.block + c + 1))) &&
    (List.range (xw b m).2).all fun u ↦ (List.range ly.slots).all fun s ↦
      decide ((xEntry ly g lv m b ((xw b m).1 + u) s).natAbs ≤ bd.table)

/-- The modes of the first `L` levels have at most the stated numbers of terms. -/
def termCheck (L : ℕ) (lv : ℕ → Level) (bd : Bounds) : Bool :=
  (List.range L).all fun m ↦
    ((List.range (lv m).rows).all fun i ↦ decide (((lv m).xModes i).length ≤ bd.xTerms)) &&
    (List.range (lv m).cols).all fun j ↦ decide (((lv m).yModes j).length ≤ bd.yTerms)

/-- The cell row `q`: normal windows within range and complete, normal jets bounded, and slot
widths large enough for the bounds. -/
def rowCheck (ly : Layout) (g : Grid ly.n) (L : ℕ) (lv : ℕ → Level) (bd : Bounds)
    (yw : ℕ → ℕ × ℕ) (q : ℕ) : Bool :=
  decide (2 * bd.coeff < 2 ^ ly.w₁) && decide (2 * bd.table < 2 ^ ly.w₂) &&
  decide (2 * bd.normalWindow * bd.normal * bd.coeff < 2 ^ ly.w₁) &&
  decide (2 * L * bd.tangentialWindow * (bd.normalWindow * bd.normal * bd.coeff) * bd.table <
    2 ^ ly.w₂) && decide (0 < L) &&
  (List.range L).all fun m ↦
    decide ((yw m).1 + (yw m).2 ≤ (lv m).cols) && decide ((yw m).2 ≤ bd.normalWindow) &&
    ((List.range (lv m).cols).all fun j ↦
      decide ((yw m).1 ≤ j ∧ j < (yw m).1 + (yw m).2) ||
      ((lv m).yModes j).all fun τ ↦ inactiveB ly.n (g.yNum m) τ (g.Y q) (g.Y (q + 1))) &&
    (List.range (yw m).2).all fun t ↦
      (List.range ly.ord).all fun l ↦ [false, true].all fun f ↦
        decide (-(ly.α₁ : ℤ) ≤ yEntry ly g lv m q ((yw m).1 + t) l f) &&
        decide ((yEntry ly g lv m q ((yw m).1 + t) l f).natAbs ≤ bd.normal)

/-! ### Soundness -/

/-- For strictly increasing numerators and `D > 0` the knots `N t / D` are strictly increasing. -/
theorem strictMono_ratKnots {N : ℕ → ℤ} {D : ℕ} (hN : StrictMono N) (hD : 0 < D) :
    StrictMono (ratKnots N D) := fun u v huv ↦ by
  unfold ratKnots
  exact div_lt_div_of_pos_right (by exact_mod_cast hN huv) (by exact_mod_cast hD)

/-- For strictly increasing numerators and `D > 0`, a term that passes `inactiveB` on `[A, B]` is
inactive on the cell `[A/D, B/D]`. -/
theorem Term.inactive_of_inactiveB {n : ℕ} {N : ℕ → ℤ} {D : ℕ} (hN : StrictMono N)
    (hD : 0 < D) {τ : Term} {A B : ℤ} (h : inactiveB n N τ A B = true) :
    τ.Inactive n (ratKnots N D) ((A : ℚ) / D) ((B : ℚ) / D) := by
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  unfold inactiveB at h
  unfold Term.Inactive
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  have hc : (if τ.reflect then -((B : ℚ) / D) else (A : ℚ) / D) =
      ((if τ.reflect then -B else A : ℤ) : ℚ) / D := by
    split_ifs <;> push_cast <;> ring
  simp only
  rw [hc]
  rcases h with h | h
  · left
    intro t
    unfold ratKnots
    refine div_le_div_of_nonneg_right ?_ hDq.le
    exact_mod_cast (hN.monotone (by omega : τ.index + t ≤ τ.index + (n + 2))).trans h
  · right
    intro t
    unfold ratKnots
    refine div_lt_div_of_pos_right ?_ hDq
    exact_mod_cast h.trans_le (hN.monotone (by omega : τ.index ≤ τ.index + t))

/-- Slot `k < n` of the biased pack of `f` reads back `f k` when `|f k| ≤ M` and `2 M < 2 ^ w`. -/
theorem signedSlot_biasedPack_of_natAbs_le {w n M : ℕ} {f : ℕ → ℤ} {k : ℕ} (hk : k < n)
    (hf : (f k).natAbs ≤ M) (hM : 2 * M < 2 ^ w) : signedSlot w k (biasedPack w n f) = f k :=
  signedSlot_biasedPack hk (fitsSlot_of_natAbs_le hf hM)

/-- `natSum n f` depends only on the values `f j`, `j < n`. -/
theorem natSum_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, f j = g j) : natSum n f = natSum n g := by
  rw [natSum_eq_sum, natSum_eq_sum]
  exact Finset.sum_congr rfl fun j hj ↦ h j (Finset.mem_range.mp hj)

/-- A packed row combination depends only on the scalars and rows of index below `n`. -/
theorem packedRowCombination_congr {w q n α : ℕ} {s s' rows rows' : ℕ → ℕ}
    (hs : ∀ j < n, s j = s' j) (hr : ∀ j < n, rows j = rows' j) :
    packedRowCombination w q n α s rows = packedRowCombination w q n α s' rows' := by
  unfold packedRowCombination
  rw [natSum_congr (fun j hj ↦ by rw [hs j hj, hr j hj]), natSum_congr hr, natSum_congr hs]

/-- Entry `k < n` of the array of the slot list of `x` is slot `k` of `x`. -/
theorem getD_toArray_slotList (w depth n x : ℕ) {k : ℕ} (hk : k < n) :
    ((slotList w depth n x).toArray).getD k 0 = slot w k x := by
  rw [← getD_slotList w depth n x hk]
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- A Boolean check that holds for all of `List.range n` holds at every `j < n`. -/
theorem all_range_spec {n : ℕ} {p : ℕ → Bool} (h : (List.range n).all p = true) {j : ℕ}
    (hj : j < n) : p j = true :=
  List.all_eq_true.mp h j (List.mem_range.mpr hj)

/-- A passed `rowCheck` gives the slot width inequalities, `0 < L`, and for every level the normal
window bounds, the inactivity of the modes outside the window and the bounds of the normal jets. -/
theorem rowCheck_spec {ly : Layout} {g : Grid ly.n} {L : ℕ} {lv : ℕ → Level} {bd : Bounds}
    {yw : ℕ → ℕ × ℕ} {q : ℕ} (h : rowCheck ly g L lv bd yw q = true) :
    2 * bd.coeff < 2 ^ ly.w₁ ∧ 2 * bd.table < 2 ^ ly.w₂ ∧
    2 * bd.normalWindow * bd.normal * bd.coeff < 2 ^ ly.w₁ ∧
    2 * L * bd.tangentialWindow * (bd.normalWindow * bd.normal * bd.coeff) * bd.table <
      2 ^ ly.w₂ ∧ 0 < L ∧
    ∀ m < L, (yw m).1 + (yw m).2 ≤ (lv m).cols ∧ (yw m).2 ≤ bd.normalWindow ∧
      (∀ j < (lv m).cols, ¬((yw m).1 ≤ j ∧ j < (yw m).1 + (yw m).2) →
        ∀ τ ∈ (lv m).yModes j, inactiveB ly.n (g.yNum m) τ (g.Y q) (g.Y (q + 1)) = true) ∧
      ∀ t < (yw m).2, ∀ l < ly.ord, ∀ f : Bool,
        -(ly.α₁ : ℤ) ≤ yEntry ly g lv m q ((yw m).1 + t) l f ∧
          (yEntry ly g lv m q ((yw m).1 + t) l f).natAbs ≤ bd.normal := by
  simp only [rowCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hA, hT⟩, h1⟩, h2⟩, hL⟩, hm⟩ := h
  refine ⟨hA, hT, h1, h2, hL, fun m hmL ↦ ?_⟩
  obtain ⟨⟨⟨hw, hn⟩, hc⟩, hj⟩ := hm m hmL
  refine ⟨hw, hn, fun j hj' hout τ hτ ↦ ?_, fun t ht l hl f ↦ ?_⟩
  · rcases hc j hj' with hin | hall
    · exact absurd hin hout
    · exact hall τ hτ
  · have := hj t ht l hl
    cases f
    · exact this false (by simp)
    · exact this true (by simp)

/-- A passed `tableCheck` gives, for every block `b < nBlocks` and level `m < L`, the tangential
window bounds, the inactivity of the modes outside the window and the bounds of the table
entries. -/
theorem tableCheck_spec {ly : Layout} {g : Grid ly.n} {L : ℕ} {lv : ℕ → Level} {bd : Bounds}
    {xw : ℕ → ℕ → ℕ × ℕ} {nBlocks nCells : ℕ}
    (h : tableCheck ly g L lv bd xw nBlocks nCells = true) {b : ℕ} (hb : b < nBlocks)
    {m : ℕ} (hm : m < L) :
    (xw b m).1 + (xw b m).2 ≤ (lv m).rows ∧ (xw b m).2 ≤ bd.tangentialWindow ∧
    (∀ c < ly.block, b * ly.block + c < nCells → ∀ i < (lv m).rows,
      ¬((xw b m).1 ≤ i ∧ i < (xw b m).1 + (xw b m).2) → ∀ τ ∈ (lv m).xModes i,
        inactiveB ly.n (g.xNum m) τ (g.X (b * ly.block + c)) (g.X (b * ly.block + c + 1)) =
          true) ∧
    ∀ u < (xw b m).2, ∀ s < ly.slots,
      (xEntry ly g lv m b ((xw b m).1 + u) s).natAbs ≤ bd.table := by
  simp only [tableCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨hw, hn⟩, hc⟩, he⟩ := h b hb m hm
  refine ⟨hw, hn, fun c hc' hp i hi hout τ hτ ↦ ?_, he⟩
  rcases hc c hc' with hnp | hrest
  · exact absurd hp hnp
  · rcases hrest i hi with hin | hall
    · exact absurd hin hout
    · exact hall τ hτ

/-- A passed `termCheck` bounds the numbers of terms of the modes of every level `m < L`. -/
theorem termCheck_spec {L : ℕ} {lv : ℕ → Level} {bd : Bounds} (h : termCheck L lv bd = true)
    {m : ℕ} (hm : m < L) :
    (∀ i < (lv m).rows, ((lv m).xModes i).length ≤ bd.xTerms) ∧
      ∀ j < (lv m).cols, ((lv m).yModes j).length ≤ bd.yTerms := by
  simp only [termCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  exact h m hm

/-- **Soundness of the checked evaluation.** Under the checks, every slot `s` of the merged row
of block `b` (cell `b * block + cellOf s` below `nCells`) for the cell row `q`, normal order `l`
and end `f` is within `cellRowError` of `2 ^ (pa + pr + pt)` times
`(x_{p+1} - x_p)ᵏ (y_{q+1} - y_q)ˡ ∂ₓᵏ ∂ᵧˡ` of the cell function at the corner, with
`k = orderOf s` and the tangential end `cornerOf s`. The coefficient columns `cols`, the
first-stage slots `coefs`, the table rows `rows` and the sums `sums` are the precomputed data
of the evaluation. -/
theorem abs_signedSlot_blockEval_sub_le (ly : Layout) {g : Grid ly.n} {L : ℕ}
    {lv : ℕ → Level} (hg : g.Sound L lv) (bd : Bounds) (xw : ℕ → ℕ → ℕ × ℕ)
    (yw : ℕ → ℕ × ℕ) {nBlocks nCells q b l : ℕ} (f : Bool)
    (htab : tableCheck ly g L lv bd xw nBlocks nCells = true)
    (hterm : termCheck L lv bd = true) (hrow : rowCheck ly g L lv bd yw q = true)
    (hb : b < nBlocks) (hl : l < ly.ord)
    (hcoeff : ∀ m < L, ∀ t < (yw m).2, ∀ i < (lv m).rows,
      (coeffEntry ly lv m i ((yw m).1 + t)).natAbs ≤ bd.coeff) (cols : ℕ → ℕ → ℕ)
    (hcols : ∀ m < L, ∀ t < (yw m).2,
      cols m ((yw m).1 + t) = column ly lv m ((yw m).1 + t))
    (coefs rows : ℕ → Array ℕ) (sums : ℕ → ℕ)
    (hcoefs : ∀ m < L, coefs m = (slotList ly.w₁ ly.depth (lv m).rows
      (rowStageOne ly g lv (cols m) m q l f (yw m))).toArray)
    (hrows : ∀ m < L, ∀ u < (xw b m).2,
      (rows m).getD u 0 = xTable ly g lv m b ((xw b m).1 + u))
    (hsums : ∀ m < L,
      sums m = Nat.mul (slotBias ly.w₁) (natSum (xw b m).2 fun u ↦ (rows m).getD u 0))
    {s : ℕ} (hs : s < ly.slots) (hp : b * ly.block + ly.cellOf s < nCells) :
    |(signedSlot ly.w₂ s (blockEval ly L (biasRow ly.w₂ ly.slots) coefs rows sums (xw b)) : ℝ) -
      2 ^ (ly.pa + ly.pr + ly.pt) *
        ((((g.X (b * ly.block + ly.cellOf s + 1) : ℚ) / g.D : ℚ) -
            (((g.X (b * ly.block + ly.cellOf s) : ℚ) / g.D : ℚ) : ℝ)) ^ ly.orderOf s *
          ((((g.Y (q + 1) : ℚ) / g.D : ℚ) : ℝ) - (((g.Y q : ℚ) / g.D : ℚ) : ℝ)) ^ l *
          mixedDeriv (ly.orderOf s) l (cellField ly.n L lv (fun _ ↦ 1)
            (((g.X (b * ly.block + ly.cellOf s) : ℚ) / g.D : ℚ) : ℝ)
            (((g.X (b * ly.block + ly.cellOf s + 1) : ℚ) / g.D : ℚ) : ℝ)
            (((g.Y q : ℚ) / g.D : ℚ) : ℝ) (((g.Y (q + 1) : ℚ) / g.D : ℚ) : ℝ))
          (if ly.cornerOf s then (((g.X (b * ly.block + ly.cellOf s + 1) : ℚ) / g.D : ℚ) : ℝ)
            else (((g.X (b * ly.block + ly.cellOf s) : ℚ) / g.D : ℚ) : ℝ))
          (if f then (((g.Y (q + 1) : ℚ) / g.D : ℚ) : ℝ) else (((g.Y q : ℚ) / g.D : ℚ) : ℝ)))| ≤
      (cellRowError ly.w₁ ly.α₁ 1 ((ly.n + 3) * bd.yTerms) ((ly.n + 3) * bd.xTerms) L
        cols (fun m ↦ rowJets ly g lv m q l f (yw m).1)
        (fun m ↦ rowStageOne ly g lv (cols m) m q l f (yw m)) (fun _ _ ↦ bd.table)
        (fun m ↦ (xw b m).1) (fun m ↦ (xw b m).2) (fun m ↦ (yw m).1) (fun m ↦ (yw m).2) : ℝ) := by
  obtain ⟨hA, hT, h1, h2, hL, hm⟩ := rowCheck_spec hrow
  have hcell : ly.cellOf s < ly.block := by
    unfold Layout.cellOf
    unfold Layout.slots at hs
    exact Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hs)
  have hN1 : ∀ m < L, (yw m).2 ≤ bd.normalWindow := fun m hmL ↦ (hm m hmL).2.1
  have hN2 : ∀ m < L, (xw b m).2 ≤ bd.tangentialWindow :=
    fun m hmL ↦ (tableCheck_spec htab hb hmL).2.1
  -- bounds of the first-stage inputs
  have hRv : ∀ m < L, ∀ t < (yw m).2, ((rowJets ly g lv m q l f (yw m).1 t : ℤ) - ly.α₁) =
      yEntry ly g lv m q ((yw m).1 + t) l f := by
    intro m hmL t ht
    unfold rowJets
    rw [Int.toNat_of_nonneg (by linarith [((hm m hmL).2.2.2 t ht l hl f).1])]
    ring
  have hRb : ∀ m < L, ∀ t < (yw m).2,
      ((rowJets ly g lv m q l f (yw m).1 t : ℤ) - ly.α₁).natAbs ≤ bd.normal := by
    intro m hmL t ht
    rw [hRv m hmL t ht]
    exact ((hm m hmL).2.2.2 t ht l hl f).2
  have hcolv : ∀ m < L, ∀ t < (yw m).2, ∀ i < (lv m).rows,
      signedSlot ly.w₁ i (cols m ((yw m).1 + t)) = coeffEntry ly lv m i ((yw m).1 + t) := by
    intro m hmL t ht i hi
    rw [hcols m hmL t ht]
    exact signedSlot_biasedPack_of_natAbs_le hi (hcoeff m hmL t ht i hi) hA
  have hcolb : ∀ m < L, ∀ t < (yw m).2, ∀ i < (lv m).rows,
      (signedSlot ly.w₁ i (cols m ((yw m).1 + t))).natAbs ≤ bd.coeff := by
    intro m hmL t ht i hi
    rw [hcolv m hmL t ht i hi]
    exact hcoeff m hmL t ht i hi
  have hcolD : ∀ m < L, ∀ t < (yw m).2, cols m ((yw m).1 + t) < 2 ^ (ly.w₁ * (lv m).rows) := by
    intro m hmL t ht
    rw [hcols m hmL t ht]
    exact biasedPack_lt _ _ _
  have h1' : ∀ m < L, 2 * (yw m).2 * bd.normal * bd.coeff < 2 ^ ly.w₁ := fun m hmL ↦
    lt_of_le_of_lt (by gcongr; exact hN1 m hmL) h1
  -- the first-stage slots and their bounds
  have hcoef : ∀ m < L, ∀ i < (lv m).rows, (coefs m).getD i 0 =
      slot ly.w₁ i (stageOne ly.w₁ ly.α₁ (lv m).rows (cols m) (rowJets ly g lv m q l f (yw m).1)
        (yw m).1 (yw m).2) := by
    intro m hmL i hi
    rw [hcoefs m hmL, getD_toArray_slotList _ _ _ _ hi]
    rfl
  have hHb : ∀ m < L, ∀ i < (lv m).rows,
      (signedSlot ly.w₁ i (stageOne ly.w₁ ly.α₁ (lv m).rows (cols m)
        (rowJets ly g lv m q l f (yw m).1) (yw m).1 (yw m).2)).natAbs ≤
        bd.normalWindow * bd.normal * bd.coeff := by
    intro m hmL i hi
    refine (natAbs_signedSlot_firstStage_le (fun t ht ↦ hcolD m hmL t ht)
      (fun t ht ↦ hRb m hmL t ht) (fun t ht i hi ↦ hcolb m hmL t ht i hi) (h1' m hmL) hi).trans ?_
    gcongr
    exact hN1 m hmL
  -- table entries
  have hentry : ∀ m < L, ∀ u < (xw b m).2, ∀ s' < ly.slots,
      signedSlot ly.w₂ s' (xTable ly g lv m b ((xw b m).1 + u)) =
        xEntry ly g lv m b ((xw b m).1 + u) s' := fun m hmL u hu s' hs' ↦
    signedSlot_biasedPack_of_natAbs_le hs' ((tableCheck_spec htab hb hmL).2.2.2 u hu s' hs') hT
  have hentryb : ∀ m < L, ∀ u < (xw b m).2, ∀ s' < ly.slots,
      (signedSlot ly.w₂ s' (xTable ly g lv m b ((xw b m).1 + u))).natAbs ≤ bd.table := by
    intro m hmL u hu s' hs'
    rw [hentry m hmL u hu s' hs']
    exact (tableCheck_spec htab hb hmL).2.2.2 u hu s' hs'
  have hc2 : ∀ m < L, ∀ u < (xw b m).2,
      (((coefs m).getD ((xw b m).1 + u) 0 : ℕ) : ℤ) - slotBias ly.w₁ =
        signedSlot ly.w₁ ((xw b m).1 + u) (stageOne ly.w₁ ly.α₁ (lv m).rows (cols m)
          (rowJets ly g lv m q l f (yw m).1) (yw m).1 (yw m).2) := by
    intro m hmL u hu
    rw [hcoef m hmL _ (by have := (tableCheck_spec htab hb hmL).1; omega)]
    rfl
  have hfit₂ : ∀ m < L, ∀ s' < ly.slots, FitsSlot ly.w₂ (∑ u ∈ range (xw b m).2,
      ((((coefs m).getD ((xw b m).1 + u) 0 : ℕ) : ℤ) - slotBias ly.w₁) *
        signedSlot ly.w₂ s' (xTable ly g lv m b ((xw b m).1 + u))) := by
    intro m hmL s' hs'
    refine fitsSlot_sum_mul (a := bd.normalWindow * bd.normal * bd.coeff) (b := bd.table)
      (fun u hu ↦ by
        rw [hc2 m hmL u hu]
        exact hHb m hmL _ (by have := (tableCheck_spec htab hb hmL).1; omega))
      (fun u hu ↦ hentryb m hmL u hu s' hs') ?_
    calc 2 * (xw b m).2 * (bd.normalWindow * bd.normal * bd.coeff) * bd.table ≤
        2 * L * bd.tangentialWindow * (bd.normalWindow * bd.normal * bd.coeff) * bd.table := by
          have := hN2 m hmL
          have : (xw b m).2 ≤ L * bd.tangentialWindow :=
            this.trans (Nat.le_mul_of_pos_left _ hL)
          calc 2 * (xw b m).2 * (bd.normalWindow * bd.normal * bd.coeff) * bd.table ≤
              2 * (L * bd.tangentialWindow) * (bd.normalWindow * bd.normal * bd.coeff) *
                bd.table := by gcongr
            _ = _ := by ring
      _ < 2 ^ ly.w₂ := h2
  -- the block row as merged second stages
  have hblock : blockEval ly L (biasRow ly.w₂ ly.slots) coefs rows sums (xw b) =
      mergeRows ly.w₂ ly.slots L fun m ↦ stageTwo ly.w₁ ly.w₂ ly.slots
        (fun i ↦ (coefs m).getD i 0) (xTable ly g lv m b) (xw b m).1 (xw b m).2 := by
    unfold blockEval mergeRows
    congr 1
    apply natSum_congr
    intro m hmL
    rw [hsums m hmL, packedRowCombinationWith_eq]
    unfold stageTwo
    exact packedRowCombination_congr (fun u _ ↦ rfl) (fun u hu ↦ hrows m hmL u hu)
  rw [hblock]
  refine abs_signedSlot_mergeRows_sub_le lv (wt := fun _ ↦ 1) contDiff_const _ _ _ _
    (ly.orderOf s) (ly.cornerOf s) f hs cols (fun m ↦ rowJets ly g lv m q l f (yw m).1)
    (fun m i ↦ xTable ly g lv m b i) (fun m i ↦ (coefs m).getD i 0) (fun _ _ ↦ bd.table)
    (fun m ↦ (xw b m).1) (fun m ↦ (xw b m).2) (fun m ↦ (yw m).1) (fun m ↦ (yw m).2) hL
    (fun m hmL ↦ by
      rw [hg.xKnots_eq m hmL]
      exact strictMono_ratKnots (hg.xNum_strictMono m hmL) hg.D_pos)
    (fun m hmL ↦ by
      rw [hg.yKnots_eq m hmL]
      exact strictMono_ratKnots (hg.yNum_strictMono m hmL) hg.D_pos)
    (fun m hmL ↦ (tableCheck_spec htab hb hmL).1) (fun m hmL ↦ (hm m hmL).1)
    (fun m hmL i hi hout τ hτ ↦ by
      rw [hg.xKnots_eq m hmL]
      exact Term.inactive_of_inactiveB (hg.xNum_strictMono m hmL) hg.D_pos
        ((tableCheck_spec htab hb hmL).2.2.1 _ hcell hp i hi (by omega) τ hτ))
    (fun m hmL j hj hout τ hτ ↦ by
      rw [hg.yKnots_eq m hmL]
      exact Term.inactive_of_inactiveB (hg.yNum_strictMono m hmL) hg.D_pos
        ((hm m hmL).2.2.1 j hj (by omega) τ hτ))
    hcolD
    (fun m hmL i hi t ht ↦ by
      rw [hcolv m hmL t ht i hi]
      unfold coeffEntry
      have h := abs_floor_sub_le_one ((2 : ℚ) ^ ly.pa * (lv m).coeff i ((yw m).1 + t))
      have h' := (Rat.cast_le (K := ℝ)).mpr h
      push_cast at h' ⊢
      exact h')
    (fun m hmL t ht ↦ by
      rw [hRv m hmL t ht, weightedJet_one, hg.yKnots_eq m hmL]
      refine (abs_modeTable_sub_le hg.D_pos (hg.yNum_strictMono m hmL) (hg.yP_eq m hmL) _ _ _ _
        _).trans ?_
      exact_mod_cast Nat.mul_le_mul_left _
        ((termCheck_spec hterm hmL).2 _ (by have := (hm m hmL).1; omega)))
    (fun m hmL i hi ↦ fitsSlot_sum_mul (fun t ht ↦ hRb m hmL t ht)
      (fun t ht ↦ hcolb m hmL t ht i hi) (h1' m hmL))
    (fun m hmL u hu ↦ hcoef m hmL _ (by have := (tableCheck_spec htab hb hmL).1; omega))
    (fun m hmL u hu ↦ biasedPack_lt _ _ _)
    (fun m hmL u hu ↦ by
      rw [hentry m hmL u hu s hs]
      unfold xEntry
      rw [hg.xKnots_eq m hmL]
      refine (abs_modeTable_sub_le hg.D_pos (hg.xNum_strictMono m hmL) (hg.xP_eq m hmL) _ _ _ _
        _).trans ?_
      exact_mod_cast Nat.mul_le_mul_left _
        ((termCheck_spec hterm hmL).1 _ (by have := (tableCheck_spec htab hb hmL).1; omega)))
    (fun m hmL u hu ↦ hentryb m hmL u hu s hs)
    hfit₂
    (fun s' hs' ↦ by
      refine fitsSlot_of_natAbs_le (m := L * (bd.tangentialWindow *
        (bd.normalWindow * bd.normal * bd.coeff) * bd.table)) ?_ (by linarith [h2])
      have hlev : ∀ m < L, (signedSlot ly.w₂ s' (stageTwo ly.w₁ ly.w₂ ly.slots
          (fun i ↦ (coefs m).getD i 0) (xTable ly g lv m b) (xw b m).1 (xw b m).2)).natAbs ≤
          bd.tangentialWindow * (bd.normalWindow * bd.normal * bd.coeff) * bd.table := by
        intro m hmL
        unfold stageTwo
        beta_reduce
        rw [signedSlot_packedRowCombination (s := fun u ↦ (coefs m).getD ((xw b m).1 + u) 0)
          (rows := fun u ↦ xTable ly g lv m b ((xw b m).1 + u)) (fun u _ ↦ biasedPack_lt _ _ _)
          (hfit₂ m hmL) hs']
        refine (natAbs_sum_mul_le_sum_bound (b := bd.table)
          (fun _ ↦ bd.normalWindow * bd.normal * bd.coeff) (fun u hu ↦ by
            rw [hc2 m hmL u hu]
            exact hHb m hmL _ (by have := (tableCheck_spec htab hb hmL).1; omega))
          (fun u hu ↦ hentryb m hmL u hu s' hs')).trans ?_
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
        gcongr
        exact hN2 m hmL
      calc (∑ m ∈ range L, signedSlot ly.w₂ s' (stageTwo ly.w₁ ly.w₂ ly.slots
            (fun i ↦ (coefs m).getD i 0) (xTable ly g lv m b) (xw b m).1 (xw b m).2)).natAbs ≤
          ∑ m ∈ range L, (signedSlot ly.w₂ s' (stageTwo ly.w₁ ly.w₂ ly.slots
            (fun i ↦ (coefs m).getD i 0) (xTable ly g lv m b) (xw b m).1 (xw b m).2)).natAbs :=
            Int.natAbs_sum_le _ _
        _ ≤ ∑ _m ∈ range L, bd.tangentialWindow * (bd.normalWindow * bd.normal * bd.coeff) *
            bd.table := Finset.sum_le_sum fun m hmL ↦ hlev m (Finset.mem_range.mp hmL)
        _ = _ := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul])

/-! ### The block error from cached data -/

/-- The first-stage errors of all tangential indices of a level for the cell row, from the slots
`colSlots t` of the window columns and the biased normal jets `Rs t`, with jets within `εR`. -/
def stageOneErrors (ly : Layout) (εR rows n₁ : ℕ) (colSlots : Array (Array ℕ)) (Rs : ℕ → ℕ) :
    Array ℕ :=
  ((List.range rows).map fun i ↦ natSum n₁ fun t ↦ ((Rs t : ℤ) - ly.α₁).natAbs * 1 +
    εR * (((((colSlots.getD t #[]).getD i 0 : ℕ) : ℤ) - slotBias ly.w₁).natAbs + 1)).toArray

/-- The error of a block row from the first-stage slots `coefs` and the first-stage errors
`eOnes`, for tables within `(n + 3) xTerms` bounded by `bd.table`. -/
def blockError (ly : Layout) (L : ℕ) (bd : Bounds) (coefs eOnes : ℕ → Array ℕ)
    (xw : ℕ → ℕ × ℕ) : ℕ :=
  natSum L fun m ↦ natSum (xw m).2 fun u ↦
    ((((coefs m).getD ((xw m).1 + u) 0 : ℕ) : ℤ) - slotBias ly.w₁).natAbs *
        ((ly.n + 3) * bd.xTerms) +
      (eOnes m).getD ((xw m).1 + u) 0 * (bd.table + (ly.n + 3) * bd.xTerms)

/-- Entry `i < n` of the array of `g 0, …, g (n - 1)` is `g i`. -/
theorem getD_toArray_map_range {α : Type*} (n : ℕ) (g : ℕ → α) (d : α) {i : ℕ} (hi : i < n) :
    (((List.range n).map g).toArray).getD i d = g i := by
  simp [Array.getD_eq_getD_getElem?, List.getElem?_map, List.getElem?_range hi]

/-- With cached first-stage slots, column slots and jets, `blockError` is `cellRowError`. -/
theorem cellRowError_eq_blockError (ly : Layout) {g : Grid ly.n} {L : ℕ} {lv : ℕ → Level}
    (bd : Bounds) (xw : ℕ → ℕ × ℕ) (yw : ℕ → ℕ × ℕ) {q l : ℕ} {f : Bool}
    (hi : ∀ m < L, (xw m).1 + (xw m).2 ≤ (lv m).rows) (cols : ℕ → ℕ → ℕ)
    (coefs eOnes : ℕ → Array ℕ) (colSlots : ℕ → Array (Array ℕ)) (Rs : ℕ → ℕ → ℕ)
    (hcoefs : ∀ m < L, coefs m = (slotList ly.w₁ ly.depth (lv m).rows
      (rowStageOne ly g lv (cols m) m q l f (yw m))).toArray)
    (hcolSlots : ∀ m < L, colSlots m = ((List.range (yw m).2).map fun t ↦
      (slotList ly.w₁ ly.depth (lv m).rows (cols m ((yw m).1 + t))).toArray).toArray)
    (hRs : ∀ m < L, ∀ t < (yw m).2, Rs m t = rowJets ly g lv m q l f (yw m).1 t)
    (heOnes : ∀ m < L, eOnes m = stageOneErrors ly ((ly.n + 3) * bd.yTerms) (lv m).rows
      (yw m).2 (colSlots m) (Rs m)) :
    cellRowError ly.w₁ ly.α₁ 1 ((ly.n + 3) * bd.yTerms) ((ly.n + 3) * bd.xTerms) L
        cols (fun m ↦ rowJets ly g lv m q l f (yw m).1)
        (fun m ↦ rowStageOne ly g lv (cols m) m q l f (yw m)) (fun _ _ ↦ bd.table)
        (fun m ↦ (xw m).1) (fun m ↦ (xw m).2) (fun m ↦ (yw m).1) (fun m ↦ (yw m).2) =
      blockError ly L bd coefs eOnes xw := by
  unfold cellRowError blockError
  refine natSum_congr fun m hm ↦ natSum_congr fun u hu ↦ ?_
  have hu' : u < (xw m).2 := hu
  have hiu : (xw m).1 + u < (lv m).rows := by have := hi m hm; omega
  have hH : signedSlot ly.w₁ ((xw m).1 + u) (rowStageOne ly g lv (cols m) m q l f (yw m)) =
      (((coefs m).getD ((xw m).1 + u) 0 : ℕ) : ℤ) - slotBias ly.w₁ := by
    rw [hcoefs m hm, getD_toArray_slotList _ _ _ _ hiu]
    rfl
  have hE : stageOneError ly.w₁ ly.α₁ 1 ((ly.n + 3) * bd.yTerms) (cols m)
      (rowJets ly g lv m q l f (yw m).1) (yw m).1 (yw m).2 ((xw m).1 + u) =
      (eOnes m).getD ((xw m).1 + u) 0 := by
    rw [heOnes m hm]
    unfold stageOneErrors
    rw [getD_toArray_map_range _ _ _ hiu]
    unfold stageOneError
    refine natSum_congr fun t ht ↦ ?_
    rw [hRs m hm t ht, hcolSlots m hm, getD_toArray_map_range _ _ _ ht,
      getD_toArray_slotList _ _ _ _ hiu]
    rfl
  rw [hH, hE]

end CAS.Numerics.TensorSpline

