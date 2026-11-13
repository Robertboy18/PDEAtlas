/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.PolarDerivatives

/-!
# Normalized coefficient tables of polar expansions

The recursions (C.16)-(C.18) of Chen and Hou produce lists of terms `c cos(f β)`, `c sin(f β)`
whose length grows by a factor of about eight per order, while the number of distinct
frequencies grows linearly: at order six a table has `262144` terms and `112` distinct ones. The
normalization folds negative frequencies, merges the terms of equal frequency and kind and drops
the vanishing ones, without changing the value.

A table is stored on the box `k, l < 7`, normalized entry by entry. The values of one recursion
step depend only on the values of the previous table, so recursing on normalized tables gives
tables with the values of `polarCoeff i j` for `i + j ≤ 6`, and of the two-step `y`-chains used by
the second-order cell estimate.

## Main definitions

* `trigTermsNormalize`: the normalized list, with nonnegative frequencies, one term per frequency
  and kind, and no vanishing terms.
* `PolarTable`: a table stored on the box `k, l < 7`.
* `tabulate`: the normalized stored table of a table.
* `normCoeff`: the normalized tables `C_{i,j,·,·}`, normalized after each recursion step.
* `normStepYY`: the normalized two-step `y`-chain from `C_{i,j,·,·}`.

## Main results

* `trigTermsEval_normalize`: the normalization does not change the value of a list of terms.
* `tableEq_polarStepX`: the `x`-step maps tables with the same values to tables with the same
  values.
* `tableEq_polarStepY`: the same for the `y`-step.
* `tableEq_normCoeff`: for `i + j ≤ 6` the stored table `normCoeff i j` has the values of
  `polarCoeff i j`.
* `tableEq_normStepYY`: for `i + j ≤ 4` the stored table `normStepYY i j` has the values of the
  two `y`-steps applied to `polarCoeff i j`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Appendix C.3.1,
  (C.16)-(C.18). <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

namespace PDE.Analysis

open Finset Real

/-! ### Normalization of term lists -/

/-- The term with a nonnegative frequency and the same value. -/
def TrigTerm.canon (t : TrigTerm) : TrigTerm :=
  if t.freq < 0 then ⟨if t.isSin then -t.coeff else t.coeff, -t.freq, t.isSin⟩ else t

/-- The term `t.canon` with a nonnegative frequency has the same value as `t`. -/
theorem TrigTerm.eval_canon (t : TrigTerm) (θ : ℝ) : t.canon.eval θ = t.eval θ := by
  rcases t with ⟨c, f, b⟩
  unfold TrigTerm.canon
  by_cases hf : f < 0
  · simp only [hf, ↓reduceIte]
    cases b <;> simp [TrigTerm.eval, neg_mul, Real.cos_neg, Real.sin_neg]
  · simp only [hf, ↓reduceIte]

/-- Adds a term to a list, merging it into the first term of the same frequency and kind. -/
def trigTermsInsert (t : TrigTerm) : List TrigTerm → List TrigTerm
  | [] => [t]
  | u :: l =>
    if u.freq = t.freq ∧ u.isSin = t.isSin then ⟨u.coeff + t.coeff, u.freq, u.isSin⟩ :: l
    else u :: trigTermsInsert t l

/-- Inserting `t` into `l` adds its value: `trigTermsInsert t l` evaluates to
`t.eval θ + trigTermsEval l θ`. -/
theorem trigTermsEval_insert (t : TrigTerm) (l : List TrigTerm) (θ : ℝ) :
    trigTermsEval (trigTermsInsert t l) θ = t.eval θ + trigTermsEval l θ := by
  induction l with
  | nil => simp [trigTermsInsert, trigTermsEval_cons]
  | cons u l ih =>
    unfold trigTermsInsert
    split_ifs with h
    · rcases t with ⟨c, f, b⟩
      rcases u with ⟨d, g, b'⟩
      obtain ⟨hf, hb⟩ := h
      simp only at hf hb
      subst hf hb
      simp only [trigTermsEval_cons, TrigTerm.eval]
      push_cast
      ring
    · rw [trigTermsEval_cons, trigTermsEval_cons, ih]
      ring

/-- A term is kept by the normalization: nonzero coefficient and not `sin (0 β)`. -/
def TrigTerm.keep (t : TrigTerm) : Bool := (t.coeff != 0) && !(t.isSin && t.freq == 0)

/-- A term dropped by the normalization (`t.keep = false`) vanishes identically. -/
theorem TrigTerm.eval_eq_zero_of_not_keep {t : TrigTerm} (h : t.keep = false) (θ : ℝ) :
    t.eval θ = 0 := by
  rcases t with ⟨c, f, b⟩
  simp only [TrigTerm.keep, Bool.and_eq_false_iff, bne_eq_false_iff_eq, Bool.not_eq_eq_eq_not,
    Bool.not_false, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with h | ⟨hb, hf⟩
  · simp [TrigTerm.eval, h]
  · simp [TrigTerm.eval, hb, hf]

/-- Dropping the terms with `t.keep = false` does not change the value of a list. -/
theorem trigTermsEval_filter_keep (l : List TrigTerm) (θ : ℝ) :
    trigTermsEval (l.filter TrigTerm.keep) θ = trigTermsEval l θ := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    rw [List.filter_cons]
    split_ifs with h
    · rw [trigTermsEval_cons, trigTermsEval_cons, ih]
    · rw [ih, trigTermsEval_cons, TrigTerm.eval_eq_zero_of_not_keep (by simpa using h), zero_add]

/-- The normalized list: nonnegative frequencies, one term per frequency and kind, no vanishing
terms. -/
def trigTermsNormalize (l : List TrigTerm) : List TrigTerm :=
  ((l.map TrigTerm.canon).foldr trigTermsInsert []).filter TrigTerm.keep

/-- The normalization `trigTermsNormalize` does not change the value of a list of terms. -/
theorem trigTermsEval_normalize (l : List TrigTerm) (θ : ℝ) :
    trigTermsEval (trigTermsNormalize l) θ = trigTermsEval l θ := by
  unfold trigTermsNormalize
  rw [trigTermsEval_filter_keep]
  induction l with
  | nil => rfl
  | cons t l ih =>
    rw [List.map_cons, List.foldr_cons, trigTermsEval_insert, ih, trigTermsEval_cons,
      TrigTerm.eval_canon]

/-- The normalization of the empty list is empty. -/
@[simp] theorem trigTermsNormalize_nil : trigTermsNormalize [] = [] := rfl

/-! ### Tables with the same values -/

/-- Two tables have the same values. -/
def TableEq (C C' : ℕ → ℕ → List TrigTerm) : Prop :=
  ∀ k l, trigTermsEval (C k l) = trigTermsEval (C' k l)

/-- Lists of terms with the same values have derivative lists `trigTermsDeriv` with the same
values. -/
theorem trigTermsEval_deriv_congr {l l' : List TrigTerm}
    (h : trigTermsEval l = trigTermsEval l') :
    trigTermsEval (trigTermsDeriv l) = trigTermsEval (trigTermsDeriv l') := by
  funext θ
  have h1 := hasDerivAt_trigTermsEval l θ
  have h2 := hasDerivAt_trigTermsEval l' θ
  rw [← h] at h2
  exact h1.unique h2

/-- The `x`-step maps tables with the same values to tables with the same values. -/
theorem tableEq_polarStepX {C C' : ℕ → ℕ → List TrigTerm} (h : TableEq C C') (n : ℕ) :
    TableEq (polarStepX n C) (polarStepX n C') := by
  intro k l
  funext θ
  rw [trigTermsEval_polarStepX, trigTermsEval_polarStepX, h k l,
    trigTermsEval_deriv_congr (h k l), h (k - 1) l, h k (l - 1)]

/-- The `y`-step maps tables with the same values to tables with the same values. -/
theorem tableEq_polarStepY {C C' : ℕ → ℕ → List TrigTerm} (h : TableEq C C') (n : ℕ) :
    TableEq (polarStepY n C) (polarStepY n C') := by
  intro k l
  funext θ
  rw [trigTermsEval_polarStepY, trigTermsEval_polarStepY, h k l,
    trigTermsEval_deriv_congr (h k l), h (k - 1) l, h k (l - 1)]

/-- Having the same values is a transitive relation on tables. -/
theorem TableEq.trans {C C' C'' : ℕ → ℕ → List TrigTerm} (h : TableEq C C')
    (h' : TableEq C' C'') : TableEq C C'' := fun k l ↦ (h k l).trans (h' k l)

/-- Tables with the same values give the same polar expansion. -/
theorem polarExpansion_congr {C C' : ℕ → ℕ → List TrigTerm} (h : TableEq C C') (N n : ℕ)
    (A B : ℕ → ℝ → ℝ) (r θ : ℝ) :
    polarExpansion N n C A B r θ = polarExpansion N n C' A B r θ := by
  unfold polarExpansion
  simp only [h _ _]

/-! ### Stored tables -/

/-- A table stored on the box `k, l < 7`. -/
abbrev PolarTable := Array (Array (List TrigTerm))

/-- The entry `(k, l)` of a stored table, empty outside the box. -/
def PolarTable.get (T : PolarTable) (k l : ℕ) : List TrigTerm := (T.getD k #[]).getD l []

/-- The normalized table on the box `k, l < 7`. -/
def tabulate (C : ℕ → ℕ → List TrigTerm) : PolarTable :=
  Array.ofFn (n := 7) fun k ↦ Array.ofFn (n := 7) fun l ↦ trigTermsNormalize (C k l)

/-- The entry `(k, l)` of `tabulate C` is the normalization of `C k l` on the box `k, l < 7` and
empty outside it. -/
theorem get_tabulate (C : ℕ → ℕ → List TrigTerm) (k l : ℕ) :
    (tabulate C).get k l = if k < 7 ∧ l < 7 then trigTermsNormalize (C k l) else [] := by
  unfold PolarTable.get tabulate
  by_cases hk : k < 7
  · by_cases hl : l < 7
    · simp [Array.getD_eq_getD_getElem?, hk, hl]
    · simp [Array.getD_eq_getD_getElem?, hk, hl]
  · simp [Array.getD_eq_getD_getElem?, hk]

/-- A table vanishes for `k + l > n`. -/
def TableSupp (n : ℕ) (C : ℕ → ℕ → List TrigTerm) : Prop := ∀ k l, n < k + l → C k l = []

/-- If `C` vanishes for `k + l > n`, so does its stored table `tabulate C`. -/
theorem tableSupp_tabulate {n : ℕ} {C : ℕ → ℕ → List TrigTerm} (h : TableSupp n C) :
    TableSupp n (tabulate C).get := by
  intro k l hkl
  rw [get_tabulate, h k l hkl]
  simp

/-- For `n ≤ 6`, a table vanishing for `k + l > n` has the same values as its stored table
`tabulate C`. -/
theorem tableEq_tabulate {n : ℕ} (hn : n ≤ 6) {C : ℕ → ℕ → List TrigTerm} (h : TableSupp n C) :
    TableEq (tabulate C).get C := by
  intro k l
  funext θ
  rw [get_tabulate]
  split_ifs with hkl
  · exact trigTermsEval_normalize _ θ
  · rw [h k l (by omega)]

/-! ### Normalized coefficient tables -/

/-- The normalized tables of the `y`-recursion. -/
def normCoeffY : ℕ → PolarTable
  | 0 => tabulate polarBase
  | j + 1 => tabulate (polarStepY j (normCoeffY j).get)

/-- The normalized tables `C_{i,j,·,·}`: the `y`-recursion `j` times, then the `x`-recursion `i`
times, normalized after each step. -/
def normCoeff (i j : ℕ) : PolarTable :=
  Nat.rec (normCoeffY j) (fun i T ↦ tabulate (polarStepX (i + j) T.get)) i

/-- `normCoeff 0 j` is the normalized `y`-table `normCoeffY j`. -/
theorem normCoeff_zero (j : ℕ) : normCoeff 0 j = normCoeffY j := rfl

/-- `normCoeff (i + 1) j` is the normalized `x`-step of order `i + j` of `normCoeff i j`. -/
theorem normCoeff_succ (i j : ℕ) :
    normCoeff (i + 1) j = tabulate (polarStepX (i + j) (normCoeff i j).get) := rfl

/-- The base table `polarBase` vanishes for `k + l > 0`. -/
theorem tableSupp_polarBase : TableSupp 0 polarBase := by
  intro k l h
  simp only [polarBase]
  exact ite_eq_right_iff.mpr fun h ↦ absurd h (by omega)

/-- For `j ≤ 6` the stored table `normCoeffY j` vanishes for `k + l > j` and has the values of
`polarCoeffY j`. -/
theorem normCoeffY_spec (j : ℕ) (hj : j ≤ 6) :
    TableSupp j (normCoeffY j).get ∧ TableEq (normCoeffY j).get (polarCoeffY j) := by
  induction j with
  | zero =>
    exact ⟨tableSupp_tabulate tableSupp_polarBase, tableEq_tabulate (by omega)
      tableSupp_polarBase⟩
  | succ j ih =>
    obtain ⟨hs, he⟩ := ih (by omega)
    have hs' : TableSupp (j + 1) (polarStepY j (normCoeffY j).get) :=
      fun k l h ↦ polarStepY_eq_nil hs h
    exact ⟨tableSupp_tabulate hs',
      (tableEq_tabulate hj hs').trans (tableEq_polarStepY he j)⟩

/-- For `i + j ≤ 6` the stored table `normCoeff i j` vanishes for `k + l > i + j` and has the values
of `polarCoeff i j`. -/
theorem normCoeff_spec (i j : ℕ) (h : i + j ≤ 6) :
    TableSupp (i + j) (normCoeff i j).get ∧ TableEq (normCoeff i j).get (polarCoeff i j) := by
  induction i with
  | zero => simpa [normCoeff_zero] using normCoeffY_spec j (by omega)
  | succ i ih =>
    obtain ⟨hs, he⟩ := ih (by omega)
    have hs' : TableSupp (i + j + 1) (polarStepX (i + j) (normCoeff i j).get) :=
      fun k l hkl ↦ polarStepX_eq_nil hs hkl
    rw [normCoeff_succ, polarCoeff_succ, show i + 1 + j = i + j + 1 by ring]
    exact ⟨tableSupp_tabulate hs', (tableEq_tabulate (by omega) hs').trans
      (tableEq_polarStepX he _)⟩

/-- For `i + j ≤ 6` the stored table `normCoeff i j` has the values of the coefficients
`polarCoeff i j`. -/
theorem tableEq_normCoeff {i j : ℕ} (h : i + j ≤ 6) :
    TableEq (normCoeff i j).get (polarCoeff i j) :=
  (normCoeff_spec i j h).2

/-- The normalized two-step `y`-chain from `C_{i,j,·,·}`. -/
def normStepYY (i j : ℕ) : PolarTable :=
  tabulate (polarStepY (i + j + 1) (tabulate (polarStepY (i + j) (normCoeff i j).get)).get)

/-- For `i + j ≤ 4` the stored table `normStepYY i j` has the values of the `y`-steps of orders
`i + j` and `i + j + 1` applied to `polarCoeff i j`. -/
theorem tableEq_normStepYY {i j : ℕ} (h : i + j ≤ 4) :
    TableEq (normStepYY i j).get
      (polarStepY (i + j + 1) (polarStepY (i + j) (polarCoeff i j))) := by
  obtain ⟨hs, he⟩ := normCoeff_spec i j (by omega)
  have hs1 : TableSupp (i + j + 1) (polarStepY (i + j) (normCoeff i j).get) :=
    fun k l hkl ↦ polarStepY_eq_nil hs hkl
  have hs2 : TableSupp (i + j + 1 + 1)
      (polarStepY (i + j + 1) (tabulate (polarStepY (i + j) (normCoeff i j).get)).get) :=
    fun k l hkl ↦ polarStepY_eq_nil (tableSupp_tabulate hs1) hkl
  exact (tableEq_tabulate (by omega) hs2).trans (tableEq_polarStepY
    ((tableEq_tabulate (by omega) hs1).trans (tableEq_polarStepY he _)) _)

end PDE.Analysis
