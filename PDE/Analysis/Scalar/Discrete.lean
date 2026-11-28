/-
Authors: Levent Alpöge, Tristan Buckmaster

The lemmas of this file come from modules of the Lean package of the paper
"Finite-time blow-up for the Navier–Stokes equations"
(https://github.com/tristanbuckmaster/navier-stokes, folder lean/, commit ad53419),
where they were steps of longer proofs. They were included in BlowupZoo
(https://github.com/lean-dojo/BlowupZoo, folder AtlasCandidates/) with the permission of the
authors (20 November 2026) and moved here from there; the file NOTICE of this repository records it.
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.RingTheory.PowerSeries.WellKnown

set_option linter.style.header false

/-!
# Natural numbers, integers, lists, finite sets and polynomials

The lemmas are identities and inequalities between natural numbers and integers, facts on the
elements and the length of a list, facts on finite sets and their cardinalities, and facts on
polynomials in one and in several variables (divisibility, coefficients, evaluation). The proofs use
`omega`, `simp`, `decide`, induction on lists and the algebra of `Polynomial` and `MvPolynomial`.

## Main results

* `PDE.Analysis.dite_choose_spec_of_exists`: If some `a` satisfies `p`, then the element
  `if h : ∃ a, p a then h.choose else 0` satisfies `p`. The condition is decided classically, and
  `0` is the default value in a type with a zero.
* `PDE.Analysis.getD_length_sub_of_reverse_map_neg`: If a list `l` of reals is symmetric under
  negation, `(l.map Neg.neg).reverse = l`, then for `m < l.length` the entry at index
  `l.length - 1 - m` is the negative of the entry at index `m`:
  `l.getD (l.length - 1 - m) 0 = -l.getD m 0`.
* `PDE.Analysis.lt_and_lt_of_mem_dropLast_drop`: Let `l` be a strictly increasing list of reals with
  first entry `lo` and last entry `hi`. Every entry `b` of `(l.drop 1).dropLast`, the list without
  its first and last entries, satisfies `lo < b` and `b < hi`.
* `PDE.Analysis.X_pow_dvd_mul_choose_sub_one`: For naturals `d` and `m`, in `Polynomial ℂ` the power
  `X ^ m` divides
  `(1 - X) ^ (d + 1) * (∑ s ∈ Finset.range m, C (Nat.choose (d + 1 - 1 + s) s) * X ^ s) - 1`.
* `PDE.Analysis.abs_intCast_le_intCast_sq`: For every integer `n`, `|(n : ℝ)| ≤ (n : ℝ) ^ 2`.
* `PDE.Analysis.abs_lt_one_of_mem_dropLast_drop`: Let `l` be a strictly increasing list of real
  numbers (`l.Pairwise (· < ·)`) whose first element is `-1` (`l.head? = some (-1)`) and whose last
  element is `1` (`l.getLast? = some 1`). Then every element `b` of `(l.drop 1).dropLast`, the list
  without its first and last elements, satisfies `|b| < 1`.
* `PDE.Analysis.coeff_eq_zero_of_iterate_derivative`: For a complex polynomial `P`, if the `o`-th
  formal derivative `derivative^[o] P` vanishes at `0`, written `((0 : ℝ) : ℂ)` in the statement,
  then `P.coeff o = 0`. The constant coefficient of `derivative^[o] P` is `o.factorial * P.coeff o`.
* `PDE.Analysis.comp_dvd_comp`: For complex polynomials `p`, `q` and `r`, if `p ∣ q` then
  `p.comp r ∣ q.comp r`.

There are 54 further lemmas of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open Set Polynomial
open scoped Pointwise

namespace PDE.Analysis

/-- For naturals `d` and `m`, in `Polynomial ℂ` the power `X ^ m` divides
`(1 - X) ^ (d + 1) * (∑ s ∈ Finset.range m, C (Nat.choose (d + 1 - 1 + s) s) * X ^ s) -
1`. The proof identifies the sum with the truncation at order `m` of the power series with
coefficients `Nat.choose (d + s) d`, whose product with `(1 - X) ^ (d + 1)` is `1`. -/
theorem X_pow_dvd_mul_choose_sub_one (d m : ℕ) :
    X ^ m ∣ (1 - X : Polynomial ℂ) ^ (d + 1) *
      (∑ s ∈ Finset.range m, C ((Nat.choose (d + 1 - 1 + s) s : ℕ) : ℂ) * X ^ s) - 1 := by
  set F : PowerSeries ℂ := PowerSeries.mk fun s ↦ ((Nat.choose (d + s) d : ℕ) : ℂ) with hF
  have hS : (∑ s ∈ Finset.range m, C ((Nat.choose (d + 1 - 1 + s) s : ℕ) : ℂ) * X ^ s) =
      PowerSeries.trunc m F := by
    ext k
    rw [PowerSeries.coeff_trunc, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range, hF, PowerSeries.coeff_mk, Nat.add_sub_cancel]
    split_ifs
    · rw [Nat.choose_symm_add]
    · rfl
  have hG : ((((1 - X : Polynomial ℂ) ^ (d + 1) : Polynomial ℂ)) : PowerSeries ℂ) =
      (1 - PowerSeries.X) ^ (d + 1) := by
    simp
  rw [hS, X_pow_dvd_iff]
  intro k hk
  have key := congrArg (fun q : Polynomial ℂ ↦ q.coeff k)
    (PowerSeries.trunc_trunc_mul (n := m) F ((1 - PowerSeries.X) ^ (d + 1)))
  simp only [PowerSeries.coeff_trunc, ite_eq_left hk] at key
  rw [PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one] at key
  rw [coeff_sub, mul_comm, ← Polynomial.coeff_coe, Polynomial.coe_mul, hG, key, coeff_one,
    PowerSeries.coeff_one]
  simp

/-- For every integer `n`, `|(n : ℝ)| ≤ (n : ℝ) ^ 2`. -/
theorem abs_intCast_le_intCast_sq (n : ℤ) : |(n : ℝ)| ≤ (n : ℝ) ^ 2 := by
  by_cases hn : n = 0
  · simp [hn]
  · have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hn
    rw [← sq_abs]
    nlinarith

/-- Let `l` be a strictly increasing list of real numbers (`l.Pairwise (· < ·)`) whose first element
is `-1` (`l.head? = some (-1)`) and whose last element is `1` (`l.getLast? = some 1`). Then every
element `b` of `(l.drop 1).dropLast`, the list without its first and last elements, satisfies
`|b| < 1`. The proof compares `b` with the head and, after splitting off the last element, with the
last element. -/
theorem abs_lt_one_of_mem_dropLast_drop (l : List ℝ) (hs : l.Pairwise (· < ·))
    (h0 : l.head? = some (-1))
    (h1 : l.getLast? = some 1) : ∀ b ∈ (l.drop 1).dropLast, |b| < 1 := by
  intro b hb
  cases l with
  | nil => simp at h0
  | cons a r =>
    simp only [List.head?_cons, Option.some.injEq] at h0
    simp only [List.drop_succ_cons, List.drop_zero] at hb
    have hr : r ≠ [] := by
      rintro rfl
      simp at hb
    have hbr : b ∈ r := List.mem_of_mem_dropLast hb
    have hlo : a < b := (List.pairwise_cons.1 hs).1 b hbr
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil a r), List.getLast_cons hr] at h1
    have hlast : r.getLast hr = 1 := by simpa using h1
    have hs' : r.Pairwise (· < ·) := hs.of_cons
    have e := List.dropLast_append_getLast hr
    rw [← e, List.pairwise_append] at hs'
    have hhi := hs'.2.2 b hb (r.getLast hr) (by simp)
    rw [hlast] at hhi
    rw [abs_lt]
    constructor <;> linarith

/-- For integers with `|a| ≤ B`, `|b| ≤ B`, `|c| ≤ B` and `3 * B < N`, `|a - (b + c)| < N`. -/
theorem abs_sub_add_lt_of_abs_le {a b c B N : ℤ} (ha : |a| ≤ B) (hb : |b| ≤ B) (hc : |c| ≤ B)
    (hN : 3 * B < N) :
    |a - (b + c)| < N := by
  rw [abs_le] at ha hb hc
  rw [abs_lt]
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]

/-- For integers with `|a| ≤ B`, `|b| ≤ B` and `3 * B < N`, `|a - b| < N`. -/
theorem abs_sub_lt_of_abs_le {a b B N : ℤ} (ha : |a| ≤ B) (hb : |b| ≤ B) (hN : 3 * B < N) :
    |a - b| < N := by
  rw [abs_le] at ha hb
  rw [abs_lt]
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

/-- For a complex polynomial `P`, if the `o`-th formal derivative `derivative^[o] P` vanishes at
`0`, written `((0 : ℝ) : ℂ)` in the statement, then `P.coeff o = 0`. The constant coefficient of
`derivative^[o] P` is `o.factorial * P.coeff o`. -/
theorem coeff_eq_zero_of_iterate_derivative (P : Polynomial ℂ) (o : ℕ)
    (h : (Polynomial.derivative^[o] P).eval (((0 : ℝ) : ℂ)) = 0) : P.coeff o = 0 := by
  have e := Polynomial.coeff_iterate_derivative (k := o) P 0
  rw [Complex.ofReal_zero] at h
  rw [Polynomial.coeff_zero_eq_eval_zero, h, zero_add, Nat.descFactorial_self, nsmul_eq_mul] at e
  exact (mul_eq_zero.1 e.symm).resolve_left (by exact_mod_cast Nat.factorial_ne_zero o)

/-- For complex polynomials `p`, `q` and `r`, if `p ∣ q` then `p.comp r ∣ q.comp r`. -/
theorem comp_dvd_comp {p q : Polynomial ℂ} (h : p ∣ q) (r : Polynomial ℂ) : p.comp r ∣ q.comp r :=
    by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k.comp r, Polynomial.mul_comp _ _ _⟩

/-- Congruence for a dependent function `f : (K : Fin n) → β K → ℝ`: if `K = K'` and `d : β K` and
`d' : β K'` are heterogeneously equal, then `f K d = f K' d'`. -/
theorem congr_of_eq_of_heq {n : ℕ} {β : Fin n → Type} (f : (K : Fin n) → β K → ℝ) {K K' : Fin n}
    {d : β K} {d' : β K'}
    (h : K = K') (hd : HEq d d') : f K d = f K' d' := by
  subst h
  rw [eq_of_heq hd]

/-- For a list `l` of reals, the set `{s | s ∈ Set.Icc 0 π ∧ Real.cos s ∈ l}` is countable. The
reason is that `Real.cos` is injective on `Set.Icc 0 π`, so each entry of `l` is the cosine of at
most one point of the interval. -/
theorem countable_setOf_mem_Icc_cos_mem (l : List ℝ) :
    {s | s ∈ Icc 0 Real.pi ∧ Real.cos s ∈ l}.Countable := by
  have hsub : {s | s ∈ Icc 0 Real.pi ∧ Real.cos s ∈ l} ⊆
      ⋃ b ∈ {a | a ∈ l}, {s | s ∈ Icc 0 Real.pi ∧ Real.cos s = b} :=
    fun s hs ↦ mem_biUnion hs.2 ⟨hs.1, rfl⟩
  refine Countable.mono hsub ((List.finite_toSet l).countable.biUnion fun b _ ↦ ?_)
  exact Subsingleton.countable fun s1 h1 s2 h2 ↦ Real.injOn_cos h1.1 h2.1 (h1.2.trans h2.2.symm)

/-- If `p a ↔ q a` for every `a`, then the element chosen from `∃ a, p a`, with default `z` when
there is no witness, equals the one chosen from `∃ a, q a`:
`(if h : ∃ a, p a then h.choose else z) = (if h : ∃ a, q a then h.choose else z)`. -/
theorem dite_choose_congr_of_iff {α : Type*} {p q : α → Prop} (hpq : ∀ a, p a ↔ q a)
    [Decidable (∃ a, p a)] [Decidable (∃ a, q a)] (z : α) :
    (if h : ∃ a, p a then h.choose else z) = (if h : ∃ a, q a then h.choose else z) := by
  have e : p = q := funext fun a ↦ propext (hpq a)
  subst e
  congr

open scoped Classical in
/-- If some `a` satisfies `p`, then the element `if h : ∃ a, p a then h.choose else 0` satisfies
`p`. The condition is decided classically, and `0` is the default value in a type with a zero. -/
theorem dite_choose_spec_of_exists {α : Type*} [Zero α] {p : α → Prop} (h : ∃ a, p a) :
    p (if h : ∃ a, p a then h.choose else 0) := by
  rw [dite_eq_left h]
  exact h.choose_spec

/-- Removing the first and last elements of a list of reals commutes with negating and reversing it:
`(((l.map Neg.neg).reverse).drop 1).dropLast = (((l.drop 1).dropLast).map Neg.neg).reverse`. -/
theorem dropLast_drop_one_reverse_map_neg (l : List ℝ) :
    (((l.map Neg.neg).reverse).drop 1).dropLast = (((l.drop 1).dropLast).map Neg.neg).reverse := by
  simp [List.drop_one, List.tail_reverse, List.dropLast_reverse, List.map_dropLast, List.map_tail,
    List.tail_dropLast]

/-- For a complex polynomial `P`, if `(derivative^[o] P).eval b = 0` for all `o < z`, then
`(X - C b) ^ z` divides `P`. The proof compares `z` with the root multiplicity of `b` in `P`. -/
theorem dvd_of_iterate_derivative {P : ℂ[X]} {z : ℕ} {b : ℂ}
    (h : ∀ o < z, (derivative^[o] P).eval b = 0) :
    (X - C b) ^ z ∣ P := by
  by_cases hP : P = 0
  · rw [hP]; exact dvd_zero _
  rcases Nat.eq_zero_or_pos z with hz | hz
  · rw [hz, pow_zero]; exact one_dvd _
  have hm : z - 1 < P.rootMultiplicity b :=
    (lt_rootMultiplicity_iff_isRoot_iterate_derivative hP).2 fun m hm ↦ h m (by omega)
  exact (pow_dvd_pow _ (by omega)).trans (pow_rootMultiplicity_dvd P b)

/-- For integers `n` and `ν`, if `n + ν` is even then `-n + ν` is even. -/
theorem even_neg_add_of_even_add {n ν : ℤ} (h : Even (n + ν)) : Even (-n + ν) := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r - n, by omega⟩

/-- If `lo < hi` and every entry of a list `I` of reals is `< hi`, then there is `m < hi` with
`b ≤ m` for all `b ∈ I`. The number `lo` serves as `m` when the list is empty. -/
theorem exists_lt_forall_mem_list_le {I : List ℝ} {lo hi : ℝ} (hlt : lo < hi)
    (h : ∀ b ∈ I, b < hi) :
    ∃ m, m < hi ∧ ∀ b ∈ I, b ≤ m := by
  induction I with
  | nil => exact ⟨lo, hlt, by simp⟩
  | cons a I ih =>
    obtain ⟨m, hm, hmI⟩ := ih fun b hb ↦ h b (List.mem_cons_of_mem _ hb)
    refine ⟨max a m, max_lt (h a (by simp)) hm, fun b hb ↦ ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact le_max_left _ _
    · exact le_max_of_le_right (hmI b hb)

/-- For every list `l` of real numbers there is `tL` with `0 ≤ tL` and `tL < 1` such that every
element `b` of `l` with `b < 1` satisfies `b ≤ tL`. The proof is by induction on the list, taking a
maximum for each element below `1`. -/
theorem exists_lt_one_forall_lt_one_le (l : List ℝ) :
    ∃ tL : ℝ, 0 ≤ tL ∧ tL < 1 ∧ ∀ b ∈ l, b < 1 → b ≤ tL := by
  induction l with
  | nil => exact ⟨0, le_rfl, one_pos, by simp⟩
  | cons b l ih =>
    obtain ⟨tL, h0, h1, h⟩ := ih
    by_cases hb : b < 1
    · refine ⟨max b tL, le_max_of_le_right h0, max_lt hb h1, ?_⟩
      intro c hc hc1
      rcases List.mem_cons.1 hc with rfl | hc
      · exact le_max_left _ _
      · exact (h c hc hc1).trans (le_max_right _ _)
    · refine ⟨tL, h0, h1, ?_⟩
      intro c hc hc1
      rcases List.mem_cons.1 hc with rfl | hc
      · exact absurd hc1 hb
      · exact h c hc hc1

/-- Let `l` be a strictly increasing list of real numbers whose last element is `1`. Then there is
`c < 1` such that every element of `(l.drop 1).dropLast`, the list without its first and last
elements, is `≤ c`. The proof shows that each such element is `< 1` and takes a maximum over the
finite list. -/
theorem exists_lt_one_forall_mem_dropLast_le (l : List ℝ) (hs : l.Pairwise (· < ·))
    (h1 : l.getLast? = some 1) :
    ∃ c < 1, ∀ b ∈ (l.drop 1).dropLast, b ≤ c := by
  have hlt : ∀ b ∈ (l.drop 1).dropLast, b < 1 := by
    intro b hb
    have hb' : b ∈ l.dropLast := by
      rw [List.dropLast_drop_eq_drop_dropLast] at hb
      exact List.mem_of_mem_drop hb
    have hne : l ≠ [] := by rintro rfl; simp at h1
    have hl : l.getLast hne = 1 := by
      rw [List.getLast?_eq_some_getLast hne] at h1
      exact Option.some_injective _ h1
    have e := List.dropLast_append_getLast hne
    have hp := hs
    rw [← e] at hp
    have := (List.pairwise_append.1 hp).2.2 b hb' (l.getLast hne) (by simp)
    rwa [hl] at this
  generalize (l.drop 1).dropLast = L at hlt ⊢
  induction L with
  | nil => exact ⟨0, by norm_num, by simp⟩
  | cons b L ih =>
    obtain ⟨c, hc, hcL⟩ := ih (fun x hx ↦ hlt x (List.mem_cons_of_mem _ hx))
    refine ⟨max b c, max_lt (hlt b (by simp)) hc, ?_⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_max_left _ _
    · exact (hcL x hx).trans (le_max_right _ _)

/-- If every entry of a list `l` of reals is less than `1`, then there is a real `m < 1` with
`b ≤ m` for all `b ∈ l`. -/
theorem exists_lt_one_forall_mem_le : ∀ (l : List ℝ), (∀ b ∈ l, b < 1) → ∃ m < 1, ∀ b ∈ l, b ≤ m
  | [], _ => ⟨0, one_pos, fun b hb ↦ by simp at hb⟩
  | b :: l, h => by
    obtain ⟨m, hm, hb⟩ := exists_lt_one_forall_mem_le l (fun c hc ↦ h c (by simp [hc]))
    refine ⟨max b m, max_lt (h b (by simp)) hm, fun c hc ↦ ?_⟩
    rcases List.mem_cons.1 hc with rfl | hc
    · exact le_max_left _ _
    · exact (hb c hc).trans (le_max_right _ _)

/-- A strictly increasing list `I` of reals with at least two entries has entries `α < β` such that
`α ≤ b` and `b ≤ β` for all `b ∈ I`. -/
theorem exists_min_lt_max_of_pairwise_lt {I : List ℝ} (hs : I.Pairwise (· < ·))
    (h2 : 2 ≤ I.length) :
    ∃ α β, α ∈ I ∧ β ∈ I ∧ α < β ∧ ∀ b ∈ I, α ≤ b ∧ b ≤ β := by
  match I, hs, h2 with
  | a :: c :: rest, hs, _ =>
    have hne : (a :: c :: rest).toFinset.Nonempty := ⟨a, by simp⟩
    refine ⟨_, _, List.mem_toFinset.1 (Finset.min'_mem _ hne),
        List.mem_toFinset.1 (Finset.max'_mem _ hne),
      ?_, fun b hb ↦ ⟨Finset.min'_le _ _ (List.mem_toFinset.2 hb),
          Finset.le_max' _ _ (List.mem_toFinset.2 hb)⟩⟩
    have hac : a < c := List.rel_of_pairwise_cons hs (by simp)
    exact lt_of_le_of_lt (Finset.min'_le _ _ (by
      simp)) (lt_of_lt_of_le hac (Finset.le_max' _ _ (by simp)))

/-- If every entry of a list `I` of reals is less than `1`, then there is a real `T` with `0 ≤ T`,
`T < 1` and `b ≤ T` for all `b ∈ I`. The proof is by induction on the list, taking the maximum of
the head and the bound for the tail. -/
theorem exists_nonneg_lt_one_forall_mem_le (I : List ℝ) (h : ∀ b ∈ I, b < 1) :
    ∃ T : ℝ, 0 ≤ T ∧ T < 1 ∧ ∀ b ∈ I, b ≤ T := by
  induction I with
  | nil => exact ⟨0, le_rfl, one_pos, by simp⟩
  | cons b I ih =>
    obtain ⟨T, hT0, hT1, hT⟩ := ih (fun c hc ↦ h c (List.mem_cons_of_mem _ hc))
    refine ⟨max b T, le_max_of_le_right hT0, max_lt (h b (by simp)) hT1, ?_⟩
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact le_max_left _ _
    · exact (hT c hc).trans (le_max_right _ _)

/-- For a list `L` of real numbers and a real `u` there is `δ > 0` such that, for every `v` with
`u ≤ v < u + δ`, the elements of `L` that are `≤ v` are those that are `≤ u`:
`L.filter (fun b ↦ decide (b ≤ v)) = L.filter (fun b ↦ decide (b ≤ u))`. The proof is by induction
on the list, shrinking `δ` to at most `b - u` for each element `b > u`. -/
theorem exists_pos_filter_le_eq_filter_le (L : List ℝ) (u : ℝ) : ∃ δ > 0, ∀ v, u ≤ v → v < u + δ →
    L.filter (fun b ↦ decide (b ≤ v)) = L.filter (fun b ↦ decide (b ≤ u)) := by
  induction L with
  | nil => exact ⟨1, one_pos, fun _ _ _ ↦ rfl⟩
  | cons b L ih =>
    obtain ⟨δ, hδ, hL⟩ := ih
    by_cases hb : b ≤ u
    · refine ⟨δ, hδ, fun v hv1 hv2 ↦ ?_⟩
      rw [List.filter_cons, List.filter_cons, hL v hv1 hv2]
      simp [hb, le_trans hb hv1]
    · rw [not_le] at hb
      refine ⟨min δ (b - u), lt_min hδ (by linarith), fun v hv1 hv2 ↦ ?_⟩
      have hv3 : v < b := by linarith [min_le_right δ (b - u)]
      rw [List.filter_cons, List.filter_cons, hL v hv1 (by linarith [min_le_left δ (b - u)])]
      simp [not_le.2 hb, not_le.2 hv3]

/-- If every element `b` of a list `L` of real numbers satisfies `|b| < 1`, then there is `δ > 0`
with `|b| < 1 - δ` for every `b ∈ L`. The proof is by induction on the list, taking the minimum of
the previous `δ` and `(1 - |b|) / 2` for the new element `b`. -/
theorem exists_pos_list_abs_lt_one_sub (L : List ℝ) (h : ∀ b ∈ L, |b| < 1) :
    ∃ δ > 0, ∀ b ∈ L, |b| < 1 - δ := by
  induction L with
  | nil => exact ⟨1, one_pos, by simp⟩
  | cons b L ih =>
    obtain ⟨δ, hδ, hL⟩ := ih (fun c hc ↦ h c (List.mem_cons_of_mem _ hc))
    have hb : |b| < 1 := h b (by simp)
    refine ⟨min δ ((1 - |b|) / 2), lt_min hδ (by linarith), ?_⟩
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · have := min_le_right δ ((1 - |c|) / 2)
      linarith
    · have := min_le_left δ ((1 - |b|) / 2)
      have := hL c hc
      linarith

/-- An element of `Fin 2` that is not `1` is `0`. -/
theorem fin_two_eq_zero_of_ne_one {e : Fin 2} (h : ¬e = 1) : e = 0 := by
  fin_cases e
  · rfl
  · exact absurd rfl h

/-- For a list `l` of reals and `i < ((l.drop 1).dropLast).length`,
`((l.drop 1).dropLast).getD i 0 = l.getD (i + 1) 0`. -/
theorem getD_dropLast_drop_one (l : List ℝ) (i : ℕ) (hi : i < ((l.drop 1).dropLast).length) :
    ((l.drop 1).dropLast).getD i 0 = l.getD (i + 1) 0 := by
  have hi' : i + 1 < l.length := by
    simp only [List.length_dropLast, List.length_drop] at hi; omega
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi', List.getElem_dropLast,
    List.getElem_drop]
  simp only [Nat.add_comm 1 i]

/-- Let `l` be a strictly increasing list of reals whose last element is `1`, that is
`l.getLast? = some 1`. Then `l.getD i 1 ≤ l.getD (i + 1) 1` for every `i`, where `l.getD i 1` is the
entry at index `i` with default `1`. The proof separates the cases `i + 1 < l.length`,
`i = l.length - 1`, where the entry is the last element `1`, and `i ≥ l.length`. -/
theorem getD_le_getD_succ_of_pairwise_lt (l : List ℝ) (hs : l.Pairwise (· < ·))
    (hl : l.getLast? = some 1) (i : ℕ) :
    l.getD i 1 ≤ l.getD (i + 1) 1 := by
  rcases lt_or_ge (i + 1) l.length with h | h
  · rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ (by omega)]
    exact (List.pairwise_iff_getElem.mp hs i (i + 1) (by omega) h (by omega)).le
  · rw [List.getD_eq_default _ _ h]
    rcases lt_or_ge i l.length with h' | h'
    · have hi : i = l.length - 1 := by omega
      rw [List.getD_eq_getElem _ _ h']
      rw [List.getLast?_eq_getElem?] at hl
      subst hi
      rw [List.getElem?_eq_getElem h'] at hl
      exact (Option.some.inj hl).le
    · rw [List.getD_eq_default _ _ h']

/-- Let `r` be a strictly increasing list of reals, `b` an element of `r` and `t < b`. If `n` is the
number of elements of `r.dropLast` that are `≤ t`, then `r.getD n 1 ≤ b`, where `r.getD n 1` is the
entry at index `n` with default `1`. The proof is by recursion on the list, according to whether the
head is `≤ t`. -/
theorem getD_length_filter_dropLast_le : ∀ (r : List ℝ), r.Pairwise (· < ·) → ∀ {t b : ℝ}, b ∈ r → t
    < b →
    r.getD (r.dropLast.filter (fun x ↦ decide (x ≤ t))).length 1 ≤ b
  | [], _, _, _, hb, _ => absurd hb List.not_mem_nil
  | [c], _, _, _, hb, _ => by
    rw [List.mem_singleton] at hb
    simp [hb]
  | c :: d :: r, hs, t, b, hb, htb => by
    rw [List.dropLast_cons_cons]
    obtain ⟨hc, hs'⟩ := List.pairwise_cons.1 hs
    by_cases hct : c ≤ t
    · rw [List.filter_cons_of_pos (by simpa using hct), List.length_cons, List.getD_cons_succ]
      have hb' : b ∈ d :: r := by
        rcases List.mem_cons.1 hb with h | h
        · exact absurd (h ▸ hct) (not_le.2 htb)
        · exact h
      exact getD_length_filter_dropLast_le (d :: r) hs' hb' htb
    · have hnil : (c :: (d :: r).dropLast).filter (fun x ↦ decide (x ≤ t)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx
        simp only [decide_eq_true_eq, not_le]
        rcases List.mem_cons.1 hx with h | h
        · rw [h]
          exact lt_of_not_ge hct
        · exact lt_trans (lt_of_not_ge hct) (hc x (List.dropLast_subset _ h))
      rw [hnil, List.length_nil, List.getD_cons_zero]
      rcases List.mem_cons.1 hb with h | h
      · exact h.ge
      · exact (hc b h).le

/-- If a list `l` of reals is symmetric under negation, `(l.map Neg.neg).reverse = l`, then for
`m < l.length` the entry at index `l.length - 1 - m` is the negative of the entry at index `m`:
`l.getD (l.length - 1 - m) 0 = -l.getD m 0`. -/
theorem getD_length_sub_of_reverse_map_neg (l : List ℝ) (hS : (l.map Neg.neg).reverse = l) (m : ℕ)
    (hm : m < l.length) :
    l.getD (l.length - 1 - m) 0 = -l.getD m 0 := by
  have h1 : l.length - 1 - m < ((l.map Neg.neg).reverse).length := by simp; omega
  calc l.getD (l.length - 1 - m) 0 = ((l.map Neg.neg).reverse).getD (l.length - 1 - m) 0 := by
         rw [hS]
    _ = -l.getD m 0 := by
      rw [List.getD_eq_getElem _ _ h1, List.getElem_reverse, List.getElem_map,
          List.getD_eq_getElem _ _ hm]
      congr 2
      simp
      omega

/-- If the last entry of a list `l` of reals is `1`, that is `l.getLast? = some 1`, then
`l.getD (l.length - 1) 0 = 1`. -/
theorem getD_length_sub_one_of_getLast {l : List ℝ} (h1 : l.getLast? = some 1) :
    l.getD (l.length - 1) 0 = 1 := by
  rw [List.getLast?_eq_getElem?] at h1
  rw [List.getD_eq_getElem?_getD, h1]
  rfl

/-- For a strictly increasing list `l` of real numbers whose first element is `0`, `0 ≤ l.getD i 1`
for every index `i`, where the default value `1` is returned for indices out of range. The proof
treats the head, the later entries, which are larger than the head, and the default value
separately. -/
theorem getD_one_nonneg_of_head_eq_zero (l : List ℝ) (hs : l.Pairwise (· < ·))
    (h0 : l.head? = some 0) (i : ℕ) :
    0 ≤ l.getD i 1 := by
  cases l with
  | nil => simp at h0
  | cons a r =>
    simp only [List.head?_cons, Option.some.injEq] at h0
    subst h0
    rw [List.pairwise_cons] at hs
    cases i with
    | zero => simp
    | succ k =>
      simp only [List.getD_cons_succ]
      rcases lt_or_ge k r.length with h | h
      · rw [List.getD_eq_getElem _ _ h]; exact (hs.1 _ (List.getElem_mem h)).le
      · rw [List.getD_eq_default _ _ h]; norm_num

/-- For a list `l` of reals and `j < l.length`, the entry at index `j` of the negated and reversed
list is the negative of the entry of `l` at index `l.length - 1 - j`:
`((l.map Neg.neg).reverse).getD j 0 = -(l.getD (l.length - 1 - j) 0)`. -/
theorem getD_reverse_map_neg (l : List ℝ) (j : ℕ) (hj : j < l.length) :
    ((l.map Neg.neg).reverse).getD j 0 = -(l.getD (l.length - 1 - j) 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ (by omega)]
  simp [List.getElem_reverse]

/-- For a list `l` of reals and an index `p` of `(l.drop 1).dropLast`, the list without its first
and last elements, the entry of that list at `p` is the entry of `l` at `p + 1`:
`l.getD (p + 1) 0 = ((l.drop 1).dropLast)[p]`. -/
theorem getD_succ_eq_getElem_dropLast_drop (l : List ℝ) (p : ℕ)
    (hp : p < ((l.drop 1).dropLast).length) :
    l.getD (p + 1) 0 = ((l.drop 1).dropLast)[p] := by
  cases l with
  | nil => simp at hp
  | cons c rest =>
    have hp' : p < rest.length := by simp at hp; omega
    simp [List.getElem?_eq_getElem hp']

/-- Let `l` be a strictly increasing list of reals, `k < l.length` and `k ≤ i`. If `l[k] ≤ 1`, then
`l[k] ≤ l.getD i 1`, the entry at index `i` with default `1`. The proof separates `i < l.length`,
where `l[k] ≤ l[i]`, from `i ≥ l.length`, where the default `1` is returned. -/
theorem getElem_le_getD_of_le {l : List ℝ} (hs : l.Pairwise (· < ·)) {k i : ℕ} (hk : k < l.length)
    (hki : k ≤ i) (h1 : l[k] ≤ 1) : l[k] ≤ l.getD i 1 := by
  rcases Nat.lt_or_ge i l.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]
    rcases Nat.lt_or_ge k i with h | h
    · exact (List.pairwise_iff_getElem.1 hs k i hk hi h).le
    · have he : k = i := by omega
      subst he
      exact le_rfl
  · rw [List.getD_eq_default _ _ hi]
    exact h1

/-- For a natural number `m ≥ 1`, the map `n ↦ n * m` on the integers is injective. -/
theorem int_mul_natCast_injective {m : ℕ} (hm : 1 ≤ m) : Function.Injective
    (fun n : ℤ ↦ n * (m : ℤ)) := by
  intro a b h
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  exact mul_right_cancel₀ hm0 h

/-- Let `I` be a strictly increasing list of real numbers, `b ∈ I` with `b ≤ u`, and
`c = (I.filter (fun x ↦ decide (x ≤ u))).length` the number of elements of `I` that are `≤ u`. Then
`1 ≤ c` and `b ≤ I.getD (c - 1) d` for any default value `d`. The proof is by induction on the list;
the entry at index `c - 1` is the largest element that is `≤ u`. -/
theorem le_getD_length_filter_le_sub_one (u d b : ℝ) : ∀ I : List ℝ, I.Pairwise (· < ·) → b ∈ I → b
    ≤ u →
    1 ≤ (I.filter (fun x ↦ decide (x ≤ u))).length ∧
      b ≤ I.getD ((I.filter (fun x ↦ decide (x ≤ u))).length - 1) d := by
  intro I
  induction I with
  | nil => intro _ hb; simp at hb
  | cons x J ih =>
    intro hs hb hbu
    rw [List.pairwise_cons] at hs
    by_cases hx : x ≤ u
    · have hfl : (x :: J).filter (fun x ↦ decide (x ≤ u)) = x ::
          J.filter (fun x ↦ decide (x ≤ u)) := by
        simp [hx]
      rw [hfl]
      refine ⟨by simp, ?_⟩
      simp only [List.length_cons, Nat.add_sub_cancel]
      rcases List.mem_cons.1 hb with h | h
      · subst h
        rcases Nat.eq_zero_or_pos (J.filter (fun x ↦ decide (x ≤ u))).length with h0 | h0
        · rw [h0]; simp
        · obtain ⟨c, hc⟩ : ∃ c, (J.filter (fun x ↦ decide (x ≤ u))).length = c + 1 :=
              ⟨_, (Nat.succ_pred_eq_of_pos h0).symm⟩
          rw [hc]
          simp only [List.getD_cons_succ]
          have hcl : c < J.length := by
            have := List.length_filter_le (fun x ↦ decide (x ≤ u)) J
            omega
          rw [List.getD_eq_getElem _ _ hcl]
          exact (hs.1 _ (List.getElem_mem hcl)).le
      · obtain ⟨h1, h2⟩ := ih hs.2 h hbu
        obtain ⟨c, hc⟩ : ∃ c, (J.filter (fun x ↦ decide (x ≤ u))).length = c + 1 :=
            ⟨_, (Nat.succ_pred_eq_of_pos h1).symm⟩
        rw [hc] at h2 ⊢
        simpa using h2
    · exfalso
      rcases List.mem_cons.1 hb with h | h
      · subst h; exact hx hbu
      · exact hx ((hs.1 _ h).le.trans hbu)

/-- Let `l` be a strictly increasing list of reals, `k < l.length` and `k ≤ i`. If `tb ≤ l[k]` and
`tb ≤ 1`, then `tb ≤ l.getD i 1`, the entry at index `i` with default `1`. The proof separates
`i < l.length`, where `l[k] ≤ l[i]`, from `i ≥ l.length`, where the default `1` is returned. -/
theorem le_getD_of_le_getElem {l : List ℝ} (hs : l.Pairwise (· < ·)) {k i : ℕ} (hk : k < l.length)
    (hki : k ≤ i) {tb : ℝ} (htb : tb ≤ l[k]) (h1 : tb ≤ 1) : tb ≤ l.getD i 1 := by
  rcases Nat.lt_or_ge i l.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]
    rcases Nat.lt_or_ge k i with h | h
    · exact htb.trans (le_of_lt (List.pairwise_iff_getElem.1 hs k i hk hi h))
    · have he : k = i := by omega
      subst he
      exact htb
  · rw [List.getD_eq_default _ _ hi]
    exact h1

/-- If `tb ≤ x` for every element `x` of a list `L` of real numbers and `tb ≤ 1`, then
`tb ≤ L.getD k 1` for every index `k`. Here `L.getD k 1` is the `k`-th entry of `L`, or `1` when `k`
is out of range. -/
theorem le_getD_one_of_forall_le (tb : ℝ) (L : List ℝ) (hL : ∀ x ∈ L, tb ≤ x) (h1 : tb ≤ 1)
    (k : ℕ) :
    tb ≤ L.getD k 1 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : L[k]? with
  | none => simpa using h1
  | some v => simpa using hL v (List.mem_of_getElem? h)

/-- For a list `I` of reals without repeated elements and a real `u`, the number of elements `≥ u`
plus the number of elements `≤ u` is `I.length`, plus `1` if `u` is in the list:
`(I.filter (u ≤ ·)).length + (I.filter (· ≤ u)).length = I.length + (if u ∈ I then 1 else
0)`. The proof is by induction on the list, comparing the head with `u`. -/
theorem length_filter_ge_add_length_filter_le (I : List ℝ) (hI : I.Nodup) (u : ℝ) :
    (I.filter (fun b ↦ decide (u ≤ b))).length + (I.filter (fun b ↦ decide (b ≤ u))).length =
      I.length + (if u ∈ I then 1 else 0) := by
  induction I with
  | nil => simp
  | cons a I ih =>
    rw [List.nodup_cons] at hI
    have h := ih hI.2
    rcases lt_trichotomy a u with h1 | h1 | h1
    · have hne : u ≠ a := ne_of_gt h1
      have e1 : (a :: I).filter (fun b ↦ decide (u ≤ b)) = I.filter (fun b ↦ decide (u ≤ b)) := by
        simp [not_le.2 h1]
      have e2 : (a :: I).filter (fun b ↦ decide (b ≤ u)) = a ::
          I.filter (fun b ↦ decide (b ≤ u)) := by
        simp [h1.le]
      have e3 : (u ∈ a :: I) ↔ u ∈ I := by simp [hne]
      simp only [e1, e2, e3, List.length_cons]
      omega
    · subst h1
      have e1 : (a :: I).filter (fun b ↦ decide (a ≤ b)) = a ::
          I.filter (fun b ↦ decide (a ≤ b)) := by
        simp
      have e2 : (a :: I).filter (fun b ↦ decide (b ≤ a)) = a ::
          I.filter (fun b ↦ decide (b ≤ a)) := by
        simp
      rw [ite_eq_right hI.1] at h
      simp only [e1, e2, List.length_cons, List.mem_cons_self, ite_true]
      omega
    · have hne : u ≠ a := ne_of_lt h1
      have e1 : (a :: I).filter (fun b ↦ decide (u ≤ b)) = a ::
          I.filter (fun b ↦ decide (u ≤ b)) := by
        simp [h1.le]
      have e2 : (a :: I).filter (fun b ↦ decide (b ≤ u)) = I.filter (fun b ↦ decide (b ≤ u)) := by
        simp [not_le.2 h1]
      have e3 : (u ∈ a :: I) ↔ u ∈ I := by simp [hne]
      simp only [e1, e2, e3, List.length_cons]
      omega

/-- In a strictly increasing list `I` of reals, exactly `p + 1` elements are at most the entry
`I[p]`: `(I.filter (· ≤ I[p])).length = p + 1`. The proof is by induction on the list. -/
theorem length_filter_le_getElem (I : List ℝ) (hs : I.Pairwise (· < ·)) (p : ℕ)
    (hp : p < I.length) :
    (I.filter (fun b ↦ decide (b ≤ I[p]))).length = p + 1 := by
  induction I generalizing p with
  | nil => simp at hp
  | cons a I ih =>
    rw [List.pairwise_cons] at hs
    rcases p with _ | p
    · have h0 : I.filter (fun b ↦ decide (b ≤ a)) = [] :=
        List.filter_eq_nil_iff.2 fun y hy ↦ by simp [not_le.2 (hs.1 y hy)]
      simp [h0]
    · have hp' : p < I.length := by simpa using hp
      have hlt : a < I[p] := hs.1 _ (List.getElem_mem hp')
      simp only [List.getElem_cons_succ, List.filter_cons, hlt.le, decide_true, ite_true,
          List.length_cons,
        ih hs.2 p hp']

/-- In a strictly increasing list `J` of real numbers, for every index `k < J.length` exactly
`k + 1` elements are `≤ J[k]` and exactly `k` elements are `< J[k]`:
`(J.filter (fun b ↦ decide (b ≤ J[k]))).length = k + 1` and
`(J.filter (fun b ↦ decide (b < J[k]))).length = k`. The proof is by recursion on the list. -/
theorem length_filter_le_getElem_of_pairwise_lt : ∀ (J : List ℝ), J.Pairwise (· < ·) → ∀ k
    (hk : k < J.length),
    (J.filter (fun b ↦ decide (b ≤ J[k]))).length = k + 1 ∧
        (J.filter (fun b ↦ decide (b < J[k]))).length = k
  | [], _, k, hk => by simp at hk
  | c :: J', hs, k, hk => by
    rw [List.pairwise_cons] at hs
    obtain ⟨hc, hs'⟩ := hs
    rcases k with _ | k
    · have h1 : J'.filter (fun b ↦ decide (b ≤ c)) = [] :=
        List.filter_eq_nil_iff.2 fun x hx ↦ by simp [not_le.2 (hc x hx)]
      have h2 : J'.filter (fun b ↦ decide (b < c)) = [] :=
        List.filter_eq_nil_iff.2 fun x hx ↦ by simp [not_lt.2 (hc x hx).le]
      simp [h1, h2]
    · have hk' : k < J'.length := by simpa using hk
      obtain ⟨e1, e2⟩ := length_filter_le_getElem_of_pairwise_lt J' hs' k hk'
      have hck : c < J'[k] := hc _ (List.getElem_mem hk')
      simp only [List.getElem_cons_succ, List.filter_cons, hck.le, hck, decide_true, ite_true,
          List.length_cons, e1, e2]
      refine ⟨?_, ?_⟩ <;> trivial

/-- In a strictly increasing list `I` of reals, exactly `p` elements are smaller than the entry
`I[p]` and exactly `p + 1` elements are at most `I[p]`: `(I.filter (· < I[p])).length = p` and
`(I.filter (· ≤ I[p])).length = p + 1`. The proof is by induction on the list, separating `p = 0`
from `p = q + 1`. -/
theorem length_filter_lt_and_le_getElem (I : List ℝ) (hI : I.Pairwise (· < ·)) (p : ℕ)
    (hp : p < I.length) :
    (I.filter (fun b ↦ decide (b < I[p]))).length = p ∧
      (I.filter (fun b ↦ decide (b ≤ I[p]))).length = p + 1 := by
  induction I generalizing p with
  | nil => simp at hp
  | cons c r ih =>
    rw [List.pairwise_cons] at hI
    cases p with
    | zero =>
      simp only [List.getElem_cons_zero]
      have hr1 : r.filter (fun b ↦ decide (b < c)) = [] :=
        List.filter_eq_nil_iff.2 fun b hb ↦ by simpa using (hI.1 b hb).le
      have hr2 : r.filter (fun b ↦ decide (b ≤ c)) = [] :=
        List.filter_eq_nil_iff.2 fun b hb ↦ by simpa using hI.1 b hb
      simp [hr1, hr2]
    | succ q =>
      simp only [List.getElem_cons_succ]
      have hq : q < r.length := by simpa using hp
      have hc : c < r[q] := hI.1 _ (List.getElem_mem hq)
      obtain ⟨h1, h2⟩ := ih hI.2 q hq
      simp [hc, hc.le, h1, h2]

/-- Let `l` be a strictly increasing list of reals with first entry `lo` and last entry `hi`. Every
entry `b` of `(l.drop 1).dropLast`, the list without its first and last entries, satisfies `lo < b`
and `b < hi`. Proof idea: in a strictly increasing list the head is below every later entry and the
last entry is above every earlier one. -/
theorem lt_and_lt_of_mem_dropLast_drop {l : List ℝ} {lo hi : ℝ} (hs : l.Pairwise (· < ·))
    (hf : l.head? = some lo)
    (hl : l.getLast? = some hi) : ∀ b ∈ (l.drop 1).dropLast, lo < b ∧ b < hi := by
  intro b hb
  refine ⟨?_, ?_⟩
  · match l, hs, hf, hb with
    | a :: rest, hs, hf, hb =>
      simp only [List.head?_cons, Option.some.injEq] at hf
      subst hf
      have hb' : b ∈ rest := by simpa using List.mem_of_mem_dropLast hb
      exact List.rel_of_pairwise_cons hs hb'
  · rw [List.dropLast_drop_eq_drop_dropLast] at hb
    have hb' := List.mem_of_mem_drop hb
    have e := List.dropLast_append_getLast? hi (by rw [hl]; rfl)
    rw [← e, List.pairwise_append] at hs
    exact hs.2.2 b hb' hi (by simp)

/-- Let `l` be a strictly increasing list of reals (`l.Pairwise (· < ·)`) with last entry `c`, that
is `l.getLast? = some c`. Then every entry `b` of `(l.drop 1).dropLast` satisfies `b < c`. The proof
locates `b` at an index before the last one and uses that the list is increasing. -/
theorem lt_getLast_of_mem_dropLast_drop {l : List ℝ} (hs : l.Pairwise (· < ·)) {c : ℝ}
    (hl : l.getLast? = some c) :
    ∀ b ∈ (l.drop 1).dropLast, b < c := by
  intro b hb
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hb
  have hlen : ((l.drop 1).dropLast).length = l.length - 1 - 1 := by simp
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_some_iff] at hl
  obtain ⟨hc, rfl⟩ := hl
  have hp' := hp
  rw [hlen] at hp'
  rw [List.getElem_dropLast, List.getElem_drop]
  exact List.pairwise_iff_getElem.1 hs _ _ _ _ (by omega)

/-- For a finite set `S` of integers, if `j ∈ {-1, 0, 1}` and `k - j ∈ S`, then `k` lies in the
pointwise sum `S + {-1, 0, 1}`. -/
theorem mem_finset_add_of_sub_mem {S : Finset ℤ} {k j : ℤ} (hj : j ∈ ({-1, 0, 1} : Finset ℤ))
    (h : k - j ∈ S) :
    k ∈ S + {-1, 0, 1} := by
  have := Finset.add_mem_add h hj
  rwa [sub_add_cancel] at this

/-- For complex numbers `t` and `x`, evaluating polynomials in two variables at `![t, x]` after the
inclusion of the constants is the identity:
`(MvPolynomial.eval ![t, x]).comp (algebraMap ℂ (MvPolynomial (Fin 2) ℂ)) = RingHom.id ℂ`. -/
theorem mvPolynomial_eval_comp_algebraMap (t x : ℂ) :
    (MvPolynomial.eval ![t, x]).comp (algebraMap ℂ (MvPolynomial (Fin 2) ℂ)) = RingHom.id ℂ := by
  ext c
  simp [MvPolynomial.algebraMap_eq]

/-- Let `m > 0` and `β` be natural numbers and `n` an integer with `(β : ℤ) ≠ n` and `-(β : ℤ) ≠ n`.
Then the integer `β * m` and its negative are both different from `n * m`, because the nonzero
factor `m` can be cancelled. -/
theorem natCast_mul_ne_and_neg_ne_mul (m : ℕ) (hm : 0 < m) (β : ℕ) (n : ℤ) (h1 : (β : ℤ) ≠ n)
    (h2 : -(β : ℤ) ≠ n) :
    (((β * m : ℕ) : ℤ) ≠ n * m) ∧ (-((β * m : ℕ) : ℤ) ≠ n * m) := by
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  constructor
  · intro h
    push_cast at h
    exact h1 (mul_right_cancel₀ hm' h)
  · intro h
    push_cast at h
    exact h2 (mul_right_cancel₀ hm' (by rw [← h]; ring))

/-- For `Q : MvPolynomial (Fin 2) ℂ` and real `a`, the one-variable polynomial
`Polynomial.map (MvPolynomial.eval ![(a : ℂ)]) (MvPolynomial.finSuccEquiv ℂ 1 Q)` has `natDegree` at
most `MvPolynomial.degreeOf 0 Q`. -/
theorem natDegree_map_finSuccEquiv_le_degreeOf (Q : MvPolynomial (Fin 2) ℂ) (a : ℝ) :
    (Polynomial.map (MvPolynomial.eval ![(a : ℂ)]) (MvPolynomial.finSuccEquiv ℂ 1 Q)).natDegree ≤
      MvPolynomial.degreeOf 0 Q :=
  Polynomial.natDegree_map_le.trans (MvPolynomial.natDegree_finSuccEquiv Q).le

/-- If the real number `x` is not of the form `a + q * (b - a)` with `q` rational, then
`x ≠ a + k * ((b - a) / (N + 1))` for all natural numbers `N` and `k`. -/
theorem ne_add_mul_div_of_notMem_range {a b x : ℝ} (N : ℕ)
    (hG : x ∉ range (fun q : ℚ ↦ a + (q : ℝ) * (b - a))) :
    ∀ k : ℕ, x ≠ a + (k : ℝ) * ((b - a) / ((N : ℝ) + 1)) := by
  intro k e
  apply hG
  refine ⟨(k : ℚ) / ((N : ℚ) + 1), ?_⟩
  simp only
  rw [e]; push_cast; ring

/-- For a real `a ≠ 1`, the identity `1 - C ((1 - a)⁻¹) * (X - C a) = C ((1 - a)⁻¹) * (1 - X)` holds
in `ℂ[X]`, where `(1 - a)⁻¹` and `a` are coerced from `ℝ` to `ℂ`. It reduces to
`(1 - a)⁻¹ * (1 - a) = 1`, which holds because `a ≠ 1`. -/
theorem one_sub_C_mul_X_sub_C {a : ℝ} (ha : a ≠ 1) :
    (1 : Polynomial ℂ) - Polynomial.C ((((1 : ℝ) - a)⁻¹ : ℝ) : ℂ) *
        (Polynomial.X - Polynomial.C (a : ℂ)) =
      Polynomial.C ((((1 : ℝ) - a)⁻¹ : ℝ) : ℂ) * (1 - Polynomial.X) := by
  have h1 : ((1 : ℝ) - a) ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  have hc : ((((1 : ℝ) - a)⁻¹ : ℝ) : ℂ) * (1 - (a : ℂ)) = 1 := by
    rw [show (1 - (a : ℂ)) = (((1 : ℝ) - a : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_mul,
      inv_mul_cancel₀ h1, Complex.ofReal_one]
  have h2 : Polynomial.C ((((1 : ℝ) - a)⁻¹ : ℝ) : ℂ) -
      Polynomial.C ((((1 : ℝ) - a)⁻¹ : ℝ) : ℂ) * Polynomial.C (a : ℂ) = 1 := by
    rw [← Polynomial.C_mul, ← Polynomial.C_sub, ← Polynomial.C_1]
    congr 1
    linear_combination hc
  linear_combination (-1 : Polynomial ℂ) * h2

/-- If a list `l` of reals is strictly increasing, then so is `(l.drop 1).dropLast`, the list
without its first and last elements. -/
theorem pairwise_lt_dropLast_drop_one (l : List ℝ) (hs : l.Pairwise (· < ·)) :
    ((l.drop 1).dropLast).Pairwise (· < ·) :=
  hs.sublist ((List.dropLast_sublist _).trans (List.drop_sublist _ _))

/-- For real numbers with `-1 < a`, `a < α`, `α < β`, `β < b` and `b < 1`, the list
`[-1, a, α, β, b, 1]` is strictly increasing, that is `List.Pairwise (· < ·)` holds for it. -/
theorem pairwise_lt_list_six_of_lt {a α β b : ℝ} (h1 : -1 < a) (h2 : a < α) (h3 : α < β)
    (h4 : β < b) (h5 : b < 1) :
    [-1, a, α, β, b, 1].Pairwise (· < ·) := by
  simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp, forall_eq,
    List.not_mem_nil, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_true, or_false]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> linarith

/-- Let `l` be a strictly increasing list of real numbers with first element `0` and last element
`1`. Then every element `b` of `(l.drop 1).dropLast`, the list without its first and last elements,
satisfies `0 < b` and `b < 1`. This is `lt_and_lt_of_mem_dropLast_drop` for the end points `0`
and `1`. -/
theorem pos_and_lt_one_of_mem_dropLast {l : List ℝ} (hs : l.Pairwise (· < ·))
    (h0 : l.head? = some 0)
    (h1 : l.getLast? = some 1) {b : ℝ} (hb : b ∈ (l.drop 1).dropLast) : 0 < b ∧ b < 1 :=
        lt_and_lt_of_mem_dropLast_drop hs h0 h1 b hb

/-- For a list `l` of real numbers and `k` with `k + 1 < l.length`, the list `(l.drop 1).take k` is
a sublist of `(l.drop 1).dropLast`. -/
theorem take_drop_one_sublist_dropLast (l : List ℝ) {k : ℕ} (hk : k + 1 < l.length) :
    ((l.drop 1).take k).Sublist (l.drop 1).dropLast := by
  rw [List.dropLast_eq_take]
  exact List.take_sublist_take_left (by simp only [List.length_drop]; omega)

/-- For every natural number `n`, `2 / ((n : ℝ) + 1) ≤ 2`. -/
theorem two_div_natCast_add_one_le_two (n : ℕ) : 2 / ((n : ℝ) + 1) ≤ 2 :=
  div_le_self (by norm_num) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])

/-- For finite sets `F`, `H`, `K` of integer pairs there is a natural number `N > 0` such that both
coordinates of `ι - (t.1 + t.2)` have absolute value less than `N` for all `ι ∈ F` and `t ∈ H ×ˢ K`,
and both coordinates of `ι - ι'` have absolute value less than `N` for all `ι, ι' ∈ F` and for all
`ι, ι' ∈ K`. The proof takes an integer `B` that bounds the absolute values of all coordinates of
the points of `F ∪ H ∪ K` and sets `N = (3 * B).toNat + 1`. -/
theorem exists_pos_nat_forall_abs_sub_lt (F H K : Finset (ℤ × ℤ)) :
    ∃ N : ℕ, 0 < N ∧
      (∀ ι ∈ F, ∀ t ∈ H ×ˢ K, |(ι - (t.1 + t.2)).1| < N ∧ |(ι - (t.1 + t.2)).2| < N) ∧
      (∀ ι ∈ F, ∀ ι' ∈ F, |(ι - ι').1| < N ∧ |(ι - ι').2| < N) ∧
      (∀ ι ∈ K, ∀ ι' ∈ K, |(ι - ι').1| < N ∧ |(ι - ι').2| < N) := by
  classical
  obtain ⟨B, hB⟩ : ∃ B : ℤ, ∀ ι ∈ F ∪ H ∪ K, |ι.1| ≤ B ∧ |ι.2| ≤ B := by
    refine ⟨∑ ι ∈ F ∪ H ∪ K, (|ι.1| + |ι.2|), fun ι hι ↦ ?_⟩
    have h := Finset.single_le_sum (f := fun ι : ℤ × ℤ ↦ |ι.1| + |ι.2|)
      (fun i _ ↦ add_nonneg (abs_nonneg i.1) (abs_nonneg i.2)) hι
    exact ⟨by linarith [abs_nonneg ι.2], by linarith [abs_nonneg ι.1]⟩
  have hN : 3 * B < ((((3 * B).toNat + 1 : ℕ)) : ℤ) := by
    push_cast
    linarith [Int.self_le_toNat (3 * B)]
  have mF : ∀ ι ∈ F, ι ∈ F ∪ H ∪ K := fun ι h ↦ Finset.mem_union_left _ (Finset.mem_union_left _ h)
  have mH : ∀ ι ∈ H, ι ∈ F ∪ H ∪ K := fun ι h ↦ Finset.mem_union_left _
      (Finset.mem_union_right _ h)
  have mK : ∀ ι ∈ K, ι ∈ F ∪ H ∪ K := fun ι h ↦ Finset.mem_union_right _ h
  refine ⟨(3 * B).toNat + 1, Nat.succ_pos _, ?_, ?_, ?_⟩
  · intro ι hι t ht
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp ht
    obtain ⟨a1, a2⟩ := hB ι (mF ι hι)
    obtain ⟨b1, b2⟩ := hB t.1 (mH _ h1)
    obtain ⟨c1, c2⟩ := hB t.2 (mK _ h2)
    exact ⟨abs_sub_add_lt_of_abs_le a1 b1 c1 hN, abs_sub_add_lt_of_abs_le a2 b2 c2 hN⟩
  · intro ι hι ι' hι'
    obtain ⟨a1, a2⟩ := hB ι (mF ι hι)
    obtain ⟨b1, b2⟩ := hB ι' (mF ι' hι')
    exact ⟨abs_sub_lt_of_abs_le a1 b1 hN, abs_sub_lt_of_abs_le a2 b2 hN⟩
  · intro ι hι ι' hι'
    obtain ⟨a1, a2⟩ := hB ι (mK ι hι)
    obtain ⟨b1, b2⟩ := hB ι' (mK ι' hι')
    exact ⟨abs_sub_lt_of_abs_le a1 b1 hN, abs_sub_lt_of_abs_le a2 b2 hN⟩

/-- Let `l` be a strictly increasing list of reals (`l.Pairwise (· < ·)`) with `l.getLast? = some 1`
and `2 ≤ l.length`. Then the entry before the last one is less than `1`:
`l.getD (l.length - 2) 0 < 1`. -/
theorem getD_length_sub_two_lt_one {l : List ℝ} (hs : l.Pairwise (· < ·)) (h1 : l.getLast? = some 1)
    (h2 : 2 ≤ l.length) : l.getD (l.length - 2) 0 < 1 := by
  have hlt := List.pairwise_iff_getElem.1 hs (l.length - 2) (l.length - 1) (by
    omega) (by omega) (by omega)
  have e := getD_length_sub_one_of_getLast h1
  rw [List.getD_eq_getElem _ _ (by omega)] at e
  rw [List.getD_eq_getElem _ _ (by omega), ← e]
  exact hlt

/-- For polynomials in several variables over a commutative semiring, the value at `v` of
`bind₁ g Q`, the polynomial `Q` with the polynomial `g i` substituted for the variable `i`, is the
value of `Q` at the point `i ↦ eval v (g i)`. This is Mathlib's `MvPolynomial.eval₂Hom_bind₁` for
the identity ring homomorphism. -/
theorem mvPolynomial_eval_bind₁ {σ τ R : Type*} [CommSemiring R] (v : τ → R)
    (g : σ → MvPolynomial τ R) (Q : MvPolynomial σ R) :
    MvPolynomial.eval v (MvPolynomial.bind₁ g Q) = MvPolynomial.eval
        (fun i ↦ MvPolynomial.eval v (g i)) Q := MvPolynomial.eval₂Hom_bind₁ (RingHom.id R) v g Q

/-- A list of real numbers whose first element is `u` and whose last element is `v`, with `u ≠ v`,
has length at least two. -/
theorem two_le_length_of_head_ne_getLast (l : List ℝ) {u v : ℝ} (huv : u ≠ v)
    (h1 : l.head? = some u)
    (h2 : l.getLast? = some v) :
    2 ≤ l.length := by
  match l, h1, h2 with
  | [], h1, _ => simp at h1
  | [c], h1, h2 =>
    simp only [List.head?_cons, Option.some.injEq, List.getLast?_singleton] at h1 h2
    exact absurd (h1.symm.trans h2) huv
  | _ :: _ :: _, _, _ => simp

/-- A list of real numbers whose first element is `0` and whose last element is `1` has length at
least two. A case of `two_le_length_of_head_ne_getLast`. -/
theorem two_le_length_of_head_eq_zero_of_getLast_eq_one (l : List ℝ) (h0 : l.head? = some 0)
    (h1 : l.getLast? = some 1) : 2 ≤
    l.length :=
  two_le_length_of_head_ne_getLast l zero_ne_one h0 h1

/-- Let `l` be a strictly increasing list of real numbers whose first element is `0`. Then every
element of `(l.drop 1).dropLast`, the list `l` without its first and last elements, is
positive. -/
theorem pos_of_mem_dropLast_drop {l : List ℝ} (hs : l.Pairwise (· < ·)) (h0 : l.head? = some 0) :
    ∀ e ∈ (l.drop 1).dropLast, 0 < e := by
  intro e he
  match l, hs, h0, he with
  | a :: rest, hs, h0, he =>
    simp only [List.head?_cons, Option.some.injEq] at h0
    subst h0
    simp only [List.drop_succ_cons, List.drop_zero] at he
    exact (List.pairwise_cons.1 hs).1 e (List.dropLast_subset _ he)

/-- For a list `l` of real numbers and `k < ((l.drop 1).dropLast).length`, the element of index `k`
of `(l.drop 1).dropLast` is the element of index `k + 1` of `l`, written `l.getD (k + 1) 0`. This is
`getD_succ_eq_getElem_dropLast_drop` with the two sides exchanged. -/
theorem getElem_dropLast_drop_eq_getD_succ (l : List ℝ) (k : ℕ)
    (hk : k < ((l.drop 1).dropLast).length) :
    ((l.drop 1).dropLast)[k] = l.getD (k + 1) 0 := (getD_succ_eq_getElem_dropLast_drop l k hk).symm

/-- Two integers `d` and `e` whose difference, taken in `ℝ`, has absolute value less than one are
equal. -/
theorem eq_of_abs_intCast_sub_lt_one {d e : ℤ} (h : |(d : ℝ) - e| < 1) : d = e := by
  have h' : |d - e| < 1 := by exact_mod_cast h
  have := abs_lt.mp h'
  omega

/-- Let `l` be a strictly increasing list of real numbers and let `i < j` with `j < l.length`.
Then the entry of `l` at position `i` is less than the entry at position `j`:
`l.getD i 0 < l.getD j 0`. -/
theorem getD_lt_getD_of_pairwise_lt {l : List ℝ} (hl : l.Pairwise (· < ·)) {i j : ℕ} (hij : i < j)
    (hj : j < l.length) : l.getD i 0 < l.getD j 0 := by
  rw [List.getD_eq_getElem _ _ (hij.trans hj), List.getD_eq_getElem _ _ hj]
  exact List.pairwise_iff_getElem.mp hl i j (hij.trans hj) hj hij

end PDE.Analysis
