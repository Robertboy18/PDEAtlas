/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators

/-!
# Finite families of derivative multiindices

`MultiIndex n k` is the finite type of multiindices `a : Fin n → ℕ` with `∑ i, a i ≤ k`, and
`Top n k` is its subtype of multiindices of order exactly `k`. The entry `a i` counts the
derivatives in the coordinate `i`, so a sum over `MultiIndex n k` contains each mixed derivative of
order at most `k` once, while a sum over ordered words of coordinates would count it once for each
ordering. `succ` adds one to an entry, and `exists_pred` writes every multiindex of nonzero order as
such a successor.
-/

@[expose] public section

namespace HolderSpace

/-- Coordinate multiindices of total order at most `k`. -/
abbrev MultiIndex (n k : ℕ) := {a : Fin n → ℕ // ∑ i, a i ≤ k}

namespace MultiIndex

variable {n k : ℕ}

/-- The total order of a derivative multiindex. -/
def order (a : MultiIndex n k) : ℕ := ∑ i, a.1 i

/-- A multiindex in `MultiIndex n k` has order at most `k`. -/
theorem order_le (a : MultiIndex n k) : a.order ≤ k := a.2

noncomputable instance : Fintype (MultiIndex n k) :=
  Fintype.ofInjective
    (fun a : MultiIndex n k ↦ fun i ↦
      (⟨a.1 i, Nat.lt_succ_of_le
        ((Finset.single_le_sum (fun j _ ↦ Nat.zero_le (a.1 j))
          (Finset.mem_univ i)).trans a.2)⟩ : Fin (k + 1)))
    fun _ _ h ↦ Subtype.ext (funext fun i ↦ congrArg Fin.val (congrFun h i))

instance : Zero (MultiIndex n k) := ⟨⟨0, by simp⟩⟩

/-- The zero multiindex has order zero. -/
@[simp]
theorem order_zero : (0 : MultiIndex n k).order = 0 := by
  change (∑ _ : Fin n, 0) = 0
  simp

/-- The multiindex obtained from `a`, of order less than `k`, by adding one to the entry `i`. -/
def succ (a : MultiIndex n k) (ha : a.order < k) (i : Fin n) : MultiIndex n k :=
  ⟨fun j ↦ a.1 j + if j = i then 1 else 0, by
    have hsum : (∑ j, (a.1 j + if j = i then 1 else 0)) = a.order + 1 := by
      simp [Finset.sum_add_distrib, order]
    change (∑ j, (a.1 j + if j = i then 1 else 0)) ≤ k
    rw [hsum]
    exact ha⟩

/-- `a.succ ha i` has order `a.order + 1`. -/
@[simp]
theorem order_succ (a : MultiIndex n k) (ha : a.order < k) (i : Fin n) :
    (a.succ ha i).order = a.order + 1 := by
  simp [order, succ, Finset.sum_add_distrib]

/-- Only the zero multiindex has total order zero. -/
theorem eq_zero_of_order_eq_zero {a : MultiIndex n k} (ha : a.order = 0) : a = 0 := by
  apply Subtype.ext
  funext i
  have hi := Finset.single_le_sum (fun j _ ↦ Nat.zero_le (a.1 j)) (Finset.mem_univ i)
  change a.1 i = 0
  change a.1 i ≤ a.order at hi
  omega

/-- A multiindex `a` of nonzero order is `b.succ hb i` for some coordinate `i` and some `b` of
order less than `k`. -/
theorem exists_pred {a : MultiIndex n k} (ha : a.order ≠ 0) :
    ∃ (b : MultiIndex n k) (hb : b.order < k) (i : Fin n), b.succ hb i = a := by
  classical
  have hi : ∃ i, 0 < a.1 i := by
    by_contra! h
    apply ha
    simp [order, fun i ↦ Nat.eq_zero_of_le_zero (h i)]
  obtain ⟨i, hi⟩ := hi
  let b : Fin n → ℕ := fun j ↦ a.1 j - if j = i then 1 else 0
  have heq (j : Fin n) : b j + (if j = i then 1 else 0) = a.1 j := by
    by_cases hj : j = i
    · subst j
      simpa [b] using Nat.sub_add_cancel hi
    · simp [b, hj]
  have hsum : (∑ j, b j) + 1 = a.order := by
    calc
      _ = ∑ j, (b j + if j = i then 1 else 0) := by
        simp [Finset.sum_add_distrib]
      _ = a.order := by simp only [heq, order]
  let b' : MultiIndex n k := ⟨b, by have := a.order_le; omega⟩
  have hb : b'.order < k := by
    have := a.order_le
    change (∑ j, b j) < k
    omega
  exact ⟨b', hb, i, Subtype.ext (funext heq)⟩

/-- Multiindices of order exactly `k`. -/
abbrev Top (n k : ℕ) := {a : MultiIndex n k // a.order = k}

instance : Unique (MultiIndex n 0) where
  default := 0
  uniq a := eq_zero_of_order_eq_zero (Nat.eq_zero_of_le_zero a.order_le)

instance : Unique (Top n 0) where
  default := ⟨0, order_zero⟩
  uniq _ := Subtype.ext (Subsingleton.elim _ _)

end MultiIndex

end HolderSpace
