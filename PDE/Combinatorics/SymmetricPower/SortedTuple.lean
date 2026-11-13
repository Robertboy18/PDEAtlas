/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Multiset.Sort
import Mathlib.Algebra.BigOperators.Fin

/-!
# Ordered representatives of symmetric powers

Sorting a multiset of fixed cardinality gives a tuple of that length.
Products over the tuple are the corresponding multiset products. Thus a
symmetric power indexes ordinary multiindices once, without permutation
multiplicities.
-/

@[expose] public section

namespace Sym

variable {α M : Type*} [LinearOrder α] {n : ℕ}

/-- The sorted tuple representing a multiset of cardinality `n`. -/
def sortedTuple (s : Sym α n) : Fin n → α :=
  fun i ↦ ((s : Multiset α).sort (· ≤ ·)).get
    (Fin.cast ((Multiset.length_sort (· ≤ ·)).trans s.card_coe).symm i)

/-- Forgetting the order of the sorted tuple recovers the original multiset. -/
theorem ofFn_sortedTuple (s : Sym α n) :
    (List.ofFn s.sortedTuple : Multiset α) = (s : Multiset α) := by
  unfold sortedTuple
  rw [← List.ofFn_congr ((Multiset.length_sort (· ≤ ·)).trans s.card_coe),
    List.ofFn_get]
  exact Multiset.sort_eq (s : Multiset α) (· ≤ ·)

/-- Every entry of the sorted representative is an entry of the multiset. -/
theorem sortedTuple_mem (s : Sym α n) (i : Fin n) :
    s.sortedTuple i ∈ (s : Multiset α) :=
  (Multiset.mem_sort (· ≤ ·)).mp (List.get_mem _ _)

/-- Sorting a repeated coordinate gives the constant tuple. -/
@[simp]
theorem sortedTuple_replicate (a : α) (i : Fin n) :
    (Sym.replicate n a).sortedTuple i = a := by
  exact (Multiset.mem_replicate.mp (by
    simpa only [Sym.coe_replicate] using (Sym.replicate n a).sortedTuple_mem i)).2

/-- A product over the sorted representative is the product over the multiset. -/
theorem prod_sortedTuple [CommMonoid M] (s : Sym α n) (f : α → M) :
    (∏ i, f (s.sortedTuple i)) = ((s : Multiset α).map f).prod := by
  unfold sortedTuple
  have hlen : ((s : Multiset α).sort (· ≤ ·)).length = n :=
    (Multiset.length_sort (· ≤ ·)).trans s.card_coe
  rw [Fin.prod_congr'
    (fun i ↦ f (((s : Multiset α).sort (· ≤ ·)).get i)) hlen.symm]
  change (∏ i : Fin ((s : Multiset α).sort (· ≤ ·)).length,
    f ((s : Multiset α).sort (· ≤ ·))[i.val]) = _
  rw [Fin.prod_univ_fun_getElem]
  exact congrArg (fun t : Multiset α ↦ (t.map f).prod)
    (Multiset.sort_eq (s : Multiset α) (· ≤ ·))

/-- A repeated coordinate produces the corresponding power. -/
theorem prod_sortedTuple_replicate [CommMonoid M] (a : α) (f : α → M) :
    (∏ i, f ((Sym.replicate n a).sortedTuple i)) = f a ^ n := by
  rw [prod_sortedTuple]
  simp [Sym.coe_replicate]

/-- The multiset expression equals the usual product of coordinate powers,
with exponents given by multiplicities. -/
theorem prod_sortedTuple_eq_prod_pow_count [Fintype α] [CommMonoid M]
    (s : Sym α n) (f : α → M) :
    (∏ i, f (s.sortedTuple i)) = ∏ a, f a ^ (s : Multiset α).count a := by
  rw [prod_sortedTuple, Finset.prod_multiset_map_count]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro a _ ha
  simp only [Multiset.mem_toFinset] at ha
  rw [Multiset.count_eq_zero.mpr ha, pow_zero]

end Sym
