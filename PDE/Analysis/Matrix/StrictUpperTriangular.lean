/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Data.Matrix.Mul

/-!
# Products of strictly upper triangular matrices

Each strictly upper triangular factor increases the minimum possible distance
above the diagonal of a nonzero entry by one. Consequently, a product of at least
`m` such `m`-by-`m` matrices is zero.

The factors need not coincide or commute, as for the coefficients of a time-dependent
change of coordinates. For such products, nilpotence of each factor alone would not
suffice.
-/

@[expose] public section

namespace Matrix

variable {R : Type*} [Semiring R] {m : ℕ}

/-- A product of strictly upper triangular matrices has no entries fewer than
the number of factors above the diagonal. No commutativity assumption on the
coefficient semiring or the factors is needed. -/
theorem list_prod_apply_eq_zero_of_lt
    (L : List (Matrix (Fin m) (Fin m) R))
    (hL : ∀ A ∈ L, ∀ i j, j ≤ i → A i j = 0)
    (i j : Fin m) (hij : j.val < i.val + L.length) :
    L.prod i j = 0 := by
  induction L generalizing i j with
  | nil =>
      have hne : i ≠ j := by
        intro h
        subst j
        simp only [List.length_nil, Nat.add_zero, lt_self_iff_false] at hij
      simpa only [List.prod_nil] using (Matrix.one_apply_ne (α := R) hne)
  | cons A L ih =>
      rw [List.prod_cons, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro k _
      by_cases hk : k ≤ i
      · rw [hL A List.mem_cons_self i k hk, zero_mul]
      · have hik : i.val + 1 ≤ k.val :=
          Nat.succ_le_of_lt (show i.val < k.val from lt_of_not_ge hk)
        have hjk : j.val < k.val + L.length := by
          have hstep : j.val < (i.val + 1) + L.length := by
            simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 L.length] using hij
          exact hstep.trans_le (Nat.add_le_add_right hik L.length)
        rw [ih (fun B hB ↦ hL B (List.mem_cons_of_mem A hB)) k j hjk, mul_zero]

/-- Any ordered product of at least `m` strictly upper triangular `m`-by-`m`
matrices vanishes. This applies to products of distinct matrices, including
matrices evaluated at different times. -/
theorem list_prod_eq_zero_of_strictUpperTriangular
    (L : List (Matrix (Fin m) (Fin m) R))
    (hL : ∀ A ∈ L, ∀ i j, j ≤ i → A i j = 0)
    (hlen : m ≤ L.length) :
    L.prod = 0 := by
  ext i j
  exact list_prod_apply_eq_zero_of_lt L hL i j
    (j.isLt.trans_le (hlen.trans (Nat.le_add_left _ _)))

end Matrix
