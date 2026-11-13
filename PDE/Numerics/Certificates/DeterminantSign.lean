/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Matrix.DeterminantSign
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Positivity.Finset

/-!
# An exact check of the sign of a determinant known up to enclosures

`detSignCheck X⁰ L U P a b c f p ε` certifies that every real matrix `X` within `ε` of
`X⁰ / 2 ^ a` entrywise has negative determinant. The data are integer matrices: `X⁰`, the
strictly lower part of an approximate inverse `L'` of the unit lower factor of `X⁰` at scale
`2 ^ b` (`lowerUnitNumerator`), the upper part of an approximate inverse `U'` of the upper factor
at scale `2 ^ c` (`upperNumerator`), and the product `P = U' L'` at scale `2 ^ (b + c)`. The check
confirms the product exactly, the Frobenius bounds `‖P X⁰ - 1‖ ≤ f` and `‖P‖ ≤ p` in integer
arithmetic, `f + p n ε < 1`, and that the product of the diagonal entries of `U'` is negative;
then `det_neg_of_detSignCheck` follows from `PDE.Analysis.Matrix.det_neg_of_enclosure`, since
`det P = ∏ U'ᵢᵢ`. The factors come from a floating-point `LU` factorization; they need not be
accurate, only good enough for the Frobenius bound. The check costs `2 n³` integer products.
-/

@[expose] public section

open Finset

namespace CAS.Numerics

variable {n : ℕ}

/-- The numerators of the unit lower triangular matrix with strictly lower part `L` at scale
`2 ^ b`. -/
def lowerUnitNumerator (L : Fin n → Fin n → ℤ) (b : ℕ) (i j : Fin n) : ℤ :=
  if j < i then L i j else if i = j then 2 ^ b else 0

/-- The numerators of the upper triangular part of `U`. -/
def upperNumerator (U : Fin n → Fin n → ℤ) (i j : Fin n) : ℤ :=
  if i ≤ j then U i j else 0

/-- The exact residual numerators `2 ^ (a + b + c) (P X⁰ / 2 ^ (a + b + c) - 1)`. -/
def detResidualNumerator (X₀ P : Fin n → Fin n → ℤ) (s : ℕ) (i j : Fin n) : ℤ :=
  (∑ k, P i k * X₀ k j) - if i = j then 2 ^ s else 0

/-- The integer check of a negative determinant for every matrix within `ε` of `X⁰ / 2 ^ a`. -/
def detSignCheck (X₀ L U P : Fin n → Fin n → ℤ) (a b c : ℕ) (f p ε : ℚ) : Bool :=
  decide (∀ i j, P i j = ∑ k, upperNumerator U i k * lowerUnitNumerator L b k j) &&
  decide (0 ≤ f) && decide (0 ≤ p) && decide (0 ≤ ε) &&
  decide ((∑ i, ∑ j, detResidualNumerator X₀ P (a + b + c) i j ^ 2) * (f.den : ℤ) ^ 2 ≤
    f.num ^ 2 * 4 ^ (a + b + c)) &&
  decide ((∑ i, ∑ j, P i j ^ 2) * (p.den : ℤ) ^ 2 ≤ p.num ^ 2 * 4 ^ (b + c)) &&
  decide (f + p * (n * ε) < 1) &&
  decide (∏ i, U i i < 0)

/-- A rational bound read through its numerator and denominator. -/
private theorem le_sq_of_mul_den_sq_le {S : ℤ} {q : ℚ} {t : ℕ}
    (h : S * (q.den : ℤ) ^ 2 ≤ q.num ^ 2 * 4 ^ t) : (S : ℝ) / 4 ^ t ≤ (q : ℝ) ^ 2 := by
  have hq : (q : ℝ) = q.num / q.den := by exact_mod_cast (Rat.num_div_den q).symm
  have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have h' : (S : ℝ) * (q.den : ℝ) ^ 2 ≤ (q.num : ℝ) ^ 2 * 4 ^ t := by exact_mod_cast h
  rw [hq, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- **Sign certificate.** A passing `detSignCheck` gives `det X < 0` for every real matrix `X`
with `|Xᵢⱼ - X⁰ᵢⱼ / 2 ^ a| ≤ ε`. -/
theorem det_neg_of_detSignCheck {X₀ L U P : Fin n → Fin n → ℤ} {a b c : ℕ} {f p ε : ℚ}
    (h : detSignCheck X₀ L U P a b c f p ε = true) (X : Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i j, |X i j - (X₀ i j : ℝ) / 2 ^ a| ≤ ε) : X.det < 0 := by
  simp only [detSignCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hP, hf0⟩, hp0⟩, hε0⟩, hf⟩, hp⟩, hlt⟩, hdiag⟩ := h
  set Uq : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j ↦ (upperNumerator U i j : ℝ) / 2 ^ c
  set Lq : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun i j ↦ (lowerUnitNumerator L b i j : ℝ) / 2 ^ b
  set Pq : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j ↦ (P i j : ℝ) / 2 ^ (b + c)
  set Xq : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j ↦ (X₀ i j : ℝ) / 2 ^ a
  have hPq : Pq = Uq * Lq := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Pq, Uq, Lq, Matrix.of_apply, hP i j]
    push_cast
    rw [sum_div]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [pow_add]
    field_simp
  have hU : Uq.IsUpperTriangular := fun i j hij ↦ by
    have hij' : j < i := hij
    simp [Uq, upperNumerator, not_le.mpr hij']
  have hL : Lq.IsLowerTriangular := fun i j hij ↦ by
    have hij' : i < j := hij
    simp [Lq, lowerUnitNumerator, not_lt.mpr hij'.le, hij'.ne]
  have hL1 : ∀ i, Lq i i = 1 := fun i ↦ by
    simp [Lq, lowerUnitNumerator]
  have hdet : Pq.det < 0 := by
    rw [hPq, PDE.Analysis.Matrix.det_upper_mul_lower hU hL hL1]
    have hprod : ∏ i, Uq i i = (∏ i, (U i i : ℝ)) / (2 ^ c) ^ n := by
      simp only [Uq, Matrix.of_apply, upperNumerator, le_refl, ite_true]
      rw [prod_div_distrib, prod_const, card_univ, Fintype.card_fin]
    rw [hprod]
    have : (∏ i, (U i i : ℝ)) < 0 := by exact_mod_cast hdiag
    exact div_neg_of_neg_of_pos this (by positivity)
  have hres : ∀ i j, (Pq * Xq - 1) i j =
      (detResidualNumerator X₀ P (a + b + c) i j : ℝ) / 2 ^ (a + b + c) := by
    intro i j
    rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply]
    simp only [Pq, Xq, Matrix.of_apply, detResidualNumerator]
    push_cast
    rw [sub_div, sum_div]
    congr 1
    · refine sum_congr rfl fun k _ ↦ ?_
      rw [show a + b + c = (b + c) + a by ring, pow_add]
      field_simp
      ring
    · split_ifs <;> simp
  have hsq : ∀ (t : ℕ) (Z : Fin n → Fin n → ℤ),
      ∑ i, ∑ j, ((Z i j : ℝ) / 2 ^ t) ^ 2 = ((∑ i, ∑ j, Z i j ^ 2 : ℤ) : ℝ) / 4 ^ t := by
    intro t Z
    push_cast
    rw [sum_div]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [sum_div]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [div_pow, ← pow_mul, show (4 : ℝ) ^ t = 2 ^ (t * 2) by
      rw [mul_comm, pow_mul]; norm_num]
  have hfq : ∑ i, ∑ j, (Pq * Xq - 1) i j ^ 2 ≤ (f : ℝ) ^ 2 := by
    simp only [hres]
    rw [hsq]
    exact le_sq_of_mul_den_sq_le hf
  have hpq : ∑ i, ∑ j, Pq i j ^ 2 ≤ (p : ℝ) ^ 2 := by
    simp only [Pq, Matrix.of_apply]
    rw [hsq]
    exact le_sq_of_mul_den_sq_le hp
  have hlt' : (f : ℝ) + p * (Fintype.card (Fin n) * ε) < 1 := by
    rw [Fintype.card_fin]
    exact_mod_cast hlt
  exact PDE.Analysis.Matrix.det_neg_of_enclosure hdet (by exact_mod_cast hf0)
    (by exact_mod_cast hp0) (by exact_mod_cast hε0) hfq hpq hlt' (fun i j ↦ hX i j)

end CAS.Numerics
