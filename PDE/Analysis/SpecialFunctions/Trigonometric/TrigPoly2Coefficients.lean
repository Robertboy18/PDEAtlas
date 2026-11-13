/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2Calculus
public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2Separable

/-!
# Coefficients of the operations on trigonometric tables

The coefficients at natural frequencies (`coeffN`, zero past the degrees) of sums, scalar
multiples, padded tables and partial derivatives are read off the definitions. Multiplying by a
coordinate table moves each frequency by one: `cos β · m_i (kβ)` is
`(m_i ((k + 1) β) + m_i ((k - 1) β)) / 2`, where the frequency `-1` folds back to `1` with the
sign of the mode, so

`(cosβ.mul p)_K = (p_(K+1) + p_(K-1) + [K = 1] σ p_0) / 2`

with `σ = 1` for cosines and `σ = -1` for sines (`coeffN_cosβ_mul`). The same holds for `sinβ`
with the sign pattern of `sin β · m_i (kβ)` (`coeffN_sinβ_mul`) and for `cosθ` in the second
variable (`coeffN_cosθ_mul`).
-/

@[expose] public section

namespace PDE.Analysis.TrigPoly2

open Finset

variable {Mβ Mθ Nβ Nθ : ℕ} {R : Type}

section Linear

variable [AddCommGroup R]

@[simp] theorem coeffN_zero (i j : Fin 2) (k l : ℕ) :
    (0 : TrigPoly2 Mβ Mθ R).coeffN i j k l = 0 := by
  unfold coeffN; split_ifs <;> rfl

@[simp] theorem coeffN_neg (p : TrigPoly2 Mβ Mθ R) (i j : Fin 2) (k l : ℕ) :
    (-p).coeffN i j k l = -p.coeffN i j k l := by
  unfold coeffN; split_ifs <;> simp

@[simp] theorem coeffN_sub (p q : TrigPoly2 Mβ Mθ R) (i j : Fin 2) (k l : ℕ) :
    (p - q).coeffN i j k l = p.coeffN i j k l - q.coeffN i j k l := by
  unfold coeffN; split_ifs <;> simp

end Linear

/-- Padding keeps the coefficients when the degrees do not drop. -/
theorem coeffN_resize [Zero R] (h₁ : Mβ ≤ Nβ) (h₂ : Mθ ≤ Nθ) (p : TrigPoly2 Mβ Mθ R)
    (i j : Fin 2) (k l : ℕ) : (p.resize : TrigPoly2 Nβ Nθ R).coeffN i j k l = p.coeffN i j k l := by
  by_cases h : k < Nβ + 1 ∧ l < Nθ + 1
  · simp [coeffN, resize, h]
  · rw [coeffN, dite_eq_right_iff.mpr fun h' ↦ absurd h' h, coeffN,
      dite_eq_right_iff.mpr fun h' ↦ absurd ⟨by omega, by omega⟩ h]

/-! ### Products with the coordinate tables -/

section Products

variable [Field R]

theorem coeffN_dβ (p : TrigPoly2 Mβ Mθ R) (i j : Fin 2) (k l : ℕ) :
    p.dβ.coeffN i j k l = (k : R) * (if i = 0 then p.coeffN 1 j k l else -p.coeffN 0 j k l) := by
  unfold coeffN; split_ifs <;> simp_all [dβ]

theorem coeffN_dθ (p : TrigPoly2 Mβ Mθ R) (i j : Fin 2) (k l : ℕ) :
    p.dθ.coeffN i j k l = (l : R) * (if j = 0 then p.coeffN i 1 k l else -p.coeffN i 0 k l) := by
  unfold coeffN; split_ifs <;> simp_all [dθ]

theorem coeffN_sum {ι : Type*} (s : Finset ι) (f : ι → TrigPoly2 Mβ Mθ R) (i j : Fin 2)
    (k l : ℕ) : (∑ x ∈ s, f x).coeffN i j k l = ∑ x ∈ s, (f x).coeffN i j k l := by
  unfold coeffN
  split_ifs
  · exact coeff_sum s f i j _ _
  · simp

/-- Sums over `Fin (n + 1)` of coefficients are sums over `range (n + 1)` of `coeffN`. -/
theorem sum_fin_coeff_eq_sum_range (p : TrigPoly2 Mβ Mθ R) (i j : Fin 2) (l : Fin (Mθ + 1))
    (g : ℕ → R → R) :
    ∑ k : Fin (Mβ + 1), g k (p.coeff i j k l) =
      ∑ k ∈ range (Mβ + 1), g k (p.coeffN i j k l) := by
  rw [← Fin.sum_univ_eq_sum_range (fun k ↦ g k (p.coeffN i j k l))]
  simp

theorem sum_fin_coeff_eq_sum_range_θ (p : TrigPoly2 Mβ Mθ R) (i j : Fin 2) (k : ℕ)
    (g : ℕ → R → R) :
    ∑ l : Fin (Mθ + 1), g l (p.coeffN i j k l) =
      ∑ l ∈ range (Mθ + 1), g l (p.coeffN i j k l) :=
  Fin.sum_univ_eq_sum_range (fun l ↦ g l (p.coeffN i j k l)) _

/-- The frequencies `k'` with `|1 - k'| = K`: `K + 1`, and `0` when `K = 1`. -/
theorem dist_one_eq_iff (K k' : ℕ) :
    Nat.dist 1 k' = K ↔ k' = K + 1 ∨ (K = 1 ∧ k' = 0) := by
  unfold Nat.dist; omega

/-- Sum of the values at the frequencies `k'` with `|1 - k'| = K`. -/
theorem sum_range_ite_dist_one {N : ℕ} (K : ℕ) (g : ℕ → R) (hg : ∀ k, N < k → g k = 0) :
    ∑ k' ∈ range (N + 1), (if K = Nat.dist 1 k' then g k' else 0) =
      g (K + 1) + (if K = 1 then g 0 else 0) := by
  have h : ∀ k', (if K = Nat.dist 1 k' then g k' else 0) =
      (if K + 1 = k' then g k' else 0) + (if K = 1 ∧ 0 = k' then g k' else 0) := by
    intro k'
    unfold Nat.dist
    split_ifs <;> first | (exfalso; omega) | simp
  simp only [h, sum_add_distrib, sum_ite_eq, mem_range]
  congr 1
  · split_ifs with hK
    · rfl
    · exact (hg _ (by omega)).symm
  · by_cases hK : K = 1
    · simp [hK]
    · simp [hK]

/-- Sum of the values at the frequency `k'` with `K = 1 + k'`. -/
theorem sum_range_ite_one_add {N : ℕ} (K : ℕ) (g : ℕ → R) (hg : ∀ k, N < k → g k = 0) :
    ∑ k' ∈ range (N + 1), (if K = 1 + k' then g k' else 0) =
      if 1 ≤ K then g (K - 1) else 0 := by
  have h : ∀ k', (if K = 1 + k' then g k' else 0) = (if K - 1 = k' ∧ 1 ≤ K then g k' else 0) := by
    intro k'
    congr 1
    exact propext (by omega)
  simp only [h, ite_and, sum_ite_eq, mem_range]
  split_ifs with h1 h2 <;> first | rfl | exact (hg _ (by omega)).symm

/-- Sum of the values at the frequency `l'` with `L = l'`. -/
theorem sum_range_ite_eq_self {N : ℕ} (L : ℕ) (g : ℕ → R) (hg : ∀ k, N < k → g k = 0) :
    ∑ l' ∈ range (N + 1), (if L = l' then g l' else 0) = g L := by
  rw [sum_ite_eq]
  split_ifs with h
  · rfl
  · exact (hg _ (by simp at h; omega)).symm

/-- A coefficient of the product of two terms: the four monomials of `mulTerm`. -/
theorem coeffN_mulTerm (i j : Fin 2) (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) (i' j' : Fin 2)
    (k' : Fin (Nβ + 1)) (l' : Fin (Nθ + 1)) (c : R) (I J : Fin 2) (K L : ℕ) :
    (mulTerm i j k l i' j' k' l' c).coeffN I J K L =
      if I = i + i' ∧ J = j + j' then c / 4 *
        ((if K = k + k' then trigSumSign i i' else 0) +
          (if K = Nat.dist k k' then trigDiffSign i i' k k' else 0)) *
        ((if L = l + l' then trigSumSign j j' else 0) +
          (if L = Nat.dist l l' then trigDiffSign j j' l l' else 0)) else 0 := by
  have hk : (k : ℕ) + k' < Mβ + Nβ + 1 := by omega
  have hk' : Nat.dist k k' < Mβ + Nβ + 1 := by unfold Nat.dist; omega
  have hl : (l : ℕ) + l' < Mθ + Nθ + 1 := by omega
  have hl' : Nat.dist l l' < Mθ + Nθ + 1 := by unfold Nat.dist; omega
  unfold coeffN
  by_cases hKL : K < Mβ + Nβ + 1 ∧ L < Mθ + Nθ + 1
  · simp only [hKL, and_self, ↓reduceDIte, mulTerm, coeff_add, monomial, Fin.mk.injEq]
    by_cases hIJ : I = i + i' ∧ J = j + j'
    · simp only [hIJ, true_and, and_self, ↓reduceIte]
      by_cases h1 : K = k + k' <;> by_cases h2 : K = Nat.dist k k' <;>
        by_cases h3 : L = l + l' <;> by_cases h4 : L = Nat.dist l l' <;>
        (first | have e1 := eq_false h1 | have e1 := eq_true h1) <;>
        (first | have e2 := eq_false h2 | have e2 := eq_true h2) <;>
        (first | have e3 := eq_false h3 | have e3 := eq_true h3) <;>
        (first | have e4 := eq_false h4 | have e4 := eq_true h4) <;>
        (try simp only [e1, e2, e3, e4, and_self, and_true, and_false,
          ↓reduceIte, add_zero, zero_add, mul_zero, zero_mul]) <;> ring
    · rcases not_and_or.mp hIJ with h | h <;> simp [h]
  · simp only [hKL, ↓reduceDIte]
    symm
    rcases not_and_or.mp hKL with h | h
    · have e1 : ¬ K = k + k' := by omega
      have e2 : ¬ K = Nat.dist k k' := by omega
      simp [e1, e2]
    · have e1 : ¬ L = l + l' := by omega
      have e2 : ¬ L = Nat.dist l l' := by omega
      simp [e1, e2]

/-- A coefficient of the product with a single term `c · m_{i₀} (k₀ β) m_{j₀} (l₀ θ)`. -/
theorem coeffN_monomial_mul (i₀ j₀ : Fin 2) (k₀ : Fin (Mβ + 1)) (l₀ : Fin (Mθ + 1)) (c : R)
    (q : TrigPoly2 Nβ Nθ R) (I J : Fin 2) (K L : ℕ) :
    ((monomial i₀ j₀ k₀ l₀ c).mul q).coeffN I J K L = c / 4 *
      ∑ k' ∈ range (Nβ + 1), ∑ l' ∈ range (Nθ + 1), q.coeffN (I - i₀) (J - j₀) k' l' *
        ((if K = k₀ + k' then trigSumSign i₀ (I - i₀) else 0) +
          (if K = Nat.dist k₀ k' then trigDiffSign i₀ (I - i₀) k₀ k' else 0)) *
        ((if L = l₀ + l' then trigSumSign j₀ (J - j₀) else 0) +
          (if L = Nat.dist l₀ l' then trigDiffSign j₀ (J - j₀) l₀ l' else 0)) := by
  unfold mul
  simp only [coeffN_sum, coeffN_mulTerm]
  rw [Fintype.sum_eq_single i₀ (fun i hi ↦ by simp [monomial, hi]),
    Fintype.sum_eq_single j₀ (fun j hj ↦ by simp [monomial, hj]),
    Fintype.sum_eq_single k₀ (fun k hk ↦ by simp [monomial, hk]),
    Fintype.sum_eq_single l₀ (fun l hl ↦ by simp [monomial, hl])]
  have hI : ∀ i' : Fin 2, I = i₀ + i' ↔ i' = I - i₀ := fun i' ↦ by
    constructor <;> intro h <;> subst h <;> abel
  have hJ : ∀ j' : Fin 2, J = j₀ + j' ↔ j' = J - j₀ := fun j' ↦ by
    constructor <;> intro h <;> subst h <;> abel
  rw [Fintype.sum_eq_single (I - i₀) (fun i' hi ↦ by simp [(hI i').not.mpr hi]),
    Fintype.sum_eq_single (J - j₀) (fun j' hj ↦ by simp [(hJ j').not.mpr hj])]
  simp only [eq_true ((hI (I - i₀)).mpr rfl), eq_true ((hJ (J - j₀)).mpr rfl), and_self,
    ↓reduceIte, monomial]
  rw [mul_sum, ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun k' _ ↦ ?_
  rw [mul_sum, ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun l' _ ↦ ?_
  simp only [coeffN_coe]
  ring

/-- Collapsing the sum over the frequency of a factor constant in that variable. -/
private theorem sum_range_const {N : ℕ} (L : ℕ) (g : ℕ → R) (hg : ∀ k, N < k → g k = 0) :
    ∑ l' ∈ range (N + 1), g l' * ((if L = 0 + l' then 1 else 0) +
      (if L = Nat.dist 0 l' then 1 else 0)) = 2 * g L := by
  have h : ∀ l', g l' * ((if L = 0 + l' then 1 else 0) + (if L = Nat.dist 0 l' then 1 else 0)) =
      if L = l' then 2 * g l' else 0 := fun l' ↦ by
    rw [zero_add, Nat.dist_zero_left]
    split_ifs <;> ring
  simp only [h]
  exact sum_range_ite_eq_self L _ fun k hk ↦ by rw [hg k hk, mul_zero]

private theorem trigSumSign_zero_left (i : Fin 2) : trigSumSign (0 : Fin 2) i = (1 : R) := by
  simp [trigSumSign]

private theorem trigDiffSign_zero_zero (i : Fin 2) (k : ℕ) :
    trigDiffSign (0 : Fin 2) i 0 k = (1 : R) := by
  simp [trigDiffSign]

/-- The `β`-part of a product with a coordinate table in `β`, summed. -/
private theorem sum_βfactor {N : ℕ} (K : ℕ) (g : ℕ → R) (hg : ∀ k, N < k → g k = 0)
    (s : R) (d : ℕ → R) :
    ∑ k' ∈ range (N + 1), g k' * ((if K = 1 + k' then s else 0) +
      (if K = Nat.dist 1 k' then d k' else 0)) =
      (if 1 ≤ K then s * g (K - 1) else 0) + d (K + 1) * g (K + 1) +
        (if K = 1 then d 0 * g 0 else 0) := by
  have h : ∀ k', g k' * ((if K = 1 + k' then s else 0) + (if K = Nat.dist 1 k' then d k' else 0)) =
      (if K = 1 + k' then s * g k' else 0) + (if K = Nat.dist 1 k' then d k' * g k' else 0) :=
    fun k' ↦ by split_ifs <;> ring
  simp only [h, sum_add_distrib]
  rw [sum_range_ite_one_add K _ fun k hk ↦ by rw [hg k hk, mul_zero],
    sum_range_ite_dist_one K _ fun k hk ↦ by rw [hg k hk, mul_zero]]
  ring

/-- Multiplication by `cos β`: `(p_(K+1) + p_(K-1) + [K = 1] σ p_0) / 2`, `σ = -1` for sines. -/
theorem coeffN_cosβ_mul (p : TrigPoly2 Nβ Nθ R) (I J : Fin 2) (K L : ℕ) :
    ((cosβ : TrigPoly2 1 0 R).mul p).coeffN I J K L =
      (p.coeffN I J (K + 1) L + (if 1 ≤ K then p.coeffN I J (K - 1) L else 0) +
        (if K = 1 then (if I = 0 then 1 else -1) * p.coeffN I J 0 L else 0)) / 2 := by
  rw [cosβ, coeffN_monomial_mul]
  simp only [sub_zero, Fin.val_zero, Fin.val_one, trigSumSign_zero_left, trigDiffSign_zero_zero]
  have hθ : ∀ k', ∑ l' ∈ range (Nθ + 1), p.coeffN I J k' l' *
      ((if K = 1 + k' then (1 : R) else 0) +
        (if K = Nat.dist 1 k' then trigDiffSign (0 : Fin 2) I 1 k' else 0)) *
      ((if L = 0 + l' then 1 else 0) + (if L = Nat.dist 0 l' then 1 else 0)) =
      2 * (p.coeffN I J k' L * ((if K = 1 + k' then 1 else 0) +
        (if K = Nat.dist 1 k' then trigDiffSign (0 : Fin 2) I 1 k' else 0))) := fun k' ↦
    sum_range_const L _ fun l hl ↦ by rw [coeffN_eq_zero_of_le_θ p I J k' (by omega)]; ring
  rw [sum_congr rfl fun k' _ ↦ hθ k', ← mul_sum, sum_βfactor K _
    (fun k hk ↦ coeffN_eq_zero_of_le_β p I J L (by omega))]
  fin_cases I <;>
    simp only [one_div, Fin.zero_eta, Fin.mk_one, Fin.isValue, one_mul, trigDiffSign, zero_ne_one,
      one_ne_zero, and_false, and_true, and_self, ↓reduceIte, le_add_iff_nonneg_left, zero_le,
      nonpos_iff_eq_zero, neg_mul] <;>
    split_ifs <;> (try subst_vars) <;>
    -- no characteristic assumption: in characteristic 2 both `2⁻¹` and `4⁻¹` vanish
    (rcases eq_or_ne (2 : R) 0 with h2 | h2
     · have h4 : (4 : R) = 0 := by rw [show (4 : R) = 2 * 2 by norm_num, h2, zero_mul]
       simp [h2, h4]
     · have h4 : (4 : R) ≠ 0 := by
         rw [show (4 : R) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
       field_simp
       ring)

/-- Multiplication by `sin β`. On cosines (`I = 0`, from sines of `p`):
`(p_(K+1) - p_(K-1) + [K = 1] p_0) / 2`; on sines (`I = 1`, from cosines of `p`):
`(p_(K-1) - p_(K+1) + [K = 0] p_1 + [K = 1] p_0) / 2` with the sign `+` at `K = 0`. -/
theorem coeffN_sinβ_mul (p : TrigPoly2 Nβ Nθ R) (I J : Fin 2) (K L : ℕ) :
    ((sinβ : TrigPoly2 1 0 R).mul p).coeffN I J K L =
      if I = 0 then
        (p.coeffN 1 J (K + 1) L - (if 1 ≤ K then p.coeffN 1 J (K - 1) L else 0) +
          (if K = 1 then p.coeffN 1 J 0 L else 0)) / 2
      else
        ((if 1 ≤ K then p.coeffN 0 J (K - 1) L else 0) +
          (if K = 0 then 1 else -1) * p.coeffN 0 J (K + 1) L +
          (if K = 1 then p.coeffN 0 J 0 L else 0)) / 2 := by
  rw [sinβ, coeffN_monomial_mul]
  simp only [sub_zero, Fin.val_zero, Fin.val_one, trigSumSign_zero_left, trigDiffSign_zero_zero]
  have hθ : ∀ k', ∑ l' ∈ range (Nθ + 1), p.coeffN (I - 1) J k' l' *
      ((if K = 1 + k' then trigSumSign (1 : Fin 2) (I - 1) else 0) +
        (if K = Nat.dist 1 k' then trigDiffSign (1 : Fin 2) (I - 1) 1 k' else 0)) *
      ((if L = 0 + l' then 1 else 0) + (if L = Nat.dist 0 l' then 1 else 0)) =
      2 * (p.coeffN (I - 1) J k' L * ((if K = 1 + k' then trigSumSign (1 : Fin 2) (I - 1) else 0) +
        (if K = Nat.dist 1 k' then trigDiffSign (1 : Fin 2) (I - 1) 1 k' else 0))) := fun k' ↦
    sum_range_const L _ fun l hl ↦ by rw [coeffN_eq_zero_of_le_θ p _ J k' (by omega)]; ring
  rw [sum_congr rfl fun k' _ ↦ hθ k', ← mul_sum, sum_βfactor K _
    (fun k hk ↦ coeffN_eq_zero_of_le_β p _ J L (by omega))]
  have h0 : (0 : Fin 2) - 1 = 1 := by decide
  fin_cases I <;>
    simp only [one_div, trigSumSign, Fin.isValue, Fin.zero_eta, Fin.mk_one, h0, and_self,
      ↓reduceIte, neg_mul, one_mul, trigDiffSign, one_ne_zero, zero_ne_one, and_true, and_false,
      sub_self, add_le_iff_nonpos_left, nonpos_iff_eq_zero, ite_mul, zero_le] <;>
    split_ifs <;> (try subst_vars) <;>
    -- no characteristic assumption: in characteristic 2 both `2⁻¹` and `4⁻¹` vanish
    (rcases eq_or_ne (2 : R) 0 with h2 | h2
     · have h4 : (4 : R) = 0 := by rw [show (4 : R) = 2 * 2 by norm_num, h2, zero_mul]
       simp [h2, h4]
     · have h4 : (4 : R) ≠ 0 := by
         rw [show (4 : R) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
       field_simp
       ring)

/-- Multiplication by `cos θ`: `(p_(L+1) + p_(L-1) + [L = 1] σ p_0) / 2` in the second
frequency, `σ = -1` for sines. -/
theorem coeffN_cosθ_mul (p : TrigPoly2 Nβ Nθ R) (I J : Fin 2) (K L : ℕ) :
    ((cosθ : TrigPoly2 0 1 R).mul p).coeffN I J K L =
      (p.coeffN I J K (L + 1) + (if 1 ≤ L then p.coeffN I J K (L - 1) else 0) +
        (if L = 1 then (if J = 0 then 1 else -1) * p.coeffN I J K 0 else 0)) / 2 := by
  rw [cosθ, coeffN_monomial_mul]
  simp only [sub_zero, Fin.val_zero, Fin.val_one, trigSumSign_zero_left, trigDiffSign_zero_zero]
  rw [sum_comm]
  have hβ : ∀ l', ∑ k' ∈ range (Nβ + 1), p.coeffN I J k' l' *
      ((if K = 0 + k' then (1 : R) else 0) + (if K = Nat.dist 0 k' then 1 else 0)) *
      ((if L = 1 + l' then 1 else 0) +
        (if L = Nat.dist 1 l' then trigDiffSign (0 : Fin 2) J 1 l' else 0)) =
      2 * (p.coeffN I J K l' * ((if L = 1 + l' then 1 else 0) +
        (if L = Nat.dist 1 l' then trigDiffSign (0 : Fin 2) J 1 l' else 0))) := fun l' ↦ by
    rw [← sum_range_const (N := Nβ) K (fun k' ↦ p.coeffN I J k' l' *
        ((if L = 1 + l' then 1 else 0) +
        (if L = Nat.dist 1 l' then trigDiffSign (0 : Fin 2) J 1 l' else 0)))
      fun k hk ↦ by rw [coeffN_eq_zero_of_le_β p I J (k := k) l' (by omega)]; ring]
    exact sum_congr rfl fun k' _ ↦ by ring
  rw [sum_congr rfl fun l' _ ↦ hβ l', ← mul_sum, sum_βfactor L _
    (fun l hl ↦ coeffN_eq_zero_of_le_θ p I J K (l := l) (by omega))]
  fin_cases J <;>
    simp only [one_div, Fin.zero_eta, Fin.mk_one, Fin.isValue, one_mul, trigDiffSign, zero_ne_one,
      one_ne_zero, and_false, and_true, and_self, ↓reduceIte, le_add_iff_nonneg_left, zero_le,
      nonpos_iff_eq_zero, neg_mul] <;>
    split_ifs <;> (try subst_vars) <;>
    -- no characteristic assumption: in characteristic 2 both `2⁻¹` and `4⁻¹` vanish
    (rcases eq_or_ne (2 : R) 0 with h2 | h2
     · have h4 : (4 : R) = 0 := by rw [show (4 : R) = 2 * 2 by norm_num, h2, zero_mul]
       simp [h2, h4]
     · have h4 : (4 : R) ≠ 0 := by
         rw [show (4 : R) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
       field_simp
       ring)

end Products

end PDE.Analysis.TrigPoly2
