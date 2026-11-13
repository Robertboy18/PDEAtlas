/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2Calculus
public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2Separable

/-!
# Products with one mode and replaced modes

By the product-to-sum formula, the product of the mode `trigMode i₀ (k₀ x)` with
`trigMode i (k x)` is `(σ trigMode (i₀ + i) ((k₀ + k) x) + δ trigMode (i₀ + i) (|k₀ - k| x)) / 2`
with the signs `σ = trigSumSign i₀ i` and `δ = trigDiffSign i₀ i k₀ k`. The same combination of
replaced modes is `mulModes i₀ k₀ A`, and the value with replaced modes of the product of a
single-term table with a table `p` is that of `p` with the transformed modes in both variables
(`approxEval_monomial_mul`). For the coordinate tables, multiplication by `cos β` and `sin β`
transforms the modes in `β` only and multiplication by `cos θ` the modes in `θ` only
(`approxEval_cosβ_mul`, `approxEval_sinβ_mul`, `approxEval_cosθ_mul`); padding a table changes
nothing (`approxEval_resize`). With the derivative and quotient transforms of
`TrigPoly2Separable`, the value with replaced modes of every table built from these operations
is that of its factors with composed mode transforms.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.TrigPoly2

open Finset

variable {Mβ Mθ Nβ Nθ : ℕ} {R : Type} [Field R] [Algebra R ℝ]

/-- The modes after multiplication by `trigMode i₀ (k₀ x)`. -/
def mulModes (i₀ : Fin 2) (k₀ : ℕ) (A : Fin 2 → ℕ → ℝ) : Fin 2 → ℕ → ℝ :=
  fun i k ↦ (trigSumSign i₀ i * A (i₀ + i) (k₀ + k) +
    trigDiffSign i₀ i k₀ k * A (i₀ + i) (Nat.dist k₀ k)) / 2

/-- Multiplication by the constant mode `cos (0 x)` leaves the modes unchanged. -/
@[simp] theorem mulModes_zero_zero (A : Fin 2 → ℕ → ℝ) : mulModes 0 0 A = A := by
  funext i k
  fin_cases i <;> simp [mulModes, trigSumSign, trigDiffSign, Nat.dist]

/-- Multiplication by `cos x` on the cosine modes: `cos x cos (k x) = (cos ((k + 1) x) +
cos ((k - 1) x)) / 2`. -/
theorem mulModes_cos_cos (A : Fin 2 → ℕ → ℝ) (k : ℕ) :
    mulModes 0 1 A 0 k = (A 0 (k + 1) + A 0 (Nat.dist 1 k)) / 2 := by
  simp [mulModes, trigSumSign, trigDiffSign, add_comm 1 k]

/-- Multiplication by `sin x` on the sine modes: `sin x sin (k x) = (cos ((k - 1) x) -
cos ((k + 1) x)) / 2`. -/
theorem mulModes_sin_sin (A : Fin 2 → ℕ → ℝ) (k : ℕ) :
    mulModes 1 1 A 1 k = (A 0 (Nat.dist 1 k) - A 0 (k + 1)) / 2 := by
  simp [mulModes, trigSumSign, trigDiffSign, add_comm 1 k, show (1 : Fin 2) + 1 = 0 from rfl]
  ring

theorem approxEval_mulTerm (i j : Fin 2) (k : Fin (Nβ + 1)) (l : Fin (Nθ + 1)) (i' j' : Fin 2)
    (k' : Fin (Mβ + 1)) (l' : Fin (Mθ + 1)) (c : R) (A B : Fin 2 → ℕ → ℝ) :
    (mulTerm i j k l i' j' k' l' c).approxEval A B =
      algebraMap R ℝ c * mulModes i k A i' k' * mulModes j l B j' l' := by
  simp only [mulTerm, approxEval_add, approxEval_monomial, map_div₀, _root_.map_mul,
    map_trigSumSign, map_trigDiffSign, map_ofNat, mulModes]
  ring

omit [Algebra R ℝ] in
private theorem monomial_coeff_mul_eq (i₀ j₀ : Fin 2) (k₀ : Fin (Nβ + 1)) (l₀ : Fin (Nθ + 1))
    (c : R) (p : TrigPoly2 Mβ Mθ R) (i j : Fin 2) (k : Fin (Nβ + 1)) (l : Fin (Nθ + 1))
    (i' j' : Fin 2) (k' : Fin (Mβ + 1)) (l' : Fin (Mθ + 1)) :
    (monomial i₀ j₀ k₀ l₀ c).coeff i j k l * p.coeff i' j' k' l' =
      if i = i₀ ∧ j = j₀ ∧ k = k₀ ∧ l = l₀ then c * p.coeff i' j' k' l' else 0 := by
  simp only [monomial]
  split_ifs <;> simp

/-- **Products with a single term.** The value with replaced modes of `monomial · p` is the
coefficient times the value of `p` with the modes transformed by `mulModes` in both
variables. -/
theorem approxEval_monomial_mul (i₀ j₀ : Fin 2) (k₀ : Fin (Nβ + 1)) (l₀ : Fin (Nθ + 1)) (c : R)
    (p : TrigPoly2 Mβ Mθ R) (A B : Fin 2 → ℕ → ℝ) :
    ((monomial i₀ j₀ k₀ l₀ c).mul p).approxEval A B =
      algebraMap R ℝ c * p.approxEval (mulModes i₀ k₀ A) (mulModes j₀ l₀ B) := by
  simp only [mul, approxEval_sum, approxEval_mulTerm, monomial_coeff_mul_eq]
  rw [sum_eq_single i₀ (fun i _ hi ↦ by simp [hi]) (by simp)]
  rw [sum_eq_single j₀ (fun j _ hj ↦ by simp [hj]) (by simp)]
  rw [sum_eq_single k₀ (fun k _ hk ↦ by simp [hk]) (by simp)]
  rw [sum_eq_single l₀ (fun l _ hl ↦ by simp [hl]) (by simp)]
  simp only [and_self, ite_true, approxEval, mul_sum, _root_.map_mul]
  refine sum_congr rfl fun i' _ ↦ sum_congr rfl fun j' _ ↦ sum_congr rfl fun k' _ ↦
    sum_congr rfl fun l' _ ↦ ?_
  ring

/-- Multiplication by `cos β` transforms the modes in `β`. -/
theorem approxEval_cosβ_mul (p : TrigPoly2 Mβ Mθ R) (A B : Fin 2 → ℕ → ℝ) :
    ((cosβ : TrigPoly2 1 0 R).mul p).approxEval A B = p.approxEval (mulModes 0 1 A) B := by
  rw [cosβ, approxEval_monomial_mul]
  simp

/-- Multiplication by `sin β` transforms the modes in `β`. -/
theorem approxEval_sinβ_mul (p : TrigPoly2 Mβ Mθ R) (A B : Fin 2 → ℕ → ℝ) :
    ((sinβ : TrigPoly2 1 0 R).mul p).approxEval A B = p.approxEval (mulModes 1 1 A) B := by
  rw [sinβ, approxEval_monomial_mul]
  simp

/-- Multiplication by `cos θ` transforms the modes in `θ`. -/
theorem approxEval_cosθ_mul (p : TrigPoly2 Mβ Mθ R) (A B : Fin 2 → ℕ → ℝ) :
    ((cosθ : TrigPoly2 0 1 R).mul p).approxEval A B = p.approxEval A (mulModes 0 1 B) := by
  rw [cosθ, approxEval_monomial_mul]
  simp

theorem approxEval_neg (p : TrigPoly2 Mβ Mθ R) (A B : Fin 2 → ℕ → ℝ) :
    (-p).approxEval A B = -p.approxEval A B := by
  simp only [approxEval, coeff_neg, _root_.map_neg, neg_mul, sum_neg_distrib]

theorem approxEval_sub (p q : TrigPoly2 Mβ Mθ R) (A B : Fin 2 → ℕ → ℝ) :
    (p - q).approxEval A B = p.approxEval A B - q.approxEval A B := by
  rw [sub_eq_add_neg, approxEval_add, approxEval_neg, sub_eq_add_neg]

/-- Padding a table to larger degrees keeps its value with replaced modes. -/
theorem approxEval_resize (p : TrigPoly2 Mβ Mθ R) (h₁ : Mβ ≤ Nβ) (h₂ : Mθ ≤ Nθ)
    (A B : Fin 2 → ℕ → ℝ) : (p.resize : TrigPoly2 Nβ Nθ R).approxEval A B = p.approxEval A B := by
  rw [approxEval_eq_sum_range, approxEval_eq_sum_range]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  have hzero : ∀ k l, ¬(k < Mβ + 1 ∧ l < Mθ + 1) → p.coeffN i j k l = 0 := by
    intro k l h
    rw [coeffN, dite_eq_right_iff]
    exact fun h' ↦ absurd h' h
  have hcoeff : ∀ k ∈ range (Nβ + 1), ∀ l ∈ range (Nθ + 1),
      (p.resize : TrigPoly2 Nβ Nθ R).coeffN i j k l = p.coeffN i j k l := by
    intro k hk l hl
    simp only [mem_range] at hk hl
    simp [coeffN, resize, hk, hl]
  have hk : range (Mβ + 1) ⊆ range (Nβ + 1) := range_subset_range.mpr (by omega)
  have hl : range (Mθ + 1) ⊆ range (Nθ + 1) := range_subset_range.mpr (by omega)
  rw [sum_congr rfl fun k hk' ↦ sum_congr rfl fun l hl' ↦ by rw [hcoeff k hk' l hl']]
  symm
  rw [sum_subset hk fun k _ hk' ↦ sum_eq_zero fun l _ ↦ by
    rw [hzero k l fun h ↦ hk' (mem_range.mpr h.1)]; simp]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [sum_subset hl fun l _ hl' ↦ by rw [hzero k l fun h ↦ hl' (mem_range.mpr h.2)]; simp]

end PDE.Analysis.TrigPoly2
