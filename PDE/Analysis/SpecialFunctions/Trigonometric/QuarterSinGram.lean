/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.Analysis.SpecialFunctions.Trigonometric.CosineQuadrature

/-!
# Gram sums of the quarter sine rule in exponential coefficients

The sine rule on `[0, π/2]` with nodes `θ_n = nπ/(2P)` gives the moments
`∑_n w_n cos (2kθ_n) = μ_k = 1 / (1 - 4k²)` for `k ≤ P` (`sum_quarterSinWeight_mul_cos`); for an
even integer `u` with `|u| ≤ 2P` the node sum of `cos (uθ)` is `ν_u = μ_{|u|/2}`
(`quarterSinLaurentMoment`, `sum_quarterSinWeight_mul_cos_int`).

A cosine series is written with symmetric coefficients `φ_i` at the frequencies `i - T`,
`i ≤ 2T` (`φ (2T - i) = φ i`), a sine series with antisymmetric ones. When the frequencies of
two such series have the same parity and `T ≤ P`, the node sum of their product is the
convolution of the coefficients against `ν`:

* `∑_n w_n (∑_i φ_i cos ((i-T)θ_n)) (∑_j ψ_j cos ((j-T)θ_n)) = ∑_{i,j} φ_i ψ_j ν_{i+j-2T}`
  (`sum_quarterSinWeight_mul_cosSum_mul_cosSum`),
* the same with sines and a minus sign (`sum_quarterSinWeight_mul_sinSum_mul_sinSum`).

At a node `β_j` of a two-variable rule the inner sum over the `θ` nodes is therefore one packed
convolution of the coefficient rows of the two tables at `β_j`, with no values at the nodes.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open CAS.Analysis
open Finset

/-- The node sum `ν_u = μ_{|u|/2}` of `cos (uθ)`, `μ_k = 1 / (1 - 4k²)`, for even `u`. -/
def quarterSinLaurentMoment (u : ℤ) : ℝ := 1 / (1 - 4 * ((u.natAbs / 2 : ℕ) : ℝ) ^ 2)

/-- The sine rule integrates `cos (uθ)` for even `u` with `|u| ≤ 2P`. -/
theorem sum_quarterSinWeight_mul_cos_int {P : ℕ} (hP : 0 < P) {u : ℤ} (hu : Even u)
    (h : u.natAbs ≤ 2 * P) :
    ∑ n : Fin (P + 1), quarterSinWeight P n * Real.cos (u * (n * Real.pi / (2 * P))) =
      quarterSinLaurentMoment u := by
  obtain ⟨k, rfl⟩ := hu
  have hk : (k + k).natAbs / 2 = k.natAbs := by omega
  have hc : ∀ x : ℝ, Real.cos (((k + k : ℤ) : ℝ) * x) = Real.cos (2 * (k.natAbs : ℕ) * x) := by
    intro x
    rcases Int.natAbs_eq k with h | h
    · rw [show ((k + k : ℤ) : ℝ) = 2 * ((k.natAbs : ℤ) : ℝ) by rw [← h]; push_cast; ring]
      norm_cast
    · rw [show ((k + k : ℤ) : ℝ) = -(2 * ((k.natAbs : ℤ) : ℝ)) by
        conv_lhs => rw [h]
        push_cast; ring, neg_mul, Real.cos_neg]
      norm_cast
  rw [sum_congr rfl fun n _ ↦ by rw [hc], sum_quarterSinWeight_mul_cos hP (by omega),
    quarterSinLaurentMoment, hk]

/-- If `i` and `j` have the same parity, then `(i + j) - 2T` and `i - j` are even integers. -/
theorem even_int_of_mod {T r i j : ℕ} (hi : i % 2 = r) (hj : j % 2 = r) :
    Even (((i + j : ℕ) : ℤ) - 2 * T) ∧ Even ((i : ℤ) - j) := by
  constructor
  · refine ⟨((i + j : ℕ) : ℤ) / 2 - T, ?_⟩
    have : ((i + j : ℕ) : ℤ) % 2 = 0 := by omega
    omega
  · refine ⟨((i : ℤ) - j) / 2, ?_⟩
    omega

private theorem sum_reflect_moment {T : ℕ} (ψ : ℕ → ℝ) (s : ℝ)
    (hψ : ∀ j < 2 * T + 1, ψ (2 * T - j) = s * ψ j) (i : ℕ) :
    ∑ j ∈ range (2 * T + 1), ψ j * quarterSinLaurentMoment ((i : ℤ) - j) =
      s * ∑ j ∈ range (2 * T + 1), ψ j * quarterSinLaurentMoment (((i + j : ℕ) : ℤ) - 2 * T) := by
  rw [← sum_range_reflect, mul_sum]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [mem_range] at hj
  rw [show 2 * T + 1 - 1 - j = 2 * T - j by omega, hψ j hj,
    show ((i : ℤ) - ((2 * T - j : ℕ) : ℤ)) = ((i + j : ℕ) : ℤ) - 2 * T by
      rw [Nat.cast_sub (by omega)]; push_cast; ring]
  ring

private theorem sum_node_mul_sum_mul_sum {P K : ℕ} (φ ψ : ℕ → ℝ) (f g : ℕ → ℝ → ℝ)
    (G : ℕ → ℕ → ℝ)
    (h : ∀ i < K, ∀ j < K, φ i ≠ 0 → ψ j ≠ 0 →
      ∑ n : Fin (P + 1), quarterSinWeight P n * (f i (n * Real.pi / (2 * P)) *
        g j (n * Real.pi / (2 * P))) = G i j) :
    ∑ n : Fin (P + 1), quarterSinWeight P n *
      ((∑ i ∈ range K, φ i * f i (n * Real.pi / (2 * P))) *
        ∑ j ∈ range K, ψ j * g j (n * Real.pi / (2 * P))) =
      ∑ i ∈ range K, ∑ j ∈ range K, φ i * ψ j * G i j := by
  have hexp : ∀ n : Fin (P + 1), quarterSinWeight P n *
      ((∑ i ∈ range K, φ i * f i (n * Real.pi / (2 * P))) *
        ∑ j ∈ range K, ψ j * g j (n * Real.pi / (2 * P))) =
      ∑ i ∈ range K, ∑ j ∈ range K, φ i * ψ j * (quarterSinWeight P n *
        (f i (n * Real.pi / (2 * P)) * g j (n * Real.pi / (2 * P)))) := by
    intro n
    rw [sum_mul_sum, mul_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [mul_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    ring
  rw [sum_congr rfl fun n _ ↦ hexp n, sum_comm]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [sum_comm]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [← mul_sum]
  by_cases hφ : φ i = 0
  · simp [hφ]
  by_cases hψ : ψ j = 0
  · simp [hψ]
  rw [h i (mem_range.mp hi) j (mem_range.mp hj) hφ hψ]

/-- The node sum of the product of two cosine series with symmetric coefficients `φ`, `ψ` at the
frequencies `i - T`, all of one parity, is `∑_{i,j} φ_i ψ_j ν_{i+j-2T}` when `T ≤ P`. -/
theorem sum_quarterSinWeight_mul_cosSum_mul_cosSum {P T r : ℕ} (hP : 0 < P) (hT : T ≤ P)
    (φ ψ : ℕ → ℝ) (hφ : ∀ i, φ i ≠ 0 → i % 2 = r) (hψ : ∀ j, ψ j ≠ 0 → j % 2 = r)
    (hsym : ∀ j < 2 * T + 1, ψ (2 * T - j) = ψ j) :
    ∑ n : Fin (P + 1), quarterSinWeight P n *
      ((∑ i ∈ range (2 * T + 1), φ i * Real.cos (((i : ℝ) - T) * (n * Real.pi / (2 * P)))) *
        ∑ j ∈ range (2 * T + 1), ψ j * Real.cos (((j : ℝ) - T) * (n * Real.pi / (2 * P)))) =
      ∑ i ∈ range (2 * T + 1), ∑ j ∈ range (2 * T + 1),
        φ i * ψ j * quarterSinLaurentMoment (((i + j : ℕ) : ℤ) - 2 * T) := by
  refine (sum_node_mul_sum_mul_sum φ ψ (fun i x ↦ Real.cos (((i : ℝ) - T) * x))
    (fun j x ↦ Real.cos (((j : ℝ) - T) * x))
    (fun i j ↦ (quarterSinLaurentMoment (((i + j : ℕ) : ℤ) - 2 * T) +
      quarterSinLaurentMoment ((i : ℤ) - j)) / 2) ?_).trans ?_
  rotate_left
  · refine sum_congr rfl fun i _ ↦ ?_
    have h := sum_reflect_moment ψ 1 (fun j hj ↦ by rw [hsym j hj, one_mul]) i
    rw [one_mul] at h
    simp only [mul_div_assoc', mul_add, add_div, sum_add_distrib, mul_assoc, ← mul_sum,
      ← sum_div] at h ⊢
    rw [show ∑ j ∈ range (2 * T + 1), ψ j * quarterSinLaurentMoment ((i : ℤ) - j) =
      ∑ j ∈ range (2 * T + 1), ψ j * quarterSinLaurentMoment (((i + j : ℕ) : ℤ) - 2 * T) from h]
    ring
  · intro i hi j hj hφi hψj
    obtain ⟨he₁, he₂⟩ := even_int_of_mod (T := T) (hφ i hφi) (hψ j hψj)
    have hpt : ∀ x : ℝ, Real.cos (((i : ℝ) - T) * x) * Real.cos (((j : ℝ) - T) * x) =
        (Real.cos (((((i + j : ℕ) : ℤ) - 2 * T : ℤ) : ℝ) * x) +
          Real.cos ((((i : ℤ) - j : ℤ) : ℝ) * x)) / 2 := by
      intro x
      rw [show (((((i + j : ℕ) : ℤ) - 2 * T : ℤ) : ℝ)) * x =
          ((i : ℝ) - T) * x + ((j : ℝ) - T) * x by push_cast; ring,
        show ((((i : ℤ) - j : ℤ) : ℝ)) * x = ((i : ℝ) - T) * x - ((j : ℝ) - T) * x by
          push_cast; ring, Real.cos_add, Real.cos_sub]
      ring
    have h1 := sum_quarterSinWeight_mul_cos_int hP he₁ (by omega)
    have h2 := sum_quarterSinWeight_mul_cos_int hP he₂ (by omega)
    have hsplit : ∀ w A B : ℝ, w * ((A + B) / 2) = w * A / 2 + w * B / 2 := fun _ _ _ ↦ by ring
    rw [sum_congr rfl fun n _ ↦ by rw [hpt, hsplit], sum_add_distrib, ← sum_div, ← sum_div, h1,
      h2, add_div]

/-- The node sum of the product of two sine series with antisymmetric coefficients `φ`, `ψ` at
the frequencies `i - T`, all of one parity, is `-∑_{i,j} φ_i ψ_j ν_{i+j-2T}` when `T ≤ P`. -/
theorem sum_quarterSinWeight_mul_sinSum_mul_sinSum {P T r : ℕ} (hP : 0 < P) (hT : T ≤ P)
    (φ ψ : ℕ → ℝ) (hφ : ∀ i, φ i ≠ 0 → i % 2 = r) (hψ : ∀ j, ψ j ≠ 0 → j % 2 = r)
    (hanti : ∀ j < 2 * T + 1, ψ (2 * T - j) = -ψ j) :
    ∑ n : Fin (P + 1), quarterSinWeight P n *
      ((∑ i ∈ range (2 * T + 1), φ i * Real.sin (((i : ℝ) - T) * (n * Real.pi / (2 * P)))) *
        ∑ j ∈ range (2 * T + 1), ψ j * Real.sin (((j : ℝ) - T) * (n * Real.pi / (2 * P)))) =
      -∑ i ∈ range (2 * T + 1), ∑ j ∈ range (2 * T + 1),
        φ i * ψ j * quarterSinLaurentMoment (((i + j : ℕ) : ℤ) - 2 * T) := by
  refine (sum_node_mul_sum_mul_sum φ ψ (fun i x ↦ Real.sin (((i : ℝ) - T) * x))
    (fun j x ↦ Real.sin (((j : ℝ) - T) * x))
    (fun i j ↦ (quarterSinLaurentMoment ((i : ℤ) - j) -
      quarterSinLaurentMoment (((i + j : ℕ) : ℤ) - 2 * T)) / 2) ?_).trans ?_
  rotate_left
  · rw [← sum_neg_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    have h := sum_reflect_moment ψ (-1) (fun j hj ↦ by rw [hanti j hj, neg_one_mul]) i
    simp only [mul_div_assoc', mul_sub, sub_div, sum_sub_distrib, mul_assoc, ← mul_sum,
      ← sum_div] at h ⊢
    rw [show ∑ j ∈ range (2 * T + 1), ψ j * quarterSinLaurentMoment ((i : ℤ) - j) =
      -1 * ∑ j ∈ range (2 * T + 1), ψ j * quarterSinLaurentMoment (((i + j : ℕ) : ℤ) - 2 * T)
      from h]
    ring
  · intro i hi j hj hφi hψj
    obtain ⟨he₁, he₂⟩ := even_int_of_mod (T := T) (hφ i hφi) (hψ j hψj)
    have hpt : ∀ x : ℝ, Real.sin (((i : ℝ) - T) * x) * Real.sin (((j : ℝ) - T) * x) =
        (Real.cos ((((i : ℤ) - j : ℤ) : ℝ) * x) -
          Real.cos (((((i + j : ℕ) : ℤ) - 2 * T : ℤ) : ℝ) * x)) / 2 := by
      intro x
      rw [show (((((i + j : ℕ) : ℤ) - 2 * T : ℤ) : ℝ)) * x =
          ((i : ℝ) - T) * x + ((j : ℝ) - T) * x by push_cast; ring,
        show ((((i : ℤ) - j : ℤ) : ℝ)) * x = ((i : ℝ) - T) * x - ((j : ℝ) - T) * x by
          push_cast; ring, Real.cos_add, Real.cos_sub]
      ring
    have h1 := sum_quarterSinWeight_mul_cos_int hP he₁ (by omega)
    have h2 := sum_quarterSinWeight_mul_cos_int hP he₂ (by omega)
    have hsplit : ∀ w A B : ℝ, w * ((A - B) / 2) = w * A / 2 - w * B / 2 := fun _ _ _ ↦ by ring
    rw [sum_congr rfl fun n _ ↦ by rw [hpt, hsplit], sum_sub_distrib, ← sum_div, ← sum_div, h1,
      h2, sub_div]

end PDE.Analysis
