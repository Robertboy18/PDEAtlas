/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigLaurent

/-!
# Gram sums of a cosine rule with any moments in exponential coefficients

`QuarterSinGram` pairs two series in `θ` by the quarter sine rule. The same holds for the
interpolatory cosine rule of any moments `μ` on the nodes `θ_n = nπ/(2P)`: its weights
`cosineRuleWeight P μ n` reproduce `∑_n w_n cos (uθ_n) = μ_{|u|/2}` for every even `u` with
`|u| ≤ 2P` (`sum_cosineRuleWeight_mul_cos_int`), so the node sum of the product of two cosine
(sine) series with symmetric (antisymmetric) coefficients of one parity is the convolution of
the coefficients against `u ↦ μ_{|u|/2}` (`sum_cosineRuleWeight_mul_laurentCos`,
`sum_cosineRuleWeight_mul_laurentSin`). A pairing computed with rounded moments `μ̃` is thus an
exact node sum with the weights `cosineRuleWeight P μ̃`, which differ from the weights of the
exact moments by `cosineRuleWeight P (μ̃ - μ)` (`cosineRuleWeight_sub`,
`abs_cosineRuleWeight_le`).
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open CAS.Analysis
open Finset

/-- The moment `μ_{|u|/2}` of the even frequency `u`. -/
def cosineRuleLaurentMoment (μ : ℕ → ℝ) (u : ℤ) : ℝ := μ (u.natAbs / 2)

/-- The sum `∑_{i,j} φ_i ψ_j ν_{i+j-2T}`, with the sign `-1` for sine series. -/
def laurentGramWith (ν : ℤ → ℝ) (isCos : Bool) (T : ℕ) (φ ψ : ℕ → ℝ) : ℝ :=
  cond isCos 1 (-1) * ∑ i ∈ range (2 * T + 1), ∑ j ∈ range (2 * T + 1),
    φ i * ψ j * ν (((i + j : ℕ) : ℤ) - 2 * T)

theorem cosineRuleWeight_sub (N : ℕ) (μ μ' : ℕ → ℝ) (n : ℕ) :
    cosineRuleWeight N μ n - cosineRuleWeight N μ' n = cosineRuleWeight N (μ - μ') n := by
  simp only [cosineRuleWeight, Pi.sub_apply, ← mul_sub, ← sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun k _ ↦ ?_
  ring

/-- `|w_n| ≤ (2/N) h_n ∑_k h_k |μ_k|`. -/
theorem abs_cosineRuleWeight_le {N : ℕ} (μ : ℕ → ℝ) (n : ℕ) :
    |cosineRuleWeight N μ n| ≤
      2 / N * trapezoidFactor N n * ∑ k ∈ range (N + 1), trapezoidFactor N k * |μ k| := by
  have hh : ∀ k, 0 ≤ trapezoidFactor N k := fun k ↦ by
    unfold trapezoidFactor; split_ifs <;> norm_num
  unfold cosineRuleWeight
  rw [abs_mul, abs_of_nonneg (mul_nonneg (div_nonneg zero_le_two (Nat.cast_nonneg N)) (hh n))]
  refine mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans
    (sum_le_sum fun k _ ↦ ?_)) (mul_nonneg (div_nonneg zero_le_two (Nat.cast_nonneg N)) (hh n))
  rw [abs_mul, abs_mul, abs_of_nonneg (hh k)]
  exact mul_le_of_le_one_right (mul_nonneg (hh k) (abs_nonneg _)) (Real.abs_cos_le_one _)

/-- The cosine rule integrates `cos (2kθ)` on the nodes `θ_n = nπ/(2P)` for `k ≤ P`. -/
theorem sum_cosineRuleWeight_mul_cos_two_mul {P k : ℕ} (hP : 0 < P) (hk : k ≤ P)
    (μ : ℕ → ℝ) :
    ∑ n : Fin (P + 1), cosineRuleWeight P μ n * Real.cos (2 * k * (n * Real.pi / (2 * P))) =
      μ k := by
  rw [Fin.sum_univ_eq_sum_range (fun n ↦ cosineRuleWeight P μ n *
    Real.cos (2 * k * (n * Real.pi / (2 * P))))]
  have h : ∀ n : ℕ, cosineRuleWeight P μ n * Real.cos (2 * k * (n * Real.pi / (2 * P))) =
      cosineRuleWeight P μ n * Real.cos (n * (k * Real.pi / P)) := fun n ↦ by
    rw [show 2 * (k : ℝ) * (n * Real.pi / (2 * P)) = n * (k * Real.pi / P) by
      have : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
      field_simp]
  rw [sum_congr rfl fun n _ ↦ h n, sum_cosineRuleWeight_mul_cos hP μ hk]

/-- The cosine rule integrates `cos (uθ)` for even `u` with `|u| ≤ 2P`. -/
theorem sum_cosineRuleWeight_mul_cos_int {P : ℕ} (hP : 0 < P) (μ : ℕ → ℝ) {u : ℤ}
    (hu : Even u) (h : u.natAbs ≤ 2 * P) :
    ∑ n : Fin (P + 1), cosineRuleWeight P μ n * Real.cos (u * (n * Real.pi / (2 * P))) =
      cosineRuleLaurentMoment μ u := by
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
  rw [sum_congr rfl fun n _ ↦ by rw [hc], sum_cosineRuleWeight_mul_cos_two_mul hP (by omega),
    cosineRuleLaurentMoment, hk]

private theorem sum_reflect_moment' {T : ℕ} (ν : ℤ → ℝ) (ψ : ℕ → ℝ) (s : ℝ)
    (hψ : ∀ j < 2 * T + 1, ψ (2 * T - j) = s * ψ j) (i : ℕ) :
    ∑ j ∈ range (2 * T + 1), ψ j * ν ((i : ℤ) - j) =
      s * ∑ j ∈ range (2 * T + 1), ψ j * ν (((i + j : ℕ) : ℤ) - 2 * T) := by
  rw [← sum_range_reflect, mul_sum]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [mem_range] at hj
  rw [show 2 * T + 1 - 1 - j = 2 * T - j by omega, hψ j hj,
    show ((i : ℤ) - ((2 * T - j : ℕ) : ℤ)) = ((i + j : ℕ) : ℤ) - 2 * T by
      rw [Nat.cast_sub (by omega)]; push_cast; ring]
  ring

private theorem sum_weight_mul_sum_mul_sum {P K : ℕ} (w : ℕ → ℝ) (φ ψ : ℕ → ℝ)
    (f g : ℕ → ℝ → ℝ) (G : ℕ → ℕ → ℝ)
    (h : ∀ i < K, ∀ j < K, φ i ≠ 0 → ψ j ≠ 0 →
      ∑ n : Fin (P + 1), w n * (f i (n * Real.pi / (2 * P)) *
        g j (n * Real.pi / (2 * P))) = G i j) :
    ∑ n : Fin (P + 1), w n *
      ((∑ i ∈ range K, φ i * f i (n * Real.pi / (2 * P))) *
        ∑ j ∈ range K, ψ j * g j (n * Real.pi / (2 * P))) =
      ∑ i ∈ range K, ∑ j ∈ range K, φ i * ψ j * G i j := by
  have hexp : ∀ n : Fin (P + 1), w n *
      ((∑ i ∈ range K, φ i * f i (n * Real.pi / (2 * P))) *
        ∑ j ∈ range K, ψ j * g j (n * Real.pi / (2 * P))) =
      ∑ i ∈ range K, ∑ j ∈ range K, φ i * ψ j * (w n *
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

/-- The cosine rule of the moments `μ` pairs two cosine series with symmetric coefficients of one
parity by the convolution of their coefficients against `μ_{|u|/2}`. -/
theorem sum_cosineRuleWeight_mul_laurentCos {P T r : ℕ} (hP : 0 < P) (hT : T ≤ P)
    (μ : ℕ → ℝ) {φ ψ : ℕ → ℝ} (hφ : HasLaurentParity r φ) (hψ : HasLaurentParity r ψ)
    (hsym : IsLaurentSymm T ψ) :
    ∑ n : Fin (P + 1), cosineRuleWeight P μ n *
      (laurentCos T φ (n * Real.pi / (2 * P)) * laurentCos T ψ (n * Real.pi / (2 * P))) =
      laurentGramWith (cosineRuleLaurentMoment μ) true T φ ψ := by
  simp only [laurentCos, laurentGramWith, Bool.cond_true, one_mul]
  refine (sum_weight_mul_sum_mul_sum (cosineRuleWeight P μ) φ ψ
    (fun i x ↦ Real.cos (((i : ℝ) - T) * x)) (fun j x ↦ Real.cos (((j : ℝ) - T) * x))
    (fun i j ↦ (cosineRuleLaurentMoment μ (((i + j : ℕ) : ℤ) - 2 * T) +
      cosineRuleLaurentMoment μ ((i : ℤ) - j)) / 2) ?_).trans ?_
  rotate_left
  · refine sum_congr rfl fun i _ ↦ ?_
    have h := sum_reflect_moment' (cosineRuleLaurentMoment μ) ψ 1
      (fun j hj ↦ by rw [hsym j hj, one_mul]) i
    rw [one_mul] at h
    simp only [mul_div_assoc', mul_add, add_div, sum_add_distrib, mul_assoc, ← mul_sum,
      ← sum_div] at h ⊢
    rw [h]
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
    have h1 := sum_cosineRuleWeight_mul_cos_int hP μ he₁ (by omega)
    have h2 := sum_cosineRuleWeight_mul_cos_int hP μ he₂ (by omega)
    have hsplit : ∀ w A B : ℝ, w * ((A + B) / 2) = w * A / 2 + w * B / 2 := fun _ _ _ ↦ by ring
    rw [sum_congr rfl fun n _ ↦ by rw [hpt, hsplit], sum_add_distrib, ← sum_div, ← sum_div, h1,
      h2, add_div]

/-- The cosine rule of the moments `μ` pairs two sine series with antisymmetric coefficients of
one parity by minus the convolution of their coefficients against `μ_{|u|/2}`. -/
theorem sum_cosineRuleWeight_mul_laurentSin {P T r : ℕ} (hP : 0 < P) (hT : T ≤ P)
    (μ : ℕ → ℝ) {φ ψ : ℕ → ℝ} (hφ : HasLaurentParity r φ) (hψ : HasLaurentParity r ψ)
    (hanti : IsLaurentAnti T ψ) :
    ∑ n : Fin (P + 1), cosineRuleWeight P μ n *
      (laurentSin T φ (n * Real.pi / (2 * P)) * laurentSin T ψ (n * Real.pi / (2 * P))) =
      laurentGramWith (cosineRuleLaurentMoment μ) false T φ ψ := by
  simp only [laurentSin, laurentGramWith, Bool.cond_false, neg_one_mul]
  refine (sum_weight_mul_sum_mul_sum (cosineRuleWeight P μ) φ ψ
    (fun i x ↦ Real.sin (((i : ℝ) - T) * x)) (fun j x ↦ Real.sin (((j : ℝ) - T) * x))
    (fun i j ↦ (cosineRuleLaurentMoment μ ((i : ℤ) - j) -
      cosineRuleLaurentMoment μ (((i + j : ℕ) : ℤ) - 2 * T)) / 2) ?_).trans ?_
  rotate_left
  · rw [← sum_neg_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    have h := sum_reflect_moment' (cosineRuleLaurentMoment μ) ψ (-1)
      (fun j hj ↦ by rw [hanti j hj, neg_one_mul]) i
    simp only [mul_div_assoc', mul_sub, sub_div, sum_sub_distrib, mul_assoc, ← mul_sum,
      ← sum_div] at h ⊢
    rw [h]
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
    have h1 := sum_cosineRuleWeight_mul_cos_int hP μ he₁ (by omega)
    have h2 := sum_cosineRuleWeight_mul_cos_int hP μ he₂ (by omega)
    have hsplit : ∀ w A B : ℝ, w * ((A - B) / 2) = w * A / 2 - w * B / 2 := fun _ _ _ ↦ by ring
    rw [sum_congr rfl fun n _ ↦ by rw [hpt, hsplit], sum_sub_distrib, ← sum_div, ← sum_div, h1,
      h2, sub_div]

/-- **Pairing of any two rows of one parity.** Without any symmetry of the coefficients, the
convolution against `μ_{|u|/2}` is the node sum of `C_φ C_ψ - S_φ S_ψ`, `C` and `S` the cosine and
sine series of the rows: `cos (aθ) cos (bθ) - sin (aθ) sin (bθ) = cos ((a + b)θ)`. -/
theorem sum_cosineRuleWeight_mul_laurent_sub {P T r : ℕ} (hP : 0 < P) (hT : T ≤ P)
    (μ : ℕ → ℝ) {φ ψ : ℕ → ℝ} (hφ : HasLaurentParity r φ) (hψ : HasLaurentParity r ψ) :
    ∑ n : Fin (P + 1), cosineRuleWeight P μ n *
      (laurentCos T φ (n * Real.pi / (2 * P)) * laurentCos T ψ (n * Real.pi / (2 * P)) -
        laurentSin T φ (n * Real.pi / (2 * P)) * laurentSin T ψ (n * Real.pi / (2 * P))) =
      ∑ i ∈ range (2 * T + 1), ∑ j ∈ range (2 * T + 1),
        φ i * ψ j * cosineRuleLaurentMoment μ (((i + j : ℕ) : ℤ) - 2 * T) := by
  have hpt : ∀ x : ℝ, laurentCos T φ x * laurentCos T ψ x - laurentSin T φ x * laurentSin T ψ x =
      ∑ i ∈ range (2 * T + 1), ∑ j ∈ range (2 * T + 1),
        φ i * ψ j * Real.cos (((((i + j : ℕ) : ℤ) - 2 * T : ℤ) : ℝ) * x) := by
    intro x
    simp only [laurentCos, laurentSin, sum_mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
    rw [show ((((i + j : ℕ) : ℤ) - 2 * T : ℤ) : ℝ) * x = ((i : ℝ) - T) * x + ((j : ℝ) - T) * x by
      push_cast; ring, Real.cos_add]
    ring
  simp only [hpt, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [sum_comm]
  refine sum_congr rfl fun j hj ↦ ?_
  by_cases h0 : φ i * ψ j = 0
  · simp [h0]
  have hφi : φ i ≠ 0 := left_ne_zero_of_mul h0
  have hψj : ψ j ≠ 0 := right_ne_zero_of_mul h0
  obtain ⟨he, -⟩ := even_int_of_mod (T := T) (hφ i hφi) (hψ j hψj)
  have hi' := mem_range.mp hi
  have hj' := mem_range.mp hj
  rw [← sum_cosineRuleWeight_mul_cos_int hP μ he (by omega), mul_sum]
  exact sum_congr rfl fun n _ ↦ by ring

end PDE.Analysis
