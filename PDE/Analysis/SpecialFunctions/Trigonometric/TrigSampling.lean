/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigTerms
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Sup bounds of trigonometric polynomials from equally spaced samples

Let `f(β) = ∑_{k ∈ U} (a_k cos kβ + b_k sin kβ)` with frequencies `0 < k`, `2k < M`. Sampling at the
`M` points `2πj/M` is exact for `f²` (discrete Parseval,
`sum_sq_trigSum_samples`: `∑_j f(2πj/M)² = (M/2) ∑_k (a_k² + b_k²)`), and
`|a_k cos kβ + b_k sin kβ| ≤ (a_k² + b_k²)^{1/2}` together with Cauchy-Schwarz over the `q = |U|`
frequencies gives
`|f(β)| ≤ ((2q / M) ∑_{j<M} f(2πj/M)²)^{1/2}` (`abs_trigSum_le_sqrt_samples`).

This is the bound of Chen and Hou, Part II, Appendix C.3.2, for `f = ∂_β² C_{i,j,k,l}`: there
`q ≤ n = i + j` and the factor is `2n / M`. Grouping the cosine and sine of each frequency
makes the bound hold for cosines and sines together. The Nyquist frequency `2k = M` must be
excluded, since `sin(Mβ/2)` vanishes at every sample. With a constant term `c₀` the factor is
`(2q + 1) / M` (`abs_const_add_trigSum_le_sqrt_samples`).

A list of `TrigTerm`s with frequencies at most `n` is `c₀ + trigSum (Icc 1 n) a b` with the
aggregated coefficients `trigCosCoeff`, `trigSinCoeff` (`trigTermsEval_eq_trigSum`); for a list of
derivatives the constant vanishes, so `|f| ≤ ((2n / M) ∑_j f(2πj/M)²)^{1/2}` for `2n < M`
(`abs_trigTermsEval_deriv_le_sqrt_samples`), the form used for `∂_β² C_{i,j,k,l}`.

## Main definitions

* `trigSum`: the trigonometric polynomial `∑_{k ∈ U} (a_k cos kβ + b_k sin kβ)`.
* `trigCosCoeff`: the aggregated cosine coefficient of frequency `k` of a list of terms;
  `trigSinCoeff` is the sine coefficient.

## Main results

* `sum_sq_trigSum_samples`: for frequencies `0 < k`, `2k < M`,
  `∑_{j<M} f(2πj/M)² = (M/2) ∑_{k ∈ U} (a_k² + b_k²)`.
* `abs_trigSum_le_sqrt_samples`: `|f(β)| ≤ ((2|U| / M) ∑_{j<M} f(2πj/M)²)^{1/2}`.
* `abs_const_add_trigSum_le_sqrt_samples`: with a constant term,
  `|f(β)| ≤ (((2|U| + 1) / M) ∑_{j<M} f(2πj/M)²)^{1/2}`.
* `trigTermsEval_eq_trigSum`: a list of terms with frequencies at most `n` is
  `trigCosCoeff l 0` plus a trigonometric sum over the frequencies `1, …, n`.
* `abs_trigTermsEval_deriv_le_sqrt_samples`: for the derivative of such a list and `2n < M`,
  `|f(θ)| ≤ ((2n / M) ∑_{j<M} f(2πj/M)²)^{1/2}`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Appendix C.3.2.
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

namespace PDE.Analysis

open CAS.Analysis
open Finset Real

/-- A real trigonometric polynomial with frequencies in `U` and coefficients `a`, `b`. -/
noncomputable def trigSum (U : Finset ℕ) (a b : ℕ → ℝ) (β : ℝ) : ℝ :=
  ∑ k ∈ U, (a k * Real.cos (k * β) + b k * Real.sin (k * β))

/-- Over the `M` points of the circle, `∑ cos(d x_j) = M` if `d = 0` and `0` for `0 < d < M`. -/
theorem sum_range_cos_samples {M d : ℕ} (hM : 0 < M) (hd : d < M) :
    ∑ j ∈ range M, Real.cos (d * (2 * π * j / M)) = if d = 0 then (M : ℝ) else 0 := by
  rw [sum_range_cos_mul_two_pi hM d]
  by_cases h0 : d = 0
  · simp [h0]
  · have : ¬ M ∣ d := fun h ↦ h0 (Nat.eq_zero_of_dvd_of_lt h hd)
    simp [h0, this]

/-- `∑_j cos(k x_j - m x_j)` is `M` for `k = m` and `0` otherwise, for `k, m < M`. -/
theorem sum_range_cos_sub_samples {M k m : ℕ} (hM : 0 < M) (hk : k < M) (hm : m < M) :
    ∑ j ∈ range M, Real.cos (k * (2 * π * j / M) - m * (2 * π * j / M)) =
      if k = m then (M : ℝ) else 0 := by
  rcases le_total m k with h | h
  · have e : ∀ j : ℕ, Real.cos (k * (2 * π * j / M) - m * (2 * π * j / M)) =
        Real.cos (((k - m : ℕ) : ℝ) * (2 * π * j / M)) := fun j ↦ by
      rw [Nat.cast_sub h]
      ring_nf
    simp only [e]
    rw [sum_range_cos_samples hM (by omega)]
    by_cases hkm : k = m
    · simp [hkm]
    · have : k - m ≠ 0 := by omega
      simp [hkm, this]
  · have e : ∀ j : ℕ, Real.cos (k * (2 * π * j / M) - m * (2 * π * j / M)) =
        Real.cos (((m - k : ℕ) : ℝ) * (2 * π * j / M)) := fun j ↦ by
      rw [Nat.cast_sub h, ← Real.cos_neg]
      ring_nf
    simp only [e]
    rw [sum_range_cos_samples hM (by omega)]
    by_cases hkm : k = m
    · simp [hkm]
    · have : m - k ≠ 0 := by omega
      simp [hkm, this]

/-- `∑_j sin(k x_j - m x_j) = 0`. -/
theorem sum_range_sin_sub_samples {M : ℕ} (k m : ℕ) :
    ∑ j ∈ range M, Real.sin (k * (2 * π * j / M) - m * (2 * π * j / M)) = 0 := by
  rcases le_total m k with h | h
  · have e : ∀ j : ℕ, Real.sin (k * (2 * π * j / M) - m * (2 * π * j / M)) =
        Real.sin (((k - m : ℕ) : ℝ) * (2 * π * j / M)) := fun j ↦ by
      rw [Nat.cast_sub h]
      ring_nf
    simp only [e]
    exact sum_range_sin_mul_two_pi _
  · have e : ∀ j : ℕ, Real.sin (k * (2 * π * j / M) - m * (2 * π * j / M)) =
        -Real.sin (((m - k : ℕ) : ℝ) * (2 * π * j / M)) := fun j ↦ by
      rw [Nat.cast_sub h, ← Real.sin_neg]
      ring_nf
    simp only [e, sum_neg_distrib, sum_range_sin_mul_two_pi, neg_zero]

/-- `∑_j cos(k x_j + m x_j) = 0` for `0 < k + m < M`. -/
theorem sum_range_cos_add_samples {M k m : ℕ} (hM : 0 < M) (hkm : 0 < k + m)
    (hkm' : k + m < M) :
    ∑ j ∈ range M, Real.cos (k * (2 * π * j / M) + m * (2 * π * j / M)) = 0 := by
  have e : ∀ j : ℕ, Real.cos (k * (2 * π * j / M) + m * (2 * π * j / M)) =
      Real.cos (((k + m : ℕ) : ℝ) * (2 * π * j / M)) := fun j ↦ by
    push_cast
    ring_nf
  simp only [e]
  rw [sum_range_cos_samples hM hkm', ite_eq_right_iff.mpr (fun h ↦ absurd h (by omega))]

/-- `∑_j sin(k x_j + m x_j) = 0`. -/
theorem sum_range_sin_add_samples {M : ℕ} (k m : ℕ) :
    ∑ j ∈ range M, Real.sin (k * (2 * π * j / M) + m * (2 * π * j / M)) = 0 := by
  have e : ∀ j : ℕ, Real.sin (k * (2 * π * j / M) + m * (2 * π * j / M)) =
      Real.sin (((k + m : ℕ) : ℝ) * (2 * π * j / M)) := fun j ↦ by
    push_cast
    ring_nf
  simp only [e]
  exact sum_range_sin_mul_two_pi _

/-- Discrete orthogonality of one frequency pair: for `0 < k, m` and `2k, 2m < M`, the sampled
products of `a cos(k·) + b sin(k·)` and `c cos(m·) + d sin(m·)` sum to `(M/2)(ac + bd)` if `k = m`
and to `0` otherwise. -/
theorem sum_range_mode_mul_mode_samples {M k m : ℕ} (hM : 0 < M) (hk : 0 < k) (hm : 0 < m)
    (hk' : 2 * k < M) (hm' : 2 * m < M) (a b c d : ℝ) :
    ∑ j ∈ range M, (a * Real.cos (k * (2 * π * j / M)) + b * Real.sin (k * (2 * π * j / M))) *
        (c * Real.cos (m * (2 * π * j / M)) + d * Real.sin (m * (2 * π * j / M))) =
      if k = m then (M : ℝ) / 2 * (a * c + b * d) else 0 := by
  -- product to sum
  have e : ∀ j : ℕ, (a * Real.cos (k * (2 * π * j / M)) + b * Real.sin (k * (2 * π * j / M))) *
      (c * Real.cos (m * (2 * π * j / M)) + d * Real.sin (m * (2 * π * j / M))) =
      (a * c + b * d) / 2 * Real.cos (k * (2 * π * j / M) - m * (2 * π * j / M)) +
      (a * c - b * d) / 2 * Real.cos (k * (2 * π * j / M) + m * (2 * π * j / M)) +
      (b * c - a * d) / 2 * Real.sin (k * (2 * π * j / M) - m * (2 * π * j / M)) +
      (a * d + b * c) / 2 * Real.sin (k * (2 * π * j / M) + m * (2 * π * j / M)) := fun j ↦ by
    rw [Real.cos_sub, Real.cos_add, Real.sin_sub, Real.sin_add]
    ring
  simp only [e, sum_add_distrib, ← mul_sum]
  rw [sum_range_cos_sub_samples hM (by omega) (by omega),
    sum_range_cos_add_samples hM (by omega) (by omega), sum_range_sin_sub_samples,
    sum_range_sin_add_samples]
  split_ifs <;> ring

/-- **Discrete Parseval.** For frequencies `0 < k`, `2k < M` in `U`,
`∑_{j<M} f(2πj/M)² = (M/2) ∑_{k ∈ U} (a_k² + b_k²)`. -/
theorem sum_sq_trigSum_samples {U : Finset ℕ} {M : ℕ} (hM : 0 < M)
    (hU : ∀ k ∈ U, 0 < k ∧ 2 * k < M) (a b : ℕ → ℝ) :
    ∑ j ∈ range M, trigSum U a b (2 * π * j / M) ^ 2 =
      (M : ℝ) / 2 * ∑ k ∈ U, (a k ^ 2 + b k ^ 2) := by
  simp only [trigSum, sq, sum_mul_sum]
  rw [sum_comm]
  rw [show (M : ℝ) / 2 * ∑ k ∈ U, (a k * a k + b k * b k) =
      ∑ k ∈ U, ∑ m ∈ U, if k = m then (M : ℝ) / 2 * (a k * a m + b k * b m) else 0 by
    rw [mul_sum]
    refine sum_congr rfl fun k hk ↦ ?_
    rw [sum_ite_eq U k]
    simp [hk]]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [sum_comm]
  refine sum_congr rfl fun m hm ↦ ?_
  exact sum_range_mode_mul_mode_samples hM (hU k hk).1 (hU m hm).1 (hU k hk).2 (hU m hm).2 _ _ _ _

/-- A single mode is at most the Euclidean norm of its coefficients. -/
theorem abs_mode_le_sqrt (a b θ : ℝ) :
    |a * Real.cos θ + b * Real.sin θ| ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
  apply Real.abs_le_sqrt
  nlinarith [sq_nonneg (a * Real.sin θ - b * Real.cos θ), Real.sin_sq_add_cos_sq θ]

/-- **Part II, App C.3.2 (sampling bound).** For `f = ∑_{k ∈ U} (a_k cos kβ + b_k sin kβ)` with
`0 < k` and `2k < M` for every frequency, `|f(β)| ≤ ((2|U| / M) ∑_{j<M} f(2πj/M)²)^{1/2}`. -/
theorem abs_trigSum_le_sqrt_samples {U : Finset ℕ} {M : ℕ} (hM : 0 < M)
    (hU : ∀ k ∈ U, 0 < k ∧ 2 * k < M) (a b : ℕ → ℝ) (β : ℝ) :
    |trigSum U a b β| ≤
      Real.sqrt (2 * U.card / M * ∑ j ∈ range M, trigSum U a b (2 * π * j / M) ^ 2) := by
  rw [sum_sq_trigSum_samples hM hU]
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hval : 2 * (U.card : ℝ) / M * ((M : ℝ) / 2 * ∑ k ∈ U, (a k ^ 2 + b k ^ 2)) =
      U.card * ∑ k ∈ U, (a k ^ 2 + b k ^ 2) := by
    field_simp
  rw [hval]
  apply Real.abs_le_sqrt
  set s : ℕ → ℝ := fun k ↦ Real.sqrt (a k ^ 2 + b k ^ 2)
  have hpt : |trigSum U a b β| ≤ ∑ k ∈ U, s k :=
    (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ ↦ abs_mode_le_sqrt _ _ _)
  have hs2 : ∀ k, s k ^ 2 = a k ^ 2 + b k ^ 2 := fun k ↦
    Real.sq_sqrt (by positivity)
  have hcs := sq_sum_le_card_mul_sum_sq (s := U) (f := s)
  simp only [hs2] at hcs
  calc trigSum U a b β ^ 2 = |trigSum U a b β| ^ 2 := (sq_abs _).symm
    _ ≤ (∑ k ∈ U, s k) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hpt 2
    _ ≤ _ := hcs

/-- `(|x| + Y)² ≤ (2q + 1) (x² + S/2)` whenever `Y ≥ 0` and `Y² ≤ q S`. -/
theorem sq_abs_add_le_of_sq_le {x Y S q : ℝ} (hq : 0 ≤ q) (hY : 0 ≤ Y) (hS : 0 ≤ S)
    (hcs : Y ^ 2 ≤ q * S) : (|x| + Y) ^ 2 ≤ (2 * q + 1) * (x ^ 2 + S / 2) := by
  have hx : |x| ^ 2 = x ^ 2 := sq_abs x
  rcases hq.eq_or_lt with hq0 | hqpos
  · rw [← hq0] at hcs ⊢
    have hY0 : Y = 0 := by nlinarith
    rw [hY0]
    nlinarith
  · have hyoung : 2 * |x| * Y ≤ 2 * q * x ^ 2 + Y ^ 2 / (2 * q) := by
      rw [← sub_nonneg]
      have hid : 2 * q * x ^ 2 + Y ^ 2 / (2 * q) - 2 * |x| * Y =
          (2 * q * |x| - Y) ^ 2 / (2 * q) := by
        field_simp
        rw [← hx]
        ring
      rw [hid]
      positivity
    have hY2 : Y ^ 2 / (2 * q) ≤ S / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith

/-- **The sampling bound with a constant term.** For `f = c₀ + ∑_{k ∈ U} (a_k cos kβ + b_k sin kβ)`
under the same frequency conditions,
`|f(β)| ≤ (((2|U| + 1) / M) ∑_{j<M} f(2πj/M)²)^{1/2}`. -/
theorem abs_const_add_trigSum_le_sqrt_samples {U : Finset ℕ} {M : ℕ} (hM : 0 < M)
    (hU : ∀ k ∈ U, 0 < k ∧ 2 * k < M) (c₀ : ℝ) (a b : ℕ → ℝ) (β : ℝ) :
    |c₀ + trigSum U a b β| ≤ Real.sqrt ((2 * U.card + 1) / M *
      ∑ j ∈ range M, (c₀ + trigSum U a b (2 * π * j / M)) ^ 2) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  -- Parseval with the constant term
  have hcross : ∑ j ∈ range M, trigSum U a b (2 * π * j / M) = 0 := by
    simp only [trigSum]
    rw [sum_comm]
    refine sum_eq_zero fun k hk ↦ ?_
    have hk2 := (hU k hk).2
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_range_cos_samples hM (by omega),
      sum_range_sin_mul_two_pi]
    simp [(hU k hk).1.ne']
  have hpars : ∑ j ∈ range M, (c₀ + trigSum U a b (2 * π * j / M)) ^ 2 =
      M * c₀ ^ 2 + (M : ℝ) / 2 * ∑ k ∈ U, (a k ^ 2 + b k ^ 2) := by
    have e : ∀ j : ℕ, (c₀ + trigSum U a b (2 * π * j / M)) ^ 2 =
        c₀ ^ 2 + 2 * c₀ * trigSum U a b (2 * π * j / M) + trigSum U a b (2 * π * j / M) ^ 2 :=
      fun j ↦ by ring
    simp only [e, sum_add_distrib, ← mul_sum, hcross, sum_sq_trigSum_samples hM hU, sum_const,
      card_range, nsmul_eq_mul]
    ring
  rw [hpars]
  apply Real.abs_le_sqrt
  set s : ℕ → ℝ := fun k ↦ Real.sqrt (a k ^ 2 + b k ^ 2)
  have hs2 : ∀ k, s k ^ 2 = a k ^ 2 + b k ^ 2 := fun k ↦ Real.sq_sqrt (by positivity)
  have hpt : |c₀ + trigSum U a b β| ≤ |c₀| + ∑ k ∈ U, s k :=
    (abs_add_le _ _).trans (add_le_add le_rfl
      ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ ↦ abs_mode_le_sqrt _ _ _)))
  have hcs := sq_sum_le_card_mul_sum_sq (s := U) (f := s)
  simp only [hs2] at hcs
  set Y := ∑ k ∈ U, s k
  set S := ∑ k ∈ U, (a k ^ 2 + b k ^ 2)
  have hY : 0 ≤ Y := sum_nonneg fun k _ ↦ Real.sqrt_nonneg _
  have hS : 0 ≤ S := sum_nonneg fun k _ ↦ by positivity
  have key := sq_abs_add_le_of_sq_le (x := c₀) (Nat.cast_nonneg U.card) hY hS hcs
  calc (c₀ + trigSum U a b β) ^ 2 = |c₀ + trigSum U a b β| ^ 2 := (sq_abs _).symm
    _ ≤ (|c₀| + Y) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hpt 2
    _ ≤ (2 * (U.card : ℝ) + 1) * (c₀ ^ 2 + S / 2) := key
    _ = (2 * (U.card : ℝ) + 1) / M * (M * c₀ ^ 2 + (M : ℝ) / 2 * S) := by field_simp

/-! ### Lists of trigonometric terms -/

/-- The aggregated cosine coefficient of frequency `k` of a list of terms. -/
noncomputable def trigCosCoeff (l : List TrigTerm) (k : ℕ) : ℝ :=
  (l.map fun t ↦ if t.isSin = false ∧ t.freq.natAbs = k then (t.coeff : ℝ) else 0).sum

/-- The aggregated sine coefficient of frequency `k` of a list of terms. -/
noncomputable def trigSinCoeff (l : List TrigTerm) (k : ℕ) : ℝ :=
  (l.map fun t ↦ if t.isSin = true ∧ t.freq.natAbs = k then
    (Int.sign t.freq : ℝ) * t.coeff else 0).sum

/-- `trigSum U` is additive in the coefficient pair `(a, b)`. -/
theorem trigSum_add (U : Finset ℕ) (a b a' b' : ℕ → ℝ) (β : ℝ) :
    trigSum U (a + a') (b + b') β = trigSum U a b β + trigSum U a' b' β := by
  simp only [trigSum, Pi.add_apply, ← sum_add_distrib]
  exact sum_congr rfl fun k _ ↦ by ring

/-- One term as a constant plus a trigonometric sum over the frequencies `1, …, n`. -/
theorem TrigTerm.eval_eq_trigSum (t : TrigTerm) {n : ℕ} (ht : t.freq.natAbs ≤ n) (θ : ℝ) :
    t.eval θ = trigCosCoeff [t] 0 + trigSum (Finset.Icc 1 n) (trigCosCoeff [t])
      (trigSinCoeff [t]) θ := by
  rcases t with ⟨c, f, bs⟩
  unfold trigSum trigCosCoeff trigSinCoeff TrigTerm.eval
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at ht ⊢
  have hcast : ((f.natAbs : ℕ) : ℝ) = |(f : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  by_cases hf : f.natAbs = 0
  · have hf0 : f = 0 := Int.natAbs_eq_zero.mp hf
    subst hf0
    rw [sum_eq_zero fun k hk ↦ by
      have : (0 : ℤ).natAbs ≠ k := by have := (Finset.mem_Icc.mp hk).1; simp; omega
      simp only [this, and_false, ite_false, zero_mul, add_zero]]
    cases bs <;> simp
  · have hmem : f.natAbs ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hf, ht⟩
    rw [sum_eq_single f.natAbs (fun k _ hk ↦ by simp only [Ne.symm hk, and_false, ite_false,
      zero_mul, add_zero]) (fun h ↦ absurd hmem h)]
    simp only [hf, and_false, ite_false, zero_add, and_true, hcast]
    cases bs
    · simp only [Bool.false_eq_true, ite_false, zero_mul, add_zero, ite_true]
      rcases abs_cases (f : ℝ) with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h]
      · rw [h, neg_mul, Real.cos_neg]
    · rcases lt_or_gt_of_ne (show f ≠ 0 from fun h ↦ hf (Int.natAbs_eq_zero.mpr h)) with h | h
      · rw [Int.sign_eq_neg_one_of_neg h, abs_of_neg (by exact_mod_cast h), neg_mul,
          Real.sin_neg]
        simp only [ite_true]
        push_cast
        ring
      · rw [Int.sign_eq_one_of_pos h, abs_of_pos (by exact_mod_cast h)]
        simp only [ite_true]
        push_cast
        ring

/-- **A list of terms as a trigonometric polynomial.** If every frequency of `l` is at most `n` in
absolute value, then `l` evaluates to `trigCosCoeff l 0 + trigSum (Icc 1 n) …`. -/
theorem trigTermsEval_eq_trigSum (l : List TrigTerm) {n : ℕ}
    (hl : ∀ t ∈ l, t.freq.natAbs ≤ n) (θ : ℝ) :
    trigTermsEval l θ =
      trigCosCoeff l 0 + trigSum (Finset.Icc 1 n) (trigCosCoeff l) (trigSinCoeff l) θ := by
  induction l with
  | nil => simp [trigCosCoeff, trigSinCoeff, trigSum]
  | cons t l ih =>
    have hsplitc : trigCosCoeff (t :: l) = trigCosCoeff [t] + trigCosCoeff l := by
      funext k
      simp [trigCosCoeff]
    have hsplits : trigSinCoeff (t :: l) = trigSinCoeff [t] + trigSinCoeff l := by
      funext k
      simp [trigSinCoeff]
    rw [trigTermsEval_cons, hsplitc, hsplits, trigSum_add, Pi.add_apply,
      t.eval_eq_trigSum (hl t List.mem_cons_self) θ,
      ih fun s hs ↦ hl s (List.mem_cons_of_mem t hs)]
    ring

/-- The derivative of a list has no constant term. -/
theorem trigCosCoeff_map_deriv_zero (l : List TrigTerm) :
    trigCosCoeff (l.map TrigTerm.deriv) 0 = 0 := by
  induction l with
  | nil => simp [trigCosCoeff]
  | cons t l ih =>
    simp only [trigCosCoeff, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, add_zero]
    rcases t with ⟨c, f, bs⟩
    cases bs <;> by_cases hf : f.natAbs = 0 <;>
      simp [TrigTerm.deriv, hf, Int.natAbs_eq_zero.mp]

/-- **App C.3.2 for lists.** If every frequency of `l` is at most `n` and `2n < M`, the derivative
list satisfies `|f(θ)| ≤ ((2n / M) ∑_{j<M} f(2πj/M)²)^{1/2}`. -/
theorem abs_trigTermsEval_deriv_le_sqrt_samples (l : List TrigTerm) {n M : ℕ}
    (hl : ∀ t ∈ l, t.freq.natAbs ≤ n) (hM : 2 * n < M) (θ : ℝ) :
    |trigTermsEval (l.map TrigTerm.deriv) θ| ≤ Real.sqrt (2 * n / M *
      ∑ j ∈ range M, trigTermsEval (l.map TrigTerm.deriv) (2 * π * j / M) ^ 2) := by
  have hl' : ∀ t ∈ l.map TrigTerm.deriv, t.freq.natAbs ≤ n := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    unfold TrigTerm.deriv
    split_ifs <;> exact hl s hs
  have hrep := fun θ ↦ trigTermsEval_eq_trigSum (l.map TrigTerm.deriv) hl' θ
  simp only [trigCosCoeff_map_deriv_zero, zero_add] at hrep
  simp only [hrep]
  have h := abs_trigSum_le_sqrt_samples (U := Finset.Icc 1 n) (M := M) (by omega)
    (fun k hk ↦ ⟨(Finset.mem_Icc.mp hk).1, by have := (Finset.mem_Icc.mp hk).2; omega⟩)
    (trigCosCoeff (l.map TrigTerm.deriv)) (trigSinCoeff (l.map TrigTerm.deriv)) θ
  simpa using h

end PDE.Analysis
