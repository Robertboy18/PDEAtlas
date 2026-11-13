/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Matrix.RealSpectrumExponential

/-!
# Signed-time bounds for real-spectrum matrix symbols

Reflection of the frequency changes the sign of the symbol. Consequently the
polynomial exponential estimate holds on bounded intervals of either sign.
The constants are chosen before the frequency and before any vector to which the
multiplier is applied.
-/

@[expose] public noncomputable section

open NormedSpace
open scoped BigOperators Matrix.Norms.L2Operator

namespace Matrix

variable {n m : ℕ}

/-- The polynomial symbol estimate holds for positive and negative times. -/
theorem norm_exp_symbol_le_polynomial_of_abs_le
    (A : Fin n → Matrix (Fin m) (Fin m) ℂ)
    (hA : ∀ ξ : ℝ^n,
      ∀ z ∈ spectrum ℂ (∑ j, ξ j • A j), z.im = 0)
    (ξ : ℝ^n) {t T : ℝ} (ht : |t| ≤ T) :
    ‖exp (t • (-Complex.I • (∑ j, ξ j • A j)))‖ ≤
      (∑ k ∈ Finset.range m, (2 * T) ^ k / k.factorial) *
        (1 + ((∑ j, ‖A j‖) * ‖ξ‖) ^ (m - 1)) := by
  by_cases ht0 : 0 ≤ t
  · exact norm_exp_symbol_le_polynomial_of_real_spectrum A hA ξ ht0
      ((le_abs_self t).trans ht)
  · have ht0' : 0 ≤ -t := neg_nonneg.mpr (le_of_not_ge ht0)
    have h := norm_exp_symbol_le_polynomial_of_real_spectrum A hA (-ξ) ht0'
      ((neg_le_abs t).trans ht)
    simpa only [PiLp.neg_apply, neg_smul, Finset.sum_neg_distrib, smul_neg,
      neg_neg, norm_neg] using h

/-- A bounded signed time interval admits a single nonnegative polynomial
constant, uniform in frequency. Zero spatial and matrix dimensions are included. -/
theorem exists_norm_exp_symbol_le
    (A : Fin n → Matrix (Fin m) (Fin m) ℂ)
    (hA : ∀ ξ : ℝ^n,
      ∀ z ∈ spectrum ℂ (∑ j, ξ j • A j), z.im = 0)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ T →
      ∀ ξ : ℝ^n,
        ‖exp (t • (-Complex.I • (∑ j, ξ j • A j)))‖ ≤
          C * (1 + ‖ξ‖ ^ (m - 1)) := by
  let S : ℝ := ∑ k ∈ Finset.range m, (2 * T) ^ k / k.factorial
  let L : ℝ := ∑ j, ‖A j‖
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ ↦ by positivity
  have hL : 0 ≤ L := Finset.sum_nonneg fun j _ ↦ norm_nonneg _
  refine ⟨S * (1 + L ^ (m - 1)), by positivity, fun t ht ξ ↦ ?_⟩
  refine (norm_exp_symbol_le_polynomial_of_abs_le A hA ξ ht).trans ?_
  change S * (1 + (L * ‖ξ‖) ^ (m - 1)) ≤
    S * (1 + L ^ (m - 1)) * (1 + ‖ξ‖ ^ (m - 1))
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hS
  rw [mul_pow]
  nlinarith [pow_nonneg hL (m - 1), pow_nonneg (norm_nonneg ξ) (m - 1)]

end Matrix
