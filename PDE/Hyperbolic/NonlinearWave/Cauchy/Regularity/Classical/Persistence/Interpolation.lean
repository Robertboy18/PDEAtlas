/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.GagliardoNirenberg.Smooth

/-!
# Scaled interpolation for tame composition estimates

Dividing the adjacent-order sequence by a geometric progression preserves
its recursion. This recovers the derivative powers needed to make each
higher chain-rule product linear in the top derivative norm.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open SobolevSpace.GagliardoNirenberg

/-- The adjacent-order estimate is invariant under geometric normalization. -/
theorem exists_constant_scaled_adjacent {C : ℝ} (k : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ X : ℕ → ℝ, (∀ j ≤ k, 0 ≤ X j) → (∀ j, 0 < j → j < k → X j ^ 2 ≤ C * X (j - 1) * X (j + 1)) →
        ∀ r : ℝ, 0 < r → ∀ j ≤ k, X j ≤ A * (X 0 + X k / r ^ k) * r ^ j := by
  obtain ⟨A, hA, hest⟩ := exists_constant_of_adjacent_sq_le (le_max_right C 0) k
  refine ⟨A, hA, fun X hX hadj₀ r hr j hj ↦ ?_⟩
  have hadj (i : ℕ) (hi : 0 < i) (hik : i < k) :
      X i ^ 2 ≤ max C 0 * X (i - 1) * X (i + 1) :=
    (hadj₀ i hi hik).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (le_max_left C 0) (hX _ (by omega))) (hX _ (by omega)))
  let Y (i : ℕ) := X i / r ^ i
  have hY (i : ℕ) (hi : i ≤ k) : 0 ≤ Y i := div_nonneg (hX i hi) (pow_nonneg hr.le i)
  have hrec (i : ℕ) (hi : 0 < i) (hik : i < k) :
      Y i ^ 2 ≤ max C 0 * Y (i - 1) * Y (i + 1) := by
    have hp : r ^ (i - 1) * r ^ (i + 1) = (r ^ i) ^ 2 := by
      rw [← pow_add, ← pow_mul]
      congr 1
      omega
    dsimp [Y]
    rw [div_pow]
    have he : max C 0 * (X (i - 1) / r ^ (i - 1)) * (X (i + 1) / r ^ (i + 1)) =
        (max C 0 * X (i - 1) * X (i + 1)) / (r ^ i) ^ 2 := by
      rw [← hp]
      ring
    rw [he]
    exact div_le_div_of_nonneg_right (hadj i hi hik) (by positivity)
  have h := hest Y hY hrec j hj
  simp only [Y, pow_zero, div_one] at h
  exact (div_le_iff₀ (pow_pos hr j)).mp h

/-- Every mixed derivative has its own geometric power of the top scale.
The constant is independent of the function, its support, and the scale. -/
theorem exists_constant_scaled_derivative (n k : ℕ) [NeZero n] :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ u : ℝ^n → ℝ,
      ContDiff ℝ k u → HasCompactSupport u →
      ∀ r : ℝ, 0 < r → ∀ α : List (Fin n), α.length ≤ k →
        lpNorm (iteratedPartialDeriv α u) (derivativeExponent k α.length) volume ≤
          A * (lpNorm u ∞ volume + maxDerivativeLpNorm k k u / r ^ k) *
            r ^ α.length := by
  obtain ⟨A, hA, hest⟩ := exists_constant_scaled_adjacent (C := 2 * (k : ℝ)) k
  refine ⟨A, hA, fun u hu hc r hr α hα ↦ ?_⟩
  have h := hest (fun j ↦ maxDerivativeLpNorm k j u) (fun j _ ↦ maxDerivativeLpNorm_nonneg k j u)
    (fun j hj hjk ↦ maxDerivativeLpNorm_sq_le hu hc hj hjk) r hr α.length hα
  simpa only [maxDerivativeLpNorm_zero] using (lpNorm_iteratedPartialDeriv_le_max k u α).trans h

/-- The higher-chain gauge is homogeneous in the common derivative scale. -/
theorem sum_root_mul_pow {k : ℕ} (T : Fin k → ℝ) (hT : ∀ i, 0 ≤ T i) {r : ℝ} (hr : 0 ≤ r) :
    (∑ i : Fin k, (T i * r ^ (i.val + 1)) ^ (((i.val + 1 : ℕ) : ℝ)⁻¹)) ^ k =
      (∑ i : Fin k, T i ^ (((i.val + 1 : ℕ) : ℝ)⁻¹)) ^ k * r ^ k := by
  have he (i : Fin k) : (T i * r ^ (i.val + 1)) ^ (((i.val + 1 : ℕ) : ℝ)⁻¹) =
        T i ^ (((i.val + 1 : ℕ) : ℝ)⁻¹) * r := by
    rw [Real.mul_rpow (hT i) (pow_nonneg hr _),
      Real.pow_rpow_inv_natCast hr (by omega)]
  simp only [he, ← Finset.sum_mul, mul_pow]

end PDE.Hyperbolic.NonlinearWave.Cauchy
