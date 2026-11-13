/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SmoothTransitionDerivatives
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Quantitative flatness of the exponential transition

Every polynomial order bounds the value and the first two derivatives
near the flat endpoint, with explicit factorial constants.

## Main results

* `exp_neg_inv_le_factorial_mul_pow`: `exp(-1/t) ≤ n! tⁿ` for `t > 0`.
* `smoothTransition_le_factorial_mul_pow`: `σ(t) ≤ 9 n! tⁿ` on `[0, 1/2]`, for
  `σ = Real.smoothTransition`.
* `abs_deriv_smoothTransition_le_factorial_mul_pow`: `|σ'(t)| ≤ 18 (n + 2)! tⁿ` on `[0, 1/2]`.
* `abs_deriv_deriv_smoothTransition_le_factorial_mul_pow`: `|σ''(t)| ≤ 54 (n + 4)! tⁿ` on
  `[0, 1/2]`.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

/-- The exponential series bounds the flat exponential by every polynomial order. -/
theorem exp_neg_inv_le_factorial_mul_pow (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Real.exp (-t⁻¹) ≤ (n.factorial : ℝ) * t ^ n := by
  have hn : 0 < (n.factorial : ℝ) := Nat.cast_pos.mpr n.factorial_pos
  have h := Real.pow_div_factorial_le_exp t⁻¹ (inv_pos.mpr ht).le n
  have hm := mul_le_mul_of_nonneg_right h
    (mul_nonneg hn.le (pow_nonneg ht.le n))
  have heq : (t⁻¹ ^ n / (n.factorial : ℝ)) * ((n.factorial : ℝ) * t ^ n) = 1 := by
    field_simp [ht.ne', hn.ne']
    rw [← mul_pow]
    simp [ht.ne']
  rw [heq] at hm
  rw [Real.exp_neg, ← one_div]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  simpa only [mul_comm] using hm

/-- `e ^ 2 < 9`. -/
private theorem exp_two_lt_nine : Real.exp 2 < 9 := by
  have heq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [heq]
  nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]

/-- Quantitative flatness of the value, including the endpoint. -/
theorem smoothTransition_le_factorial_mul_pow (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) (ht₂ : t ≤ 1 / 2) :
    Real.smoothTransition t ≤ 9 * (n.factorial : ℝ) * t ^ n := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp only [Real.smoothTransition.zero]
    positivity
  have ht₁ : t < 1 := by linarith
  have hgap : 0 < 1 - t := by linarith
  have hrecip : 1 / (1 - t) ≤ 2 := by
    apply (div_le_iff₀ hgap).mpr
    linarith
  have hχ : Real.smoothTransition t ≤ Real.exp (-(1 / t - 1 / (1 - t))) := by
    rw [smoothTransition_eq_inv_one_add_exp ht ht₁, Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le
      (Real.exp_pos (1 / t - 1 / (1 - t))) (le_add_of_nonneg_left zero_le_one)
  have heq : Real.exp (-(1 / t - 1 / (1 - t))) =
      Real.exp (-t⁻¹) * Real.exp (1 / (1 - t)) := by
    rw [← Real.exp_add]
    congr 1
    simp only [one_div]
    ring
  calc
    Real.smoothTransition t ≤ Real.exp (-t⁻¹) * Real.exp (1 / (1 - t)) := hχ.trans_eq heq
    _ ≤ Real.exp (-t⁻¹) * 9 :=
      mul_le_mul_of_nonneg_left
        ((Real.exp_le_exp.mpr hrecip).trans exp_two_lt_nine.le) (Real.exp_pos _).le
    _ ≤ ((n.factorial : ℝ) * t ^ n) * 9 :=
      mul_le_mul_of_nonneg_right (exp_neg_inv_le_factorial_mul_pow n ht) (by norm_num)
    _ = _ := by ring

/-- On `(0, 1/2]` the rate `1 / t ^ 2 + 1 / (1 - t) ^ 2` lies between `0` and `2 / t ^ 2`. -/
private theorem rate_bounds {t : ℝ} (ht : 0 < t) (ht₂ : t ≤ 1 / 2) :
    0 ≤ smoothTransitionRate t ∧ smoothTransitionRate t ≤ 2 / t ^ 2 := by
  have hrecip : 1 / (1 - t) ^ 2 ≤ 1 / t ^ 2 := by
    apply one_div_le_one_div_of_le (sq_pos_of_pos ht)
    nlinarith
  constructor
  · unfold smoothTransitionRate
    positivity
  · unfold smoothTransitionRate
    simp only [div_eq_mul_inv] at hrecip ⊢
    linarith

/-- On `(0, 1/2]` the derivative `-2 / t ^ 3 + 2 / (1 - t) ^ 3` of the rate is at most `2 / t ^ 4`
in absolute value. -/
private theorem abs_rate_derivative_le {t : ℝ} (ht : 0 < t) (ht₂ : t ≤ 1 / 2) :
    |-2 / t ^ 3 + 2 / (1 - t) ^ 3| ≤ 2 / t ^ 4 := by
  have hgap : 0 < 1 - t := by linarith
  have hp : t ^ 3 ≤ (1 - t) ^ 3 := by
    gcongr
    linarith
  have hrecip : 2 / (1 - t) ^ 3 ≤ 2 / t ^ 3 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos ht 3) hp
  calc
    |-2 / t ^ 3 + 2 / (1 - t) ^ 3| ≤ |-2 / t ^ 3| + |2 / (1 - t) ^ 3| :=
      abs_add_le _ _
    _ = 2 / t ^ 3 + 2 / (1 - t) ^ 3 := by
      rw [abs_div, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos (pow_pos ht 3), abs_of_pos (pow_pos hgap 3)]
    _ ≤ 4 / t ^ 3 := by
      simp only [div_eq_mul_inv] at hrecip ⊢
      linarith
    _ ≤ 2 / t ^ 4 := by
      apply (div_le_div_iff₀ (pow_pos ht 3) (pow_pos ht 4)).mpr
      nlinarith [mul_nonneg (pow_nonneg ht.le 3) (by linarith : 0 ≤ 1 - 2 * t)]

/-- Quantitative flatness of the first derivative. -/
theorem abs_deriv_smoothTransition_le_factorial_mul_pow (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) (ht₂ : t ≤ 1 / 2) :
    |deriv Real.smoothTransition t| ≤ 18 * ((n + 2).factorial : ℝ) * t ^ n := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · have hz := iteratedDeriv_smoothTransition_zero 1
    simp only [iteratedDeriv_one] at hz
    rw [hz, abs_zero]
    positivity
  have ht₁ : t < 1 := by linarith
  have hχ := Real.smoothTransition.nonneg t
  have hχ₁ := Real.smoothTransition.le_one t
  have hrate := rate_bounds ht ht₂
  rw [deriv_smoothTransition ht ht₁,
    abs_of_nonneg (mul_nonneg (mul_nonneg hχ (sub_nonneg.mpr hχ₁)) hrate.1)]
  calc
    Real.smoothTransition t * (1 - Real.smoothTransition t) * smoothTransitionRate t
        ≤ Real.smoothTransition t * smoothTransitionRate t :=
          mul_le_mul_of_nonneg_right (by nlinarith) hrate.1
    _ ≤ Real.smoothTransition t * (2 / t ^ 2) :=
      mul_le_mul_of_nonneg_left hrate.2 hχ
    _ ≤ (9 * ((n + 2).factorial : ℝ) * t ^ (n + 2)) * (2 / t ^ 2) :=
      mul_le_mul_of_nonneg_right (smoothTransition_le_factorial_mul_pow (n + 2) ht.le ht₂)
        (by positivity)
    _ = _ := by
      rw [pow_add]
      field_simp [ht.ne']
      ring

/-- Quantitative flatness of the second derivative. -/
theorem abs_deriv_deriv_smoothTransition_le_factorial_mul_pow (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) (ht₂ : t ≤ 1 / 2) :
    |deriv (deriv Real.smoothTransition) t| ≤
      54 * ((n + 4).factorial : ℝ) * t ^ n := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · have hz := iteratedDeriv_smoothTransition_zero 2
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at hz
    rw [hz, abs_zero]
    positivity
  have ht₁ : t < 1 := by linarith
  have hχ := Real.smoothTransition.nonneg t
  have hχ₁ := Real.smoothTransition.le_one t
  have hfactor : 0 ≤ Real.smoothTransition t * (1 - Real.smoothTransition t) :=
    mul_nonneg hχ (sub_nonneg.mpr hχ₁)
  have hfactor_le : Real.smoothTransition t * (1 - Real.smoothTransition t) ≤
      Real.smoothTransition t := by nlinarith
  have hmiddle : |1 - 2 * Real.smoothTransition t| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hrate := rate_bounds ht ht₂
  have hrate_sq : smoothTransitionRate t ^ 2 ≤ 4 / t ^ 4 := by
    calc
      smoothTransitionRate t ^ 2 ≤ (2 / t ^ 2) ^ 2 := by
        gcongr
        · exact hrate.1
        · exact hrate.2
      _ = _ := by ring
  have hbracket : |(1 - 2 * Real.smoothTransition t) * smoothTransitionRate t ^ 2 +
      (-2 / t ^ 3 + 2 / (1 - t) ^ 3)| ≤ 6 / t ^ 4 := by
    calc
      _ ≤ |(1 - 2 * Real.smoothTransition t) * smoothTransitionRate t ^ 2| +
          |-2 / t ^ 3 + 2 / (1 - t) ^ 3| := abs_add_le _ _
      _ ≤ smoothTransitionRate t ^ 2 + 2 / t ^ 4 := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg (smoothTransitionRate t))]
        exact add_le_add
          (by simpa using mul_le_mul_of_nonneg_right hmiddle (sq_nonneg (smoothTransitionRate t)))
          (abs_rate_derivative_le ht ht₂)
      _ ≤ _ := by
        simp only [div_eq_mul_inv] at hrate_sq ⊢
        linarith
  rw [deriv_deriv_smoothTransition ht ht₁, abs_mul, abs_of_nonneg hfactor]
  calc
    _ ≤ Real.smoothTransition t * (6 / t ^ 4) :=
      mul_le_mul hfactor_le hbracket (abs_nonneg _) hχ
    _ ≤ (9 * ((n + 4).factorial : ℝ) * t ^ (n + 4)) * (6 / t ^ 4) :=
      mul_le_mul_of_nonneg_right (smoothTransition_le_factorial_mul_pow (n + 4) ht.le ht₂)
        (by positivity)
    _ = _ := by
      rw [pow_add]
      field_simp [ht.ne']
      ring

end PDE.Analysis
