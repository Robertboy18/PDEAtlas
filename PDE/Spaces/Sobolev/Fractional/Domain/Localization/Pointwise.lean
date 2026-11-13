/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.Kernel

/-!
# Pointwise fractional product estimates

The cutoff contribution is controlled by its Lipschitz constant and uniform
bound. Splitting a product increment leaves the original fractional increment
and an integrable radial kernel times the original function's square.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace SobolevSpace.Fractional.Localization

variable {n : ℕ} {s : ℝ} {φ : ℝ^n → ℝ} {L M : ℝ≥0}

/-- Squaring the difference quotient recovers its full kernel exponent. -/
theorem norm_diffQuot_sq (u : ℝ^n → ℝ) (x y : ℝ^n) :
    ‖diffQuot n s u (x, y)‖ ^ 2 =
      ‖u x - u y‖ ^ 2 / ‖x - y‖ ^ ((n : ℝ) + 2 * s) := by
  simp only [diffQuot_apply_real, ENNReal.toReal_ofNat, norm_div,
    Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), div_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  push_cast
  ring

/-- A bounded Lipschitz cutoff has a squared difference quotient controlled by
the integrable localization kernel. -/
theorem norm_diffQuot_cutoff_sq_le
    (hs : 0 ≤ (n : ℝ) + 2 * s) (hL : LipschitzWith L φ)
    (hM : ∀ x, ‖φ x‖ ≤ M) (x y : ℝ^n) :
    ‖diffQuot n s φ (x, y)‖ ^ 2 ≤
      ((L : ℝ) ^ 2 + 4 * (M : ℝ) ^ 2) * cutoffKernel n s (x - y) := by
  by_cases hxy : x = y
  · subst y
    simp only [diffQuot_apply_real, ENNReal.toReal_ofNat, sub_self, zero_div,
      norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    exact mul_nonneg (by positivity) (cutoffKernel_nonneg _)
  have hr : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  rw [norm_diffQuot_sq]
  by_cases hnear : ‖x - y‖ < 1
  · have hinc : ‖φ x - φ y‖ ≤ (L : ℝ) * ‖x - y‖ := by
      simpa only [dist_eq_norm] using hL.dist_le_mul x y
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hinc 2
    have hquot :
        ‖φ x - φ y‖ ^ 2 / ‖x - y‖ ^ ((n : ℝ) + 2 * s) ≤
          (L : ℝ) ^ 2 * ‖x - y‖ ^ (-(n : ℝ) - 2 * s + 2) := by
      have he : -(n : ℝ) - 2 * s + 2 = 2 - ((n : ℝ) + 2 * s) := by ring
      rw [he, Real.rpow_sub hr, Real.rpow_two, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right (by simpa only [mul_pow] using hsq) (by positivity)
    rw [cutoffKernel, ite_eq_left hnear]
    exact hquot.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (by positivity)) (by positivity))
  · have hinc : ‖φ x - φ y‖ ≤ 2 * (M : ℝ) :=
      (norm_sub_le _ _).trans (by linarith [hM x, hM y])
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hinc 2
    have hquot :
        ‖φ x - φ y‖ ^ 2 / ‖x - y‖ ^ ((n : ℝ) + 2 * s) ≤
          (4 * (M : ℝ) ^ 2) * ‖x - y‖ ^ (-((n : ℝ) + 2 * s)) := by
      rw [Real.rpow_neg hr.le, ← div_eq_mul_inv]
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
    have hk := rpow_le_cutoffKernel_of_one_le hs (le_of_not_gt hnear)
    calc
      _ ≤ (4 * (M : ℝ) ^ 2) * ‖x - y‖ ^ (-((n : ℝ) + 2 * s)) := hquot
      _ ≤ (4 * (M : ℝ) ^ 2) * cutoffKernel n s (x - y) :=
        mul_le_mul_of_nonneg_left hk (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (sq_nonneg _)) (cutoffKernel_nonneg _)

/-- For `φ` `L`-Lipschitz with `‖φ x‖ ≤ M` and `0 ≤ n + 2s`, the squared difference quotient of
`φ u` at `(x, y)` is at most `2 M² ‖diffQuot n s u (x, y)‖² + 2 (L² + 4 M²) ‖u y‖²
cutoffKernel n s (x - y)`. -/
theorem norm_diffQuot_mul_sq_le
    (hs : 0 ≤ (n : ℝ) + 2 * s) (hL : LipschitzWith L φ)
    (hM : ∀ x, ‖φ x‖ ≤ M) (u : ℝ^n → ℝ) (x y : ℝ^n) :
    ‖diffQuot n s (fun z ↦ φ z * u z) (x, y)‖ ^ 2 ≤
      2 * (M : ℝ) ^ 2 * ‖diffQuot n s u (x, y)‖ ^ 2 +
        2 * ((L : ℝ) ^ 2 + 4 * (M : ℝ) ^ 2) *
          (‖u y‖ ^ 2 * cutoffKernel n s (x - y)) := by
  have hid : diffQuot n s (fun z ↦ φ z * u z) (x, y) =
      φ x * diffQuot n s u (x, y) + u y * diffQuot n s φ (x, y) := by
    simp only [diffQuot_apply_real]
    ring
  have hφ : (φ x) ^ 2 ≤ (M : ℝ) ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      pow_le_pow_left₀ (norm_nonneg _) (hM x) 2
  have hcut := norm_diffQuot_cutoff_sq_le hs hL hM x y
  simp only [Real.norm_eq_abs, sq_abs] at hcut ⊢
  rw [hid]
  have h₁ := mul_le_mul_of_nonneg_right hφ (sq_nonneg (diffQuot n s u (x, y)))
  have h₂ := mul_le_mul_of_nonneg_left hcut (sq_nonneg (u y))
  nlinarith [sq_nonneg (φ x * diffQuot n s u (x, y) -
    u y * diffQuot n s φ (x, y))]

/-- The finite-exponent quotient gives the distance power of the fractional kernel. -/
theorem norm_diffQuot_rpow {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) (u : ℝ^n → F) (x y : ℝ^n) :
    ‖diffQuot n s u (x, y) (p := p)‖ ^ p.toReal =
      ‖u x - u y‖ ^ p.toReal / ‖x - y‖ ^ ((n : ℝ) + p.toReal * s) := by
  have h := congrArg ENNReal.toReal (enorm_diffQuot_rpow (s := s) u (x, y) hp0 hp)
  simpa only [← ENNReal.toReal_rpow, ENNReal.toReal_div, enorm_eq_nnnorm,
    ENNReal.coe_toReal, coe_nnnorm,
    ENNReal.toReal_ofReal (norm_nonneg _), mul_comm s p.toReal] using h

/-- The Lipschitz bound controls small increments, and the uniform bound controls the tail. -/
theorem norm_diffQuot_cutoff_rpow_le {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (hs : 0 ≤ (n : ℝ) + p.toReal * s) (hL : LipschitzWith L φ)
    (hM : ∀ x, ‖φ x‖ ≤ M) (x y : ℝ^n) :
    ‖diffQuot n s φ (x, y) (p := p)‖ ^ p.toReal ≤
      ((L : ℝ) ^ p.toReal + (2 * (M : ℝ)) ^ p.toReal) *
        cutoffKernel n s (x - y) (p := p.toReal) := by
  have hp' : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  by_cases hxy : x = y
  · subst y
    simp only [diffQuot, sub_self, smul_zero, norm_zero, Real.zero_rpow hp'.ne']
    exact mul_nonneg (by positivity) (cutoffKernel_nonneg _ _)
  have hr : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  rw [norm_diffQuot_rpow hp0 hp]
  by_cases hnear : ‖x - y‖ < 1
  · have hinc : ‖φ x - φ y‖ ≤ (L : ℝ) * ‖x - y‖ := by
      simpa only [dist_eq_norm] using hL.dist_le_mul x y
    have hpow := Real.rpow_le_rpow (norm_nonneg _) hinc hp'.le
    have hquot :
        ‖φ x - φ y‖ ^ p.toReal / ‖x - y‖ ^ ((n : ℝ) + p.toReal * s) ≤
          (L : ℝ) ^ p.toReal * ‖x - y‖ ^ (-(n : ℝ) - p.toReal * s + p.toReal) := by
      rw [show -(n : ℝ) - p.toReal * s + p.toReal =
        p.toReal - ((n : ℝ) + p.toReal * s) by ring,
        Real.rpow_sub hr, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right
        (by simpa only [Real.mul_rpow L.coe_nonneg (norm_nonneg _)] using hpow) (by positivity)
    rw [cutoffKernel, ite_eq_left hnear]
    exact hquot.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (by positivity)) (by positivity))
  · have hinc : ‖φ x - φ y‖ ≤ 2 * (M : ℝ) :=
      (norm_sub_le _ _).trans (by linarith [hM x, hM y])
    have hquot :
        ‖φ x - φ y‖ ^ p.toReal / ‖x - y‖ ^ ((n : ℝ) + p.toReal * s) ≤
          (2 * (M : ℝ)) ^ p.toReal * ‖x - y‖ ^ (-((n : ℝ) + p.toReal * s)) := by
      rw [Real.rpow_neg hr.le, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right
        (Real.rpow_le_rpow (norm_nonneg _) hinc hp'.le) (by positivity)
    exact hquot.trans ((mul_le_mul_of_nonneg_left
      (rpow_le_cutoffKernel_of_one_le hs (le_of_not_gt hnear)) (by positivity)).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity))
          (cutoffKernel_nonneg _ _)))

/-- The weighted product difference splits into the original difference and a cutoff increment. -/
theorem diffQuot_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ℝ≥0∞} (φ : ℝ^n → ℝ) (u : ℝ^n → F) (x y : ℝ^n) :
    diffQuot n s (fun z ↦ φ z • u z) (x, y) (p := p) =
      φ x • diffQuot n s u (x, y) (p := p) +
        diffQuot n s φ (x, y) (p := p) • u y := by
  simp only [diffQuot, smul_sub, smul_eq_mul, mul_smul]
  simp only [sub_smul, smul_sub]
  simp only [smul_comm (φ x) (‖x - y‖ ^ ((n : ℝ) / p.toReal + s))⁻¹]
  abel

/-- A power estimate for a scalar multiplier acting on any real normed codomain. -/
theorem enorm_diffQuot_smul_rpow_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (hs : 0 ≤ (n : ℝ) + p.toReal * s) (hL : LipschitzWith L φ)
    (hM : ∀ x, ‖φ x‖ ≤ M) (u : ℝ^n → F) (x y : ℝ^n) :
    ‖diffQuot n s (fun z ↦ φ z • u z) (x, y) (p := p)‖ₑ ^ p.toReal ≤
      (2 : ℝ≥0∞) ^ p.toReal *
        (ENNReal.ofReal ((M : ℝ) ^ p.toReal) *
            ‖diffQuot n s u (x, y) (p := p)‖ₑ ^ p.toReal +
          ENNReal.ofReal ((L : ℝ) ^ p.toReal + (2 * (M : ℝ)) ^ p.toReal) *
            (‖u y‖ₑ ^ p.toReal *
              ENNReal.ofReal (cutoffKernel n s (x - y) (p := p.toReal)))) := by
  have hp' : 0 ≤ p.toReal := ENNReal.toReal_nonneg
  have hφ : ‖φ x‖ₑ ^ p.toReal ≤ ENNReal.ofReal ((M : ℝ) ^ p.toReal) := by
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp']
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) (hM x) hp')
  have hcut := ENNReal.ofReal_le_ofReal (norm_diffQuot_cutoff_rpow_le hp0 hp hs hL hM x y)
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp', ofReal_norm,
    ENNReal.ofReal_mul (by positivity)] at hcut
  rw [diffQuot_smul]
  calc
    _ ≤ (‖φ x • diffQuot n s u (x, y) (p := p)‖ₑ +
          ‖diffQuot n s φ (x, y) (p := p) • u y‖ₑ) ^ p.toReal :=
      ENNReal.rpow_le_rpow (enorm_add_le _ _) hp'
    _ ≤ _ := (ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow _ _ hp').trans (by
      simp only [enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ hp']
      calc
        _ ≤ (2 : ℝ≥0∞) ^ p.toReal *
            (ENNReal.ofReal ((M : ℝ) ^ p.toReal) *
                ‖diffQuot n s u (x, y) (p := p)‖ₑ ^ p.toReal +
              (ENNReal.ofReal ((L : ℝ) ^ p.toReal + (2 * (M : ℝ)) ^ p.toReal) *
                ENNReal.ofReal (cutoffKernel n s (x - y) (p := p.toReal))) *
                ‖u y‖ₑ ^ p.toReal) := by gcongr
        _ = _ := by ac_rfl)

end SobolevSpace.Fractional.Localization
