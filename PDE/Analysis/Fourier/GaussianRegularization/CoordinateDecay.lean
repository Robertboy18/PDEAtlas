/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.GaussianRegularization.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Gaussian kernel decay from one frequency coordinate

Fubini separates one frequency coordinate of the operator exponential.
Only that coordinate is shifted into the complex plane; the remaining real
coordinates are controlled by scalar Gaussian integrals. No commutation of the
operators is required.
-/

@[expose] public noncomputable section

open MeasureTheory Complex

namespace PDE.Analysis.Fourier

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
variable {n : ℕ}

omit [CompleteSpace A] in
private theorem integral_eq_integral_insertNth
    {f : (Fin (n + 1) → ℝ) → A} (hf : Integrable f) (i : Fin (n + 1)) :
    ∫ x, f x = ∫ y : Fin n → ℝ, ∫ t : ℝ, f (i.insertNth t y) := by
  have hmp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) i).symm
  rw [← hmp.integral_comp' f]
  change (∫ x, (f ∘ (MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) ↦ ℝ) i).symm) x ∂volume.prod volume) = _
  rw [integral_prod_symm _ (hmp.integrable_comp_of_integrable hf)]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Function.comp_apply]

omit [CompleteSpace A] in
/-- Separate a frequency coordinate without splitting the operator exponential
into commuting factors. -/
theorem gaussianExponentialIntegrand_insertNth
    (S : Fin (n + 1) → A) (b : ℝ) (k : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (t : ℝ) (y : Fin n → ℝ) :
    gaussianExponentialIntegrand S b k (i.insertNth t y) =
      Complex.exp ((-(b * ∑ j, y j ^ 2) : ℝ) +
        (∑ j, k (i.succAbove j) * y j : ℝ) * I) •
      (Complex.exp (-(b : ℂ) * (t : ℂ) ^ 2 + (k i : ℂ) * I * t) •
        NormedSpace.exp ((∑ j, (y j : ℂ) • S (i.succAbove j)) + (t : ℂ) • S i)) := by
  unfold gaussianExponentialIntegrand
  rw [Fin.sum_univ_succAbove
    (fun j ↦ (i.insertNth t y : Fin (n + 1) → ℝ) j ^ 2) i,
    Fin.sum_univ_succAbove
      (fun j ↦ k j * (i.insertNth t y : Fin (n + 1) → ℝ) j) i,
    Fin.sum_univ_succAbove
      (fun j ↦ ((i.insertNth t y : Fin (n + 1) → ℝ) j : ℂ) • S j) i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  rw [smul_smul, ← Complex.exp_add, add_comm ((t : ℂ) • S i)]
  congr 2
  push_cast
  ring

/-- The shifted coordinate supplies Gaussian decay; the other coordinates
retain integrable scalar Gaussian majorants. -/
theorem norm_integral_gaussianExponentialIntegrand_insertNth_le
    (h₁ : ‖(1 : A)‖ ≤ 1) (S : Fin (n + 1) → A) {b : ℝ} (hb : 0 < b)
    (k : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (y : Fin n → ℝ) :
    ‖∫ t : ℝ, gaussianExponentialIntegrand S b k (i.insertNth t y)‖ ≤
      (√(Real.pi / (b / 2)) *
        Real.exp (-(k i ^ 2 / (4 * b)) + ‖S i‖ * |k i / (2 * b)| +
          ‖S i‖ ^ 2 / (2 * b))) *
        ∏ j, Real.exp (‖S (i.succAbove j)‖ ^ 2 / (2 * b)) *
          Real.exp (-(b / 2) * y j ^ 2) := by
  simp_rw [gaussianExponentialIntegrand_insertNth]
  rw [integral_smul, norm_smul, Complex.norm_exp]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero,
    I_im, zero_mul, sub_zero, add_zero]
  let R : A := ∑ j, (y j : ℂ) • S (i.succAbove j)
  let C : ℝ := √(Real.pi / (b / 2)) *
    Real.exp (-(k i ^ 2 / (4 * b)) + ‖S i‖ * |k i / (2 * b)| +
      ‖S i‖ ^ 2 / (2 * b))
  have hC : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  calc
    _ ≤ Real.exp (-(b * ∑ j, y j ^ 2)) * (Real.exp ‖R‖ * C) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      simpa only [C, R, mul_assoc] using
        norm_integral_gaussian_phase_exp_le h₁ R (S i) hb (k i)
    _ = C * Real.exp (-(b * ∑ j, y j ^ 2) + ‖R‖) := by
      rw [Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (exp_neg_mul_sum_sq_add_norm_sum_smul_le (fun j ↦ S (i.succAbove j)) hb y) hC

/-- A bound for the full kernel obtained by shifting any one frequency
coordinate and integrating the remaining scalar Gaussian majorants. -/
theorem norm_gaussianExponentialKernel_le_coordinate
    (h₁ : ‖(1 : A)‖ ≤ 1) (S : Fin (n + 1) → A) {b : ℝ} (hb : 0 < b)
    (k : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    ‖gaussianExponentialKernel S b k‖ ≤
      (√(Real.pi / (b / 2)) *
        Real.exp (-(k i ^ 2 / (4 * b)) + ‖S i‖ * |k i / (2 * b)| +
          ‖S i‖ ^ 2 / (2 * b))) *
        ∏ j, Real.exp (‖S (i.succAbove j)‖ ^ 2 / (2 * b)) *
          √(Real.pi / (b / 2)) := by
  rw [gaussianExponentialKernel, integral_eq_integral_insertNth
    (integrable_gaussianExponentialIntegrand h₁ S hb k) i]
  let C : ℝ := √(Real.pi / (b / 2)) *
    Real.exp (-(k i ^ 2 / (4 * b)) + ‖S i‖ * |k i / (2 * b)| +
      ‖S i‖ ^ 2 / (2 * b))
  have hg : Integrable (fun y : Fin n → ℝ ↦ C *
      ∏ j, Real.exp (‖S (i.succAbove j)‖ ^ 2 / (2 * b)) *
        Real.exp (-(b / 2) * y j ^ 2)) :=
    (Integrable.fintype_prod fun j ↦
      (integrable_exp_neg_mul_sq (half_pos hb)).const_mul _).const_mul C
  calc
    _ ≤ ∫ y : Fin n → ℝ, C *
        ∏ j, Real.exp (‖S (i.succAbove j)‖ ^ 2 / (2 * b)) *
          Real.exp (-(b / 2) * y j ^ 2) :=
      norm_integral_le_of_norm_le hg (ae_of_all _ fun y ↦
        norm_integral_gaussianExponentialIntegrand_insertNth_le h₁ S hb k i y)
    _ = _ := by
      rw [integral_const_mul, integral_fintype_prod_volume_eq_prod
        (fun (j : Fin n) (x : ℝ) ↦ Real.exp (‖S (i.succAbove j)‖ ^ 2 / (2 * b)) *
          Real.exp (-(b / 2) * x ^ 2))]
      simp_rw [integral_const_mul, integral_gaussian]
      rfl

/-- A simpler Gaussian bound, with the growth absorbed into the sum of squared
operator norms. The negative coordinate term will dominate this growth outside
a sufficiently large spatial cone. -/
theorem norm_gaussianExponentialKernel_le_coordinate_sq
    (h₁ : ‖(1 : A)‖ ≤ 1) (S : Fin (n + 1) → A) {b : ℝ} (hb : 0 < b)
    (k : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    ‖gaussianExponentialKernel S b k‖ ≤
      √(Real.pi / (b / 2)) ^ (n + 1) *
        Real.exp ((-(k i ^ 2 / 8) + ∑ j, ‖S j‖ ^ 2) / b) := by
  have hprod :
      (∏ j : Fin n, Real.exp (‖S (i.succAbove j)‖ ^ 2 / (2 * b)) *
        √(Real.pi / (b / 2))) =
      Real.exp (∑ j : Fin n, ‖S (i.succAbove j)‖ ^ 2 / (2 * b)) *
        √(Real.pi / (b / 2)) ^ n := by
    rw [Finset.prod_mul_distrib, ← Real.exp_sum]
    simp only [Finset.prod_const, Finset.card_fin]
  have hy := two_mul_le_add_mul_sq (a := |k i|) (b := ‖S i‖)
    (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [sq_abs] at hy
  norm_num at hy
  have hrest : 0 ≤ ∑ j : Fin n, ‖S (i.succAbove j)‖ ^ 2 :=
    Finset.sum_nonneg fun j _ ↦ sq_nonneg _
  have hnum :
      -(k i ^ 2 / 4) + ‖S i‖ * |k i| / 2 + ‖S i‖ ^ 2 / 2 +
        (∑ j : Fin n, ‖S (i.succAbove j)‖ ^ 2) / 2 ≤
      -(k i ^ 2 / 8) + (‖S i‖ ^ 2 + ∑ j : Fin n, ‖S (i.succAbove j)‖ ^ 2) := by
    nlinarith
  apply (norm_gaussianExponentialKernel_le_coordinate h₁ S hb k i).trans
  rw [hprod]
  calc
    _ = √(Real.pi / (b / 2)) ^ (n + 1) *
        Real.exp (-(k i ^ 2 / (4 * b)) + ‖S i‖ * |k i / (2 * b)| +
          ‖S i‖ ^ 2 / (2 * b) + ∑ j : Fin n, ‖S (i.succAbove j)‖ ^ 2 / (2 * b)) := by
      simp only [Real.exp_add, pow_succ]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Real.sqrt_nonneg _) _)
      apply Real.exp_le_exp.mpr
      rw [Fin.sum_univ_succAbove (fun j ↦ ‖S j‖ ^ 2) i,
        ← Finset.sum_div, abs_div, abs_of_pos (mul_pos two_pos hb)]
      calc
        _ = (-(k i ^ 2 / 4) + ‖S i‖ * |k i| / 2 + ‖S i‖ ^ 2 / 2 +
            (∑ j : Fin n, ‖S (i.succAbove j)‖ ^ 2) / 2) / b := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hnum hb.le

/-- A positive coordinate gap yields a bound independent of the remaining
phase coordinates. This form allows the coefficients and phase to vary
through a family with the same gap. -/
theorem norm_gaussianExponentialKernel_le_of_coordinate_gap
    (h₁ : ‖(1 : A)‖ ≤ 1) (S : Fin (n + 1) → A) {b : ℝ} (hb : 0 < b)
    (k : Fin (n + 1) → ℝ) (i : Fin (n + 1)) {δ : ℝ}
    (hgap : (∑ j, ‖S j‖ ^ 2) + δ ≤ k i ^ 2 / 8) :
    ‖gaussianExponentialKernel S b k‖ ≤
      √(Real.pi / (b / 2)) ^ (n + 1) * Real.exp (-δ / b) := by
  apply (norm_gaussianExponentialKernel_le_coordinate_sq h₁ S hb k i).trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Real.sqrt_nonneg _) _)
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ hb.le
  linarith

end PDE.Analysis.Fourier
