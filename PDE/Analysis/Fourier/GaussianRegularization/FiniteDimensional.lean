/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.GaussianRegularization.OperatorExponential
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Gaussian regularization of finite-dimensional operator symbols

The Gaussian-regularized inverse Fourier kernel uses the exponential of
a linear operator pencil. Scalar Gaussian bounds establish absolute
integrability before any change of integration order. Frequencies are written
as a finite real product; setting `k = 2π y` gives the inverse Fourier convention.
-/

@[expose] public noncomputable section

open MeasureTheory Complex

namespace PDE.Analysis.Fourier

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
variable {n : ℕ}

/-- The integrand of the Gaussian-regularized inverse Fourier kernel of a
constant operator pencil. The operators are not required to commute. -/
def gaussianExponentialIntegrand (S : Fin n → A) (b : ℝ) (k x : Fin n → ℝ) : A :=
  Complex.exp ((-(b * ∑ j, x j ^ 2) : ℝ) + (∑ j, k j * x j : ℝ) * I) •
    NormedSpace.exp (∑ j, (x j : ℂ) • S j)

/-- The Gaussian-regularized kernel. The phase is `k · x`; for the inverse
Fourier transform with Mathlib's convention, take `k = 2π y`. -/
def gaussianExponentialKernel (S : Fin n → A) (b : ℝ) (k : Fin n → ℝ) : A :=
  ∫ x, gaussianExponentialIntegrand S b k x

/-- The exponential growth of a linear pencil is absorbed by a product
of scalar Gaussians. -/
theorem exp_neg_mul_sum_sq_add_norm_sum_smul_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S : Fin n → E) {b : ℝ} (hb : 0 < b) (x : Fin n → ℝ) :
    Real.exp (-(b * ∑ j, x j ^ 2) + ‖∑ j, (x j : ℂ) • S j‖) ≤
      ∏ j, Real.exp (‖S j‖ ^ 2 / (2 * b)) * Real.exp (-(b / 2) * x j ^ 2) := by
  have hsum : ‖∑ j, (x j : ℂ) • S j‖ ≤ ∑ j, ‖S j‖ * |x j| := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
  have hy (j : Fin n) :
      -b * x j ^ 2 + ‖S j‖ * |x j| ≤
        ‖S j‖ ^ 2 / (2 * b) + -(b / 2) * x j ^ 2 := by
    have h := two_mul_le_add_mul_sq (a := |x j|) (b := ‖S j‖) hb
    rw [sq_abs] at h
    ring_nf at h ⊢
    linarith
  calc
    _ ≤ Real.exp (-(b * ∑ j, x j ^ 2) + ∑ j, ‖S j‖ * |x j|) :=
      Real.exp_le_exp.mpr (add_le_add le_rfl hsum)
    _ = Real.exp (∑ j, (-b * x j ^ 2 + ‖S j‖ * |x j|)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, neg_mul]
    _ ≤ Real.exp (∑ j, (‖S j‖ ^ 2 / (2 * b) + -(b / 2) * x j ^ 2)) :=
      Real.exp_le_exp.mpr (Finset.sum_le_sum fun j _ ↦ hy j)
    _ = _ := by simp only [Real.exp_sum, Real.exp_add]

omit [CompleteSpace A] in
/-- A product of scalar Gaussians dominates the operator integrand. -/
theorem norm_gaussianExponentialIntegrand_le
    (h₁ : ‖(1 : A)‖ ≤ 1) (S : Fin n → A) {b : ℝ} (hb : 0 < b)
    (k x : Fin n → ℝ) :
    ‖gaussianExponentialIntegrand S b k x‖ ≤
      ∏ j, Real.exp (‖S j‖ ^ 2 / (2 * b)) * Real.exp (-(b / 2) * x j ^ 2) := by
  let : NormedAlgebra ℝ A := NormedAlgebra.restrictScalars ℝ ℂ A
  rw [gaussianExponentialIntegrand, norm_smul, Complex.norm_exp]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero,
    I_im, zero_mul, sub_zero, add_zero]
  calc
    _ ≤ Real.exp (-(b * ∑ j, x j ^ 2)) * Real.exp ‖∑ j, (x j : ℂ) • S j‖ :=
      mul_le_mul_of_nonneg_left
        (NormedSpace.norm_exp_le_exp_norm_of_norm_one_le h₁ _) (Real.exp_pos _).le
    _ = Real.exp (-(b * ∑ j, x j ^ 2) + ‖∑ j, (x j : ℂ) • S j‖) :=
      (Real.exp_add _ _).symm
    _ ≤ _ := exp_neg_mul_sum_sq_add_norm_sum_smul_le S hb x

/-- Gaussian regularization makes every finite constant operator symbol
integrable, including the zero-dimensional frequency space and the zero algebra. -/
theorem integrable_gaussianExponentialIntegrand
    (h₁ : ‖(1 : A)‖ ≤ 1) (S : Fin n → A) {b : ℝ} (hb : 0 < b)
    (k : Fin n → ℝ) :
    Integrable (gaussianExponentialIntegrand S b k) := by
  have hg : Integrable (fun x : Fin n → ℝ ↦
      ∏ j, Real.exp (‖S j‖ ^ 2 / (2 * b)) * Real.exp (-(b / 2) * x j ^ 2)) :=
    Integrable.fintype_prod fun j ↦
      (integrable_exp_neg_mul_sq (half_pos hb)).const_mul _
  apply hg.mono'
  · have hexp : Continuous (NormedSpace.exp : A → A) :=
      continuous_iff_continuousAt.mpr
        (fun R ↦ (NormedSpace.exp_analytic (𝕂 := ℂ) R).continuousAt)
    have hcont : Continuous (gaussianExponentialIntegrand S b k) := by
      unfold gaussianExponentialIntegrand
      fun_prop
    exact hcont.aestronglyMeasurable
  · exact ae_of_all _ (norm_gaussianExponentialIntegrand_le h₁ S hb k)

end PDE.Analysis.Fourier
