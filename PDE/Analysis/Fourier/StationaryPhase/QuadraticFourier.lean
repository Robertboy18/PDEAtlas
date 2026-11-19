/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.StationaryPhase.DiagonalGaussian
public import Mathlib.Analysis.Fourier.Inversion

/-!
# Removing the damping from quadratic Fourier integrals

The Fourier pairing identity for integrable Gaussians passes to the imaginary
boundary by dominated convergence. Integrability of both a function and its
Fourier transform suffices.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Complex
open scoped Topology FourierTransform RealInnerProductSpace

namespace PDE.Analysis.StationaryPhase

variable {n : ℕ}

/-- A diagonal Gaussian with nonnegative real coefficients has modulus at most one. -/
theorem norm_cexp_neg_sum_mul_sq_le_one {c : Fin n → ℂ}
    (hc : ∀ i, 0 ≤ (c i).re) (x : ℝ^n) :
    ‖Complex.exp (-∑ i, c i * (x i : ℂ) ^ 2)‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  simp only [Complex.neg_re, Complex.re_sum, Complex.mul_re,
    ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    neg_nonpos]
  exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hc i) (sq_nonneg _)

/-- Fourier-side Gaussian multipliers obey the same uniform modulus bound. -/
theorem norm_cexp_neg_pi_sq_sum_div_le_one {c : Fin n → ℂ}
    (hc : ∀ i, 0 ≤ (c i).re) (x : ℝ^n) :
    ‖Complex.exp (-Real.pi ^ 2 * ∑ i, (x i : ℂ) ^ 2 / c i)‖ ≤ 1 := by
  have heq : -((Real.pi : ℂ) ^ 2) * ∑ i, (x i : ℂ) ^ 2 / c i =
      -∑ i, ((Real.pi : ℂ) ^ 2 / c i) * (x i : ℂ) ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq]
  apply norm_cexp_neg_sum_mul_sq_le_one
  intro i
  simp only [Complex.div_re, ← Complex.ofReal_pow, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, zero_div, add_zero]
  exact div_nonneg (mul_nonneg (sq_nonneg _) (hc i)) (Complex.normSq_nonneg _)

/-- Boundary convergence of the finite product of Gaussian normalizations. -/
theorem tendsto_prod_gaussian_coefficient {b : Fin n → ℝ} (hb : ∀ i, b i ≠ 0) :
    Tendsto (fun ε : ℝ ↦
      ∏ i, ((Real.pi : ℂ) / ((ε : ℂ) - b i * I)) ^ (1 / 2 : ℂ))
      (𝓝[>] 0)
      (𝓝 (∏ i, (Real.sqrt (Real.pi / |b i|) : ℂ) *
        Complex.exp (Real.pi / 4 * (Real.sign (b i) : ℂ) * I))) := by
  apply tendsto_finsetProd
  intro i _
  apply (tendsto_integral_damped_fresnel (hb i)).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact integral_gaussian_complex (by simpa using hε)

/-- Gaussian damping can be removed from Fourier pairing for an invertible
diagonal real quadratic form. Both integrability assumptions are automatic for
a smooth compactly supported amplitude and its Fourier transform. -/
theorem integral_cexp_quadratic_mul_fourier {b : Fin n → ℝ}
    (hb : ∀ i, b i ≠ 0) {f : ℝ^n → ℂ}
    (hf : Integrable f) (hff : Integrable (𝓕 f)) :
    (∫ x : ℝ^n, Complex.exp (-∑ i, (-(b i : ℂ) * I) * (x i : ℂ) ^ 2) *
      (𝓕 f) x) =
    (∏ i, (Real.sqrt (Real.pi / |b i|) : ℂ) *
      Complex.exp (Real.pi / 4 * (Real.sign (b i) : ℂ) * I)) *
    ∫ x : ℝ^n, Complex.exp (-Real.pi ^ 2 *
      ∑ i, (x i : ℂ) ^ 2 / (-(b i : ℂ) * I)) * f x := by
  let c (ε : ℝ) (i : Fin n) : ℂ := (ε : ℂ) - b i * I
  have hc (ε : ℝ) (i : Fin n) : (c ε i).re = ε := by simp [c]
  have hlim (i : Fin n) :
      Tendsto (fun ε : ℝ ↦ c ε i) (𝓝[>] 0) (𝓝 (-(b i : ℂ) * I)) := by
    simpa [c] using
      (Complex.continuous_ofReal.tendsto 0 |>.mono_left nhdsWithin_le_nhds).sub_const
        ((b i : ℂ) * I)
  have hne (i : Fin n) : -(b i : ℂ) * I ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (hb i))) I_ne_zero
  have hleft : Tendsto (fun ε : ℝ ↦ ∫ x : ℝ^n,
      Complex.exp (-∑ i, c ε i * (x i : ℂ) ^ 2) * (𝓕 f) x)
      (𝓝[>] 0)
      (𝓝 (∫ x : ℝ^n,
        Complex.exp (-∑ i, (-(b i : ℂ) * I) * (x i : ℂ) ^ 2) * (𝓕 f) x)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖(𝓕 f) x‖)
    · exact Eventually.of_forall fun ε ↦
        (show Continuous (fun x : ℝ^n ↦
          Complex.exp (-∑ i, c ε i * (x i : ℂ) ^ 2)) by
          fun_prop).aestronglyMeasurable.mul hff.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards with x
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (norm_cexp_neg_sum_mul_sq_le_one (fun i ↦ by simpa [hc] using hε.le) x)
    · exact hff.norm
    · filter_upwards with x
      apply Tendsto.mul_const
      apply Tendsto.cexp
      apply Tendsto.neg
      exact tendsto_finsetSum _ fun i _ ↦ (hlim i).mul_const _
  have hright : Tendsto (fun ε : ℝ ↦ ∫ x : ℝ^n,
      Complex.exp (-Real.pi ^ 2 * ∑ i, (x i : ℂ) ^ 2 / c ε i) * f x)
      (𝓝[>] 0)
      (𝓝 (∫ x : ℝ^n, Complex.exp (-Real.pi ^ 2 *
        ∑ i, (x i : ℂ) ^ 2 / (-(b i : ℂ) * I)) * f x)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖f x‖)
    · exact Eventually.of_forall fun ε ↦
        (show Continuous (fun x : ℝ^n ↦ Complex.exp
          (-Real.pi ^ 2 * ∑ i, (x i : ℂ) ^ 2 / c ε i)) by
          fun_prop).aestronglyMeasurable.mul hf.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards with x
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (norm_cexp_neg_pi_sq_sum_div_le_one (fun i ↦ by simpa [hc] using hε.le) x)
    · exact hf.norm
    · filter_upwards with x
      apply Tendsto.mul_const
      apply Tendsto.cexp
      apply Tendsto.const_mul
      exact tendsto_finsetSum _ fun i _ ↦ tendsto_const_nhds.div (hlim i) (hne i)
  apply tendsto_nhds_unique hleft
  apply ((tendsto_prod_gaussian_coefficient hb).mul hright).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hg := integrable_cexp_neg_sum_mul_sq (b := c ε) (fun i ↦ by
    simpa [hc] using hε)
  calc
    _ = ∫ x : ℝ^n, (𝓕 (fun y : ℝ^n ↦
        Complex.exp (-∑ i, c ε i * (y i : ℂ) ^ 2))) x * f x := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      rw [fourier_cexp_neg_sum_mul_sq (fun i ↦ by simpa [hc] using hε)]
      simp [c, mul_assoc]
    _ = _ := by
      simpa [Real.fourier_eq, VectorFourier.fourierIntegral, smul_eq_mul] using
        (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ (ℝ^n))
          Real.continuous_fourierChar continuous_inner hg hf)

end PDE.Analysis.StationaryPhase
