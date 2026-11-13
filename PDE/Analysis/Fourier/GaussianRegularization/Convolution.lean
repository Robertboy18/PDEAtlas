/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.GaussianRegularization.FiniteDimensional
public import PDE.Common.Euclidean

/-!
# Convolution by Gaussian-regularized operator kernels

Mathlib's bilinear Fourier pairing identifies the regularized inverse
transform with the kernel acting on the original data. The coordinate product
measure and Euclidean volume agree through the native measure equivalence.
-/

@[expose] public noncomputable section

open MeasureTheory Complex
open scoped FourierTransform RealInnerProductSpace

namespace PDE.Analysis.Fourier

variable {n : ℕ}

section Algebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- Fourier transformation subtracts `2π y` from the phase of the
Gaussian operator integrand. This also identifies the coordinate kernel with
the Euclidean-volume integral. -/
theorem fourier_gaussianExponentialIntegrand
    (S : Fin n → A) (b : ℝ) (k : Fin n → ℝ) (y : ℝ^n) :
    𝓕 (fun ξ : ℝ^n ↦ gaussianExponentialIntegrand S b k (WithLp.ofLp ξ)) y =
      gaussianExponentialKernel S b (fun j ↦ k j - 2 * Real.pi * y j) := by
  calc
    _ = ∫ ξ : ℝ^n, gaussianExponentialIntegrand S b
        (fun j ↦ k j - 2 * Real.pi * y j) (WithLp.ofLp ξ) := by
      simp only [Real.fourier_eq']
      apply integral_congr_ae
      filter_upwards with ξ
      have hphase : (∑ j, (k j - 2 * Real.pi * y j) * ξ j) =
          (∑ j, k j * ξ j) - 2 * Real.pi * ⟪ξ, y⟫ := by
        simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, sub_mul,
          Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
      unfold gaussianExponentialIntegrand
      rw [smul_smul, ← Complex.exp_add, hphase]
      congr 2
      push_cast
      ring
    _ = _ := (PiLp.volume_preserving_ofLp (Fin n)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding _

end Algebra

section Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A Gaussian-regularized operator multiplier acts by its spatial
kernel. Only integrability of the original datum is assumed. -/
theorem integral_gaussianExponential_fourier_eq
    (S : Fin n → E →L[ℂ] E) {b : ℝ} (hb : 0 < b) (k : Fin n → ℝ)
    {f : ℝ^n → E} (hf : Integrable f) :
    (∫ ξ : ℝ^n, gaussianExponentialIntegrand S b k (WithLp.ofLp ξ) (𝓕 f ξ)) =
      ∫ y : ℝ^n, gaussianExponentialKernel S b
        (fun j ↦ k j - 2 * Real.pi * y j) (f y) := by
  have hG : Integrable
      (fun ξ : ℝ^n ↦ gaussianExponentialIntegrand S b k (WithLp.ofLp ξ)) :=
    (PiLp.volume_preserving_ofLp (Fin n)).integrable_comp_of_integrable
      (integrable_gaussianExponentialIntegrand
        (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := E)) S hb k)
  calc
    _ = ∫ y : ℝ^n,
        (𝓕 (fun ξ : ℝ^n ↦ gaussianExponentialIntegrand S b k (WithLp.ofLp ξ)) y)
          (f y) := by
      simpa [Real.fourier_eq, VectorFourier.fourierIntegral] using
        (VectorFourier.integral_bilin_fourierIntegral_eq_flip
          (L := innerₗ (ℝ^n))
          (ContinuousLinearMap.apply ℂ E) Real.continuous_fourierChar continuous_inner
          hf hG)
    _ = _ := by simp_rw [fourier_gaussianExponentialIntegrand]

end Operator

end PDE.Analysis.Fourier
