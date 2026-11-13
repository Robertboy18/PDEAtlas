/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.StationaryPhase.Fresnel
public import PDE.Common.Euclidean

/-!
# Fourier transforms of diagonal complex Gaussians

Different quadratic coefficients in each orthogonal direction allow indefinite
quadratic phases after the positive damping tends to zero.
-/

@[expose] public noncomputable section

open MeasureTheory Complex
open scoped FourierTransform RealInnerProductSpace

namespace PDE.Analysis.StationaryPhase

variable {n : ℕ}

/-- Coordinatewise Gaussian integrability in Euclidean space. -/
theorem integrable_cexp_neg_sum_mul_sq {b : Fin n → ℂ}
    (hb : ∀ i, 0 < (b i).re) :
    Integrable (fun x : ℝ^n ↦ Complex.exp (-∑ i, b i * (x i : ℂ) ^ 2)) := by
  rw [← (PiLp.volume_preserving_toLp (Fin n)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  simpa [Function.comp_def] using
    GaussianFourier.integrable_cexp_neg_sum_mul_add hb (fun _ ↦ 0)

/-- The Fourier transform of a diagonal Gaussian, for the `2π` Fourier convention. -/
theorem fourier_cexp_neg_sum_mul_sq {b : Fin n → ℂ}
    (hb : ∀ i, 0 < (b i).re) (w : ℝ^n) :
    (𝓕 (fun x : ℝ^n ↦ Complex.exp (-∑ i, b i * (x i : ℂ) ^ 2))) w =
      (∏ i, ((Real.pi : ℂ) / b i) ^ (1 / 2 : ℂ)) *
        Complex.exp (-Real.pi ^ 2 * ∑ i, (w i : ℂ) ^ 2 / b i) := by
  rw [Real.fourier_eq',
    ← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
      (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  have heq (x : Fin n → ℝ) :
      Complex.exp (((-2 * Real.pi * ⟪WithLp.toLp 2 x, w⟫ : ℝ) : ℂ) * I) *
        Complex.exp (-∑ i, b i * (x i : ℂ) ^ 2) =
      Complex.exp (-∑ i, b i * (x i : ℂ) ^ 2 +
        ∑ i, (-2 * Real.pi * I * (w i : ℂ)) * x i) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, ofReal_neg,
      ofReal_mul, ofReal_ofNat, ofReal_sum, Finset.mul_sum, Finset.sum_mul]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [smul_eq_mul]
  simp_rw [heq]
  rw [GaussianFourier.integral_cexp_neg_sum_mul_add hb,
    Finset.prod_mul_distrib, ← Complex.exp_sum]
  congr 2
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_pow, I_sq]
  ring

end PDE.Analysis.StationaryPhase
