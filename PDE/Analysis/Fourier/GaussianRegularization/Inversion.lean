/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Fourier.Inversion

/-!
# Gaussian-regularized inversion at continuity points

The regularized inverse Fourier integrals converge for integrable data at every
continuity point, without integrability of the unregularized Fourier transform.
The proof uses Mathlib's Fourier pairing identity and Gaussian approximate
identity. The Fourier phase is `2π ⟪v,w⟫`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Complex
open scoped Topology FourierTransform RealInnerProductSpace

namespace PDE.Analysis.Fourier

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The Gaussian-regularized inverse Fourier integral equals convolution with
the Gaussian approximate identity. -/
theorem integral_gaussian_fourier_smul_eq
    {f : V → E} (hf : Integrable f) {c : ℝ} (hc : 0 < c) (v : V) :
    (∫ w : V, Complex.exp (-(c⁻¹ : ℝ) * ‖w‖ ^ 2 +
      2 * Real.pi * I * ⟪v, w⟫) • (𝓕 f) w) =
    ∫ w : V, (((Real.pi * c : ℝ) : ℂ) ^ (Module.finrank ℝ V / 2 : ℂ) *
      Complex.exp (-Real.pi ^ 2 * c * ‖v - w‖ ^ 2)) • f w := by
  have hg : Integrable (fun w : V ↦ Complex.exp (-(c⁻¹ : ℝ) * ‖w‖ ^ 2 +
      2 * Real.pi * I * ⟪v, w⟫)) :=
    GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (by simpa) _ _
  calc
    _ = ∫ w : V, (𝓕 (fun z : V ↦ Complex.exp (-(c⁻¹ : ℝ) * ‖z‖ ^ 2 +
        2 * Real.pi * I * ⟪v, z⟫))) w • f w := by
      simpa [Real.fourier_eq, VectorFourier.fourierIntegral] using
        (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ V)
        Real.continuous_fourierChar continuous_inner hg hf).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with w
      rw [fourier_gaussian_innerProductSpace' (by simpa)]
      congr 2
      · simp
      · congr 1
        simp
        ring

/-- Gaussian-regularized inverse Fourier integrals recover any integrable
function at its continuity points. -/
theorem tendsto_integral_gaussian_fourier_smul
    {f : V → E} (hf : Integrable f) {v : V} (hv : ContinuousAt f v) :
    Tendsto (fun c : ℝ ↦ ∫ w : V, Complex.exp (-(c⁻¹ : ℝ) * ‖w‖ ^ 2 +
      2 * Real.pi * I * ⟪v, w⟫) • (𝓕 f) w) atTop (𝓝 (f v)) := by
  apply (Real.tendsto_integral_gaussian_smul' hf hv).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  simpa only [Complex.ofReal_mul] using (integral_gaussian_fourier_smul_eq hf hc v).symm

end PDE.Analysis.Fourier
