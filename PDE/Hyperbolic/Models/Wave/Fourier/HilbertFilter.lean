/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.Schwartz.HilbertDerivatives
public import PDE.Hyperbolic.Models.Wave.Fourier.Representation

/-!
# Hilbert filters in the one-dimensional wave formula

For an odd absolute frequency power, the initial data in the characteristic
formula are Hilbert transforms of odd derivatives. Their principal values
converge because the original data are Schwartz functions. The filtered
Fourier transforms are integrable, so the inverse-transform wave formula
applies without requiring the Hilbert transforms themselves to be Schwartz.

This supplies the one-dimensional step in the even-dimensional Radon wave
formula. All interval integrals are oriented, including at negative time.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap

namespace WaveEquation.Fourier

private theorem integrable_abs_pow_smul_fourier (f : 𝓢(ℝ, ℂ)) (n : ℕ) :
    Integrable (fun σ : ℝ ↦ |σ| ^ n • 𝓕 (f : ℝ → ℂ) σ) := by
  have hc : Continuous (fun σ : ℝ ↦ |σ| ^ n • 𝓕 (f : ℝ → ℂ) σ) :=
    (continuous_abs.pow n).smul (𝓕 f).continuous
  apply (integrable_norm_iff hc.aestronglyMeasurable).mp
  simpa only [norm_smul, Real.norm_eq_abs, abs_pow, abs_abs] using (𝓕 f).integrable_pow_mul volume n

/-- An odd absolute frequency filter gives the characteristic integral of
Hilbert principal values of the odd derivatives of the real initial data. -/
theorem hilbertFiltered_fourierSolution_eq_characteristicIntegral
    (g h : 𝓢(ℝ, ℝ)) (k : ℕ) (s t : ℝ) :
    𝓕⁻ (fun σ : ℝ ↦ |σ| ^ (2 * k + 1) •
      ((Real.cos (2 * Real.pi * σ * t) : ℂ) * 𝓕 (fun y ↦ (g y : ℂ)) σ +
        (t * Real.sinc (2 * Real.pi * σ * t) : ℝ) *
          𝓕 (fun y ↦ (h y : ℂ)) σ)) s =
      (((-1 : ℝ) ^ k / (2 * (2 * Real.pi) ^ (2 * k + 1))) *
        (PDE.Analysis.hilbertPV (iteratedDeriv (2 * k + 1) g) (s + t) +
          PDE.Analysis.hilbertPV (iteratedDeriv (2 * k + 1) g) (s - t) +
          ∫ y in s - t..s + t,
            PDE.Analysis.hilbertPV (iteratedDeriv (2 * k + 1) h) y) : ℝ) := by
  let G : ℝ → ℂ := fun σ ↦ |σ| ^ (2 * k + 1) • 𝓕 (fun y ↦ (g y : ℂ)) σ
  let H : ℝ → ℂ := fun σ ↦ |σ| ^ (2 * k + 1) • 𝓕 (fun y ↦ (h y : ℂ)) σ
  have hG : Integrable G := integrable_abs_pow_smul_fourier (g.postcompCLM Complex.ofRealCLM) _
  have hH : Integrable H := integrable_abs_pow_smul_fourier (h.postcompCLM Complex.ofRealCLM) _
  have hHc : Continuous H :=
    (continuous_abs.pow _).smul (𝓕 (h.postcompCLM Complex.ofRealCLM)).continuous
  have he : (fun σ : ℝ ↦ |σ| ^ (2 * k + 1) •
      ((Real.cos (2 * Real.pi * σ * t) : ℂ) * 𝓕 (fun y ↦ (g y : ℂ)) σ +
        (t * Real.sinc (2 * Real.pi * σ * t) : ℝ) * 𝓕 (fun y ↦ (h y : ℂ)) σ)) =
      fun σ ↦ (Real.cos (2 * Real.pi * σ * t) : ℂ) * G σ +
        (t * Real.sinc (2 * Real.pi * σ * t) : ℝ) * H σ := by
    funext σ
    simp only [G, H, Complex.real_smul]
    ring
  rw [he, fourierInv_waveMultiplier_eq_characteristicIntegral hG hH hHc]
  dsimp only [G, H]
  simp_rw [g.fourierInv_odd_abs_pow_smul_fourier_real, h.fourierInv_odd_abs_pow_smul_fourier_real]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul]
  push_cast
  ring

end WaveEquation.Fourier
