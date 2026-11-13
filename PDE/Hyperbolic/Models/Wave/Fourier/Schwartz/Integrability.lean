/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import PDE.Hyperbolic.Models.Wave.Fourier.Schwartz.Kernel

/-!
# Integrability of the Fourier wave profile

At each frequency the wave equation is a harmonic oscillator. Its cosine and
sinc kernels are even in the frequency, and their bounds preserve integrability
of Schwartz initial data at every real time. These facts justify changing to
signed polar coordinates in the Radon representation.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace WaveEquation.Fourier

/-- Reversing the frequency does not change the oscillator solution. -/
theorem waveValue_neg_frequency (ω : ℝ) (g h : ℂ) (t : ℝ) :
    waveValue (-ω) g h t = waveValue ω g h t := by
  simp only [waveValue, sineKernel, neg_mul, Real.cos_neg, Real.sinc_neg]

/-- The oscillator depends only on the absolute value of its frequency. -/
theorem waveValue_abs_frequency (ω : ℝ) (g h : ℂ) (t : ℝ) :
    waveValue |ω| g h t = waveValue ω g h t := by
  rcases le_total 0 ω with hω | hω
  · rw [abs_of_nonneg hω]
  · rw [abs_of_nonpos hω, waveValue_neg_frequency]

/-- On a frequency line, the radial oscillator agrees with the signed
one-dimensional Fourier wave kernel. -/
theorem waveValue_real_frequency (σ t : ℝ) (g h : ℂ) :
    waveValue (2 * Real.pi * |σ|) g h t = (Real.cos (2 * Real.pi * σ * t) : ℂ) * g +
      (t * Real.sinc (2 * Real.pi * σ * t) : ℝ) * h := by
  have he : 2 * Real.pi * |σ| = |2 * Real.pi * σ| := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  rw [he, waveValue_abs_frequency]
  simp only [waveValue, sineKernel, Complex.real_smul]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Evolving Schwartz frequency data by the wave oscillator gives an integrable
profile at every real time. -/
theorem integrable_waveValue (G H : 𝓢(E, ℂ)) (t : ℝ) :
    Integrable (fun ξ : E ↦ waveValue (2 * Real.pi * ‖ξ‖) (G ξ) (H ξ) t) := by
  apply (G.integrable.norm.add (H.integrable.norm.const_mul |t|)).mono'
  · apply Continuous.aestronglyMeasurable
    unfold waveValue sineKernel
    fun_prop
  · exact Filter.Eventually.of_forall fun ξ ↦ norm_waveValue_le _ _ _ _ _ le_rfl

end WaveEquation.Fourier
