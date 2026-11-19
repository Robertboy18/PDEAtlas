/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Strichartz.CosinePairing

/-!
# Fourier pairing for the full wave

The cosine/sinc propagator preserves integrability of input frequency data.
Mathlib's Fourier Fubini theorem identifies physical pairings with the
frequency multiplier, including zero frequency and both displacement and velocity.
The evolved wave itself need not be integrable.
-/

@[expose] public section

open MeasureTheory FourierTransform
open scoped ComplexConjugate

namespace WaveEquation.Fourier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The sine propagator preserves frequency integrability, including zero frequency. -/
theorem integrable_sine_frequency {H : E → ℂ} (hH : Integrable H) (t : ℝ) :
    Integrable (fun ξ ↦ sineKernel (2 * Real.pi * ‖ξ‖) t • H ξ) := by
  apply hH.bdd_smul (𝕜 := ℝ) (φ := fun ξ ↦ sineKernel (2 * Real.pi * ‖ξ‖) t) |t|
  · apply Continuous.aestronglyMeasurable
    unfold sineKernel
    fun_prop
  · exact Filter.Eventually.of_forall fun ξ ↦ by
      simpa only [Real.norm_eq_abs] using abs_sineKernel_le (2 * Real.pi * ‖ξ‖) t

/-- Physical pairing with the full cosine/sinc wave equals its frequency pairing.
Only the input functions are assumed integrable. -/
theorem integral_inner_wave_eq {f G H : E → ℂ}
    (hf : Integrable f) (hG : Integrable G) (hH : Integrable H) (t : ℝ) :
    (∫ x, inner ℂ (f x) (waveSolution G H (t, x))) =
      ∫ ξ, inner ℂ (𝓕 f ξ) (waveValue (2 * Real.pi * ‖ξ‖) (G ξ) (H ξ) t) := by
  have hi : Integrable (fun ξ ↦ waveValue (2 * Real.pi * ‖ξ‖) (G ξ) (H ξ) t) :=
    (integrable_cosine_frequency hG t).add (integrable_sine_frequency hH t)
  have hflip : (innerₗ E).flip = innerₗ E := by
    ext x y
    exact real_inner_comm x y
  have h := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip
    (μ := (volume : Measure E)) (ν := (volume : Measure E))
    (L := innerₗ E) (innerSL ℂ) Real.continuous_fourierChar continuous_inner hf hi
  rw [hflip] at h
  exact h.symm

end WaveEquation.Fourier
