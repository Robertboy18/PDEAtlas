/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Fourier.Schwartz.Regularity

/-!
# Fourier pairing for the cosine wave

The physical pairing with the inverse-Fourier cosine wave equals its
frequency pairing. Mathlib’s sesquilinear Fourier Fubini theorem applies to integrable input data.
-/

@[expose] public section

open MeasureTheory FourierTransform
open scoped ComplexConjugate

namespace WaveEquation.Fourier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A bounded cosine multiplier preserves frequency integrability. -/
theorem integrable_cosine_frequency {G : E → ℂ} (hG : Integrable G) (t : ℝ) :
    Integrable (fun ξ ↦ Real.cos ((2 * Real.pi * ‖ξ‖) * t) • G ξ) := by
  apply hG.bdd_smul (𝕜 := ℝ) (φ := fun ξ ↦ Real.cos ((2 * Real.pi * ‖ξ‖) * t)) 1
  · exact (show Continuous (fun ξ : E ↦ Real.cos ((2 * Real.pi * ‖ξ‖) * t)) by
      fun_prop).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun ξ ↦ by
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one ((2 * Real.pi * ‖ξ‖) * t)

/-- The cosine wave pairing equals the Fourier frequency pairing.
Both integrability assumptions concern the input data, not the wave or its potential. -/
theorem integral_inner_cosine_wave_eq {f G : E → ℂ}
    (hf : Integrable f) (hG : Integrable G) (t : ℝ) :
    (∫ x, inner ℂ (f x) (waveSolution G 0 (t, x))) =
      ∫ ξ, inner ℂ (𝓕 f ξ) (Real.cos ((2 * Real.pi * ‖ξ‖) * t) • G ξ) := by
  have hflip : (innerₗ E).flip = innerₗ E := by
    ext x y
    exact real_inner_comm x y
  have h := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip
    (μ := (volume : Measure E)) (ν := (volume : Measure E))
    (L := innerₗ E) (innerSL ℂ) Real.continuous_fourierChar continuous_inner
    hf (integrable_cosine_frequency hG t)
  rw [hflip] at h
  change (∫ ξ, inner ℂ (𝓕 f ξ) (Real.cos ((2 * Real.pi * ‖ξ‖) * t) • G ξ)) = (∫ x, inner ℂ (f x)
      (𝓕⁻ (fun ξ ↦ Real.cos ((2 * Real.pi * ‖ξ‖) * t) • G ξ) x)) at h
  simpa only [waveSolution, waveValue, Pi.zero_apply, smul_zero, add_zero] using h.symm

end WaveEquation.Fourier
