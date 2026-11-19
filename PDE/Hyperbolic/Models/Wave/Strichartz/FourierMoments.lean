/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Fourier.Schwartz.Regularity

/-!
# Cosine waves with integrable frequency moments

An integrable frequency datum with two integrable norm moments defines a
jointly C² cosine wave. Differentiation under the Fourier integral gives its
first and second derivatives and the wave equation in every dimension.
The datum need not be Schwartz or square-integrable.
-/

@[expose] public section

open MeasureTheory FourierTransform PDE.Analysis.Fourier
open scoped Topology

namespace WaveEquation.Fourier

attribute [local instance] instNormedAddCommGroupComplexDerivative
  instNormedSpaceComplexDerivative instNormedAddCommGroupComplexHessian
  instNormedSpaceComplexHessian instContinuousENormWaveDerivative
  instContinuousENormWaveHessian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Three integrable frequency moments suffice for the cosine wave and
its first two joint derivatives; the frequency datum need not be Schwartz. -/
theorem cosine_wave_regular_of_integrable_moments {G : E → ℂ} (hG : Integrable G)
    (hG₁ : Integrable (fun ξ ↦ ‖ξ‖ * ‖G ξ‖)) (hG₂ : Integrable (fun ξ ↦ ‖ξ‖ ^ 2 * ‖G ξ‖)) :
    ContDiff ℝ 2 (waveSolution G 0) ∧
      ∀ p : ℝ × E, Integrable (waveFirstKernel G 0 p) ∧
        HasFDerivAt (waveSolution G 0) (∫ ξ, waveFirstKernel G 0 p ξ) p ∧
        Integrable (waveSecondKernel G 0 p) ∧
        HasFDerivAt (fderiv ℝ (waveSolution G 0)) (∫ ξ, waveSecondKernel G 0 p ξ) p := by
  apply contDiff_two_fourierInv_family (fun t ξ ↦ waveValue (2 * Real.pi * ‖ξ‖) (G ξ) 0 t)
    (fun t ξ ↦ waveVelocity (2 * Real.pi * ‖ξ‖) (G ξ) 0 t)
    (fun t ξ ↦ waveAcceleration (2 * Real.pi * ‖ξ‖) (G ξ) 0 t) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t
    have hc : Continuous (fun ξ : E ↦ Real.cos ((2 * Real.pi * ‖ξ‖) * t)) := by fun_prop
    simp only [waveValue, smul_zero, add_zero]
    exact hc.aestronglyMeasurable.fun_smul hG.aestronglyMeasurable
  · intro t
    have hc : Continuous (fun ξ : E ↦ -(2 * Real.pi * ‖ξ‖) *
        Real.sin ((2 * Real.pi * ‖ξ‖) * t)) := by fun_prop
    simp only [waveVelocity, smul_zero, add_zero]
    exact hc.aestronglyMeasurable.fun_smul hG.aestronglyMeasurable
  · intro t
    have hc : Continuous (fun ξ : E ↦ -((2 * Real.pi * ‖ξ‖) ^ 2) *
        Real.cos ((2 * Real.pi * ‖ξ‖) * t)) := by fun_prop
    simp only [waveAcceleration, smul_zero, add_zero]
    exact hc.aestronglyMeasurable.fun_smul hG.aestronglyMeasurable
  · exact fun ξ t ↦ hasDerivAt_waveValue _ _ _ _
  · exact fun ξ t ↦ hasDerivAt_waveVelocity _ _ _ _
  · intro ξ
    unfold waveAcceleration
    fun_prop
  · intro T _
    refine ⟨fun ξ ↦ ‖G ξ‖, fun ξ ↦ (2 * Real.pi) * (‖ξ‖ * ‖G ξ‖),
      fun ξ ↦ (2 * Real.pi) ^ 2 * (‖ξ‖ ^ 2 * ‖G ξ‖),
      hG.norm, hG₁, hG₂, hG₁.const_mul _, ?_, hG₂.const_mul _, ?_⟩
    · convert hG₂.const_mul (2 * Real.pi) using 1
      ext ξ
      ring
    · intro t ht ξ
      have hω : 0 ≤ 2 * Real.pi * ‖ξ‖ := by positivity
      refine ⟨?_, ?_, ?_⟩
      · simpa only [norm_zero, mul_zero, add_zero] using
          norm_waveValue_le (2 * Real.pi * ‖ξ‖) t T (G ξ) 0 ht
      · simpa only [norm_zero, add_zero, mul_assoc] using norm_waveVelocity_le hω t (G ξ) 0
      · simpa only [norm_zero, mul_zero, add_zero, mul_pow, mul_assoc] using
          norm_waveAcceleration_le hω t (G ξ) 0

/-- The cosine wave with these moments satisfies the Hessian wave equation. -/
theorem waveSolution_waveTrace_of_integrable_moments {n : ℕ} {G : ℝ^n → ℂ}
    (hG : Integrable G) (hG₁ : Integrable (fun ξ ↦ ‖ξ‖ * ‖G ξ‖))
    (hG₂ : Integrable (fun ξ ↦ ‖ξ‖ ^ 2 * ‖G ξ‖)) (p : ℝ × ℝ^n) :
    waveTrace n (fderiv ℝ (fderiv ℝ (waveSolution G 0)) p) = 0 := by
  obtain ⟨hKi, hD⟩ := ((cosine_wave_regular_of_integrable_moments hG hG₁ hG₂).2 p).2.2
  rw [hD.fderiv, ← (waveTrace n).integral_comp_comm hKi]
  simp only [waveTrace_secondKernel, integral_zero]

end WaveEquation.Fourier
