/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.L2Compatibility
public import PDE.Hyperbolic.Models.Wave.Fourier.Lp.Sine
public import PDE.Hyperbolic.Models.Wave.Fourier.Schwartz.Regularity
public import PDE.Hyperbolic.Models.Wave.Fourier.Schwartz.Integrability

/-!
# Physical L2 sine evolution

Unitary Fourier transformation conjugates the sine multiplier to the physical
wave evolution. Its strong time derivative is the cosine evolution, including
at time zero, and its displacement norm costs at most absolute elapsed time.
For Schwartz data it is the inverse Fourier integral almost everywhere.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace WaveEquation.Fourier

open FourierTransform
open scoped SchwartzMap

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The physical L2 sine evolution, constructed by the unitary Fourier transform. -/
noncomputable def sineEvolution (t : ℝ) :
    Lp F 2 (volume : Measure V) →L[ℝ] Lp F 2 (volume : Measure V) :=
  ((fourierInvCLM ℂ (Lp F 2 (volume : Measure V))).restrictScalars ℝ).comp
    ((sinePropagator (ω := fun ξ : V ↦ 2 * Real.pi * ‖ξ‖)
      (continuous_const.mul continuous_norm).measurable t).comp
      ((fourierCLM ℂ (Lp F 2 (volume : Measure V))).restrictScalars ℝ))

/-- Its displacement norm costs only absolute elapsed time times velocity norm. -/
theorem norm_sineEvolution_apply_le (t : ℝ) (u : Lp F 2 (volume : Measure V)) :
    ‖sineEvolution t u‖ ≤ |t| * ‖u‖ := by
  change ‖𝓕⁻ (sinePropagator (ω := fun ξ : V ↦ 2 * Real.pi * ‖ξ‖)
    (continuous_const.mul continuous_norm).measurable t (𝓕 u))‖ ≤ _
  have hinv (v : Lp F 2 (volume : Measure V)) : ‖𝓕⁻ v‖ = ‖v‖ := by
    simpa only [fourier_fourierInv_eq] using (Lp.norm_fourier_eq (𝓕⁻ v)).symm
  rw [hinv]
  exact (norm_sinePropagator_apply_le _ t (𝓕 u)).trans_eq
    (congrArg (fun r : ℝ ↦ |t| * r) (Lp.norm_fourier_eq u))

/-- The strong time derivative of the physical sine evolution is the Fourier
cosine propagator, including time zero. -/
theorem hasDerivAt_sineEvolution_apply (u : Lp F 2 (volume : Measure V)) (t : ℝ) :
    HasDerivAt (fun s ↦ sineEvolution s u) (𝓕⁻ (Lp.modulationCLM Real.continuous_cos
      Real.abs_cos_le_one (ω := fun ξ : V ↦ 2 * Real.pi * ‖ξ‖)
      (continuous_const.mul continuous_norm).measurable t (𝓕 u))) t :=
  ((fourierInvCLM ℂ (Lp F 2 (volume : Measure V))).restrictScalars ℝ).hasFDerivAt
    |>.comp_hasDerivAt t
      (hasDerivAt_sinePropagator_apply (by norm_num : (2 : ℝ≥0∞) ≠ ∞) _ (𝓕 u) t)

/-- L2 sine evolution is strongly continuous in time. -/
theorem continuous_sineEvolution_apply (u : Lp F 2 (volume : Measure V)) :
    Continuous (fun t ↦ sineEvolution t u) :=
  continuous_iff_continuousAt.mpr fun t ↦ (hasDerivAt_sineEvolution_apply u t).continuousAt

/-- At zero elapsed time the physical sine evolution vanishes. -/
@[simp] theorem sineEvolution_zero_apply (u : Lp F 2 (volume : Measure V)) :
    sineEvolution 0 u = 0 := by
  change 𝓕⁻ (sinePropagator _ 0 (𝓕 u)) = _
  rw [sinePropagator_zero, zero_apply, fourierInv_zero]

/-- For Schwartz velocity the physical L2 evolution agrees almost everywhere
with the inverse Fourier sine integral. -/
theorem sineEvolution_schwartz_ae (h : 𝓢(V, ℂ)) (t : ℝ) :
    sineEvolution t (h.toLp 2 volume) =ᵐ[volume]
      (fun x ↦ waveSolution (0 : 𝓢(V, ℂ)) (𝓕 h : 𝓢(V, ℂ)) (t, x)) := by
  have hrep : (fun ξ ↦ waveValue (2 * Real.pi * ‖ξ‖)
      ((0 : 𝓢(V, ℂ)) ξ) ((𝓕 h : 𝓢(V, ℂ)) ξ) t) =ᵐ[volume]
      (sinePropagator (ω := fun ξ : V ↦ 2 * Real.pi * ‖ξ‖)
        (continuous_const.mul continuous_norm).measurable t (𝓕 (h.toLp 2 volume))) := by
    rw [SchwartzMap.toLp_fourier_eq]
    filter_upwards [sinePropagator_coeFn (ω := fun ξ : V ↦ 2 * Real.pi * ‖ξ‖)
        (continuous_const.mul continuous_norm).measurable t ((𝓕 h : 𝓢(V, ℂ)).toLp 2 volume),
      (𝓕 h : 𝓢(V, ℂ)).coeFn_toLp 2 volume] with ξ hs hh
    rw [hs, hh]
    simp only [waveValue, zero_apply, smul_zero, zero_add]
  exact (PDE.Analysis.Fourier.fourierInvIntegral_eq_L2_ae
    (integrable_waveValue 0 (𝓕 h) t) _ hrep).symm

end WaveEquation.Fourier
