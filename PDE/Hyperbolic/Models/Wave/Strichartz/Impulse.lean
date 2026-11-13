/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Modulation
public import PDE.Hyperbolic.Models.Wave.Strichartz.HomogeneousIdentification

import CAS.ExactTactic

/-!
# Physical pairings of time-shifted wave impulses

The signed energy rotation converts the adjoint energy pairing at time `t`
into the sine-wave pairing at `t - s`. This identity holds for arbitrary L2
frequency data. Schwartz frequency impulses then identify the homogeneous
operator against compact spatial tests and finite compact spacetime tensors.
The identities use Fourier waves and explicit Lp representative transport.
-/

@[expose] public section

open MeasureTheory FourierTransform
open scoped ENNReal SchwartzMap

namespace WaveEquation.Strichartz

/-- The signed rotation column turns the energy test at t into the sine test at t-s. -/
theorem inner_frequencyEnergyDatum_rotationColumn
    (F : 𝓢(ℝ^3, ℂ)) (H : Lp ℂ 2 (volume : Measure (ℝ^3))) (t s : ℝ) :
    inner ℂ (frequencyEnergyDatum F t) (Lp.rotationColumn (show Measurable
      (fun ξ : ℝ^3 ↦ 2 * Real.pi * ‖ξ‖) from (continuous_const.mul continuous_norm).measurable) s
      H) = inner ℂ (sineEnergyDatum F (t - s)) H := by
  let ω : ℝ^3 → ℝ := fun ξ ↦ 2 * Real.pi * ‖ξ‖
  have hω : Measurable ω := (continuous_const.mul continuous_norm).measurable
  change inner ℂ (frequencyEnergyDatum F t) (Lp.rotationColumn hω s H) = _
  rw [WithLp.prod_inner_apply]
  change inner ℂ (cosineEnergyDatum F t) (Lp.rotationColumn hω s H).fst +
    inner ℂ (sineEnergyDatum F t) (Lp.rotationColumn hω s H).snd = _
  rw [L2.inner_def, L2.inner_def, L2.inner_def, ← integral_add
    (L2.integrable_inner (𝕜 := ℂ) (cosineEnergyDatum F t) (Lp.rotationColumn hω s H).fst)
    (L2.integrable_inner (𝕜 := ℂ) (sineEnergyDatum F t) (Lp.rotationColumn hω s H).snd)]
  apply integral_congr_ae
  filter_upwards [cosineEnergyDatum_ae_eq F t, sineEnergyDatum_ae_eq F t,
    sineEnergyDatum_ae_eq F (t - s), Lp.rotationColumn_fst_ae hω s H,
    Lp.rotationColumn_snd_ae hω s H] with ξ hcos hsin hdiff hfst hsnd
  rw [hcos, hsin, hdiff, hfst, hsnd]
  change inner ℂ (Real.cos (ω ξ * t) • _) (-Real.sin (ω ξ * s) • H ξ) +
    inner ℂ (Real.sin (ω ξ * t) • _) (Real.cos (ω ξ * s) • H ξ) = _
  simp only [inner_smul_left_eq_smul, inner_smul_right_eq_smul, smul_smul]
  rw [← add_smul]
  congr 1
  rw [mul_sub, Real.sin_sub]
  cas

end WaveEquation.Strichartz

namespace WaveEquation.Strichartz

/-- A frequency impulse rotated to time s gives the physical zero-displacement
wave at t-s when paired with any compact real spatial test. -/
theorem re_inner_frequencyEnergyDatum_rotationColumn_eq_integral_wave (f : 𝓢(ℝ^3, ℝ))
    (hfc : HasCompactSupport (f : ℝ^3 → ℝ)) (H : 𝓢(ℝ^3, ℂ)) (t s : ℝ) :
    (inner ℂ (frequencyEnergyDatum (𝓕 (f.postcompCLM Complex.ofRealCLM)) t)
      (Lp.rotationColumn
        (show Measurable (fun ξ : ℝ^3 ↦ 2 * Real.pi * ‖ξ‖) from
          (continuous_const.mul continuous_norm).measurable) s (H.toLp 2 volume))).re =
      ∫ x, f x * (Fourier.waveSolution (0 : 𝓢(ℝ^3, ℂ)) H (t - s, x)).re := by
  rw [inner_frequencyEnergyDatum_rotationColumn]
  have hzero : (0 : Lp ℂ 2 (volume : Measure (ℝ^3))) =ᵐ[volume]
      fun ξ ↦ (2 * Real.pi * ‖ξ‖) • (0 : 𝓢(ℝ^3, ℂ)) ξ := by
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure (ℝ^3))] with ξ hξ
    simpa only [Pi.zero_apply, zero_apply, smul_zero] using hξ
  have he := re_inner_frequencyEnergyDatum_input_eq_integral_wave f hfc 0 H
    0 (H.toLp 2 volume) hzero (H.coeFn_toLp 2 volume) (t - s)
  rw [WithLp.prod_inner_apply] at he
  change (inner ℂ (cosineEnergyDatum _ (t - s)) 0 +
    inner ℂ (sineEnergyDatum _ (t - s)) (H.toLp 2 volume)).re = _ at he
  simpa only [inner_zero_right, zero_add] using he

end WaveEquation.Strichartz

namespace WaveEquation.Strichartz

/-- The bounded homogeneous output for a rotated impulse has the physical
shifted sine-wave pairing against every finite compact spacetime tensor. -/
theorem spacetimePairing_homogeneousWaveOperator_rotationColumn_compactTensor
    (H : 𝓢(ℝ^3, ℂ)) (s : ℝ)
    (a : ({w : 𝓢(ℝ, ℝ) // HasCompactSupport (w : ℝ → ℝ)} ×
      {f : 𝓢(ℝ^3, ℝ) // HasCompactSupport (f : ℝ^3 → ℝ)}) →₀ ℝ) :
    spacetimePairing (homogeneousWaveOperator
      (Lp.rotationColumn
        (show Measurable (fun ξ : ℝ^3 ↦ 2 * Real.pi * ‖ξ‖) from
          (continuous_const.mul continuous_norm).measurable) s (H.toLp 2 volume)))
      (SchwartzMap.compactTensorLpLinearMap (4 / 3) (12 / 11) volume volume a) =
        ∫ t, ∫ x, SchwartzMap.compactTensorSchwartzLinearMap a t x *
          (Fourier.waveSolution (0 : 𝓢(ℝ^3, ℂ)) H (t - s, x)).re := by
  rw [spacetimePairing_homogeneousWaveOperator, energyAdjointOperator_compactTensor]
  have hi := integrable_frequencyEnergyDatum_compactTensor a
  change RCLike.re (inner ℂ (∫ t, frequencyEnergyDatum
    (𝓕 ((SchwartzMap.compactTensorSchwartzLinearMap a t).postcompCLM Complex.ofRealCLM)) t)
    (Lp.rotationColumn _ s (H.toLp 2 volume))) = _
  rw [inner_re_symm, ← integral_inner hi, ← integral_re (hi.const_inner _)]
  apply integral_congr_ae
  filter_upwards with t
  rw [inner_re_symm]
  exact re_inner_frequencyEnergyDatum_rotationColumn_eq_integral_wave
    (SchwartzMap.compactTensorSchwartzLinearMap a t)
    (hasCompactSupport_compactTensorSchwartzSection a t) H t s

end WaveEquation.Strichartz
