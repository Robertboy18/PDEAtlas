/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Fourier.Lp.Evolution
public import PDE.Hyperbolic.Models.Wave.Strichartz.Impulse

/-!
# Physical sine pairing for arbitrary L2 impulses

The inverse-frequency adjoint sine datum is the bounded sine propagator at a
Schwartz test. Self-adjointness and Plancherel then identify the rotated energy
impulse pairing with the physical L2 wave at the time difference. The velocity may be arbitrary L2
data.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace WaveEquation.Strichartz

open WaveEquation.Fourier FourierTransform
open scoped SchwartzMap

/-- The inverse-frequency sine datum is the bounded sine propagator applied
at the Schwartz L2 class. The value at zero frequency is irrelevant to the class. -/
theorem sineEnergyDatum_eq_sinePropagator (F : 𝓢(ℝ^3, ℂ)) (t : ℝ) :
    sineEnergyDatum F t = sinePropagator (ω := fun ξ : ℝ^3 ↦ 2 * Real.pi * ‖ξ‖)
      (continuous_const.mul continuous_norm).measurable t (F.toLp 2 volume) := by
  apply Lp.ext
  filter_upwards [sineEnergyDatum_ae_eq F t,
    sinePropagator_coeFn (ω := fun ξ : ℝ^3 ↦ 2 * Real.pi * ‖ξ‖)
      (continuous_const.mul continuous_norm).measurable t (F.toLp 2 volume),
    F.coeFn_toLp 2 volume, volume.ae_ne (0 : ℝ^3)] with ξ he hs hf hξ
  rw [he, hs, hf, smul_smul, smul_smul, Real.rpow_neg (norm_nonneg ξ), Real.rpow_one]
  rw [sineKernel_eq_div (mul_ne_zero
    (mul_ne_zero (by norm_num) Real.pi_ne_zero) (norm_ne_zero_iff.mpr hξ))]
  simp only [div_eq_mul_inv, mul_inv, mul_assoc]

/-- A shifted energy impulse paired with a spatial L2 test is the
physical Fourier sine evolution for arbitrary L2 velocity. -/
theorem inner_frequencyEnergyDatum_rotationColumn_eq_sineEvolution
    (f : 𝓢(ℝ^3, ℂ)) (u : Lp ℂ 2 (volume : Measure (ℝ^3))) (t s : ℝ) :
    inner ℂ (frequencyEnergyDatum (𝓕 f) t)
      (Lp.rotationColumn
        (show Measurable (fun ξ : ℝ^3 ↦ 2 * Real.pi * ‖ξ‖) from
          (continuous_const.mul continuous_norm).measurable) s (𝓕 u)) =
      inner ℂ (f.toLp 2 volume) (sineEvolution (t - s) u) := by
  rw [inner_frequencyEnergyDatum_rotationColumn, sineEnergyDatum_eq_sinePropagator,
    inner_sinePropagator_left, ← SchwartzMap.toLp_fourier_eq]
  have he := Lp.inner_fourier_eq (f.toLp 2 volume) (sineEvolution (t - s) u)
  change inner ℂ (𝓕 (f.toLp 2 volume)) (𝓕 (𝓕⁻ (sinePropagator _ (t - s) (𝓕 u)))) = _ at he
  rwa [fourier_fourierInv_eq] at he

end WaveEquation.Strichartz
