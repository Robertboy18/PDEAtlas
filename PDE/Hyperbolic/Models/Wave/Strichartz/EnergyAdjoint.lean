/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Integral.InnerProduct
public import PDE.Hyperbolic.Models.Wave.Strichartz.EnergyKernel
public import PDE.Hyperbolic.Models.Wave.Strichartz.EnergyContinuity
public import PDE.Hyperbolic.Models.Wave.Strichartz.LpOperator

/-!
# The Fourier energy adjoint estimate

The energy Gram kernel, spatial Young inequality, and temporal fractional
integration bound the squared norm of the Bochner energy integral.
Compact time weights supply integrable examples directly. The estimate concerns the concrete Fourier
data.
-/

@[expose] public section

open MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal

namespace WaveEquation.Strichartz

/-- Continuous compact time weights give Bochner-integrable energy data. -/
theorem integrable_smul_frequencyEnergyDatum (F : 𝓢(ℝ^3, ℂ))
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w) :
    Integrable (fun t ↦ w t • frequencyEnergyDatum F t) :=
  (hw.smul (continuous_frequencyEnergyDatum F)).integrable_of_hasCompactSupport hwc.smul_right

/-- The adjoint energy integral satisfies the dual mixed-norm squared estimate.
The explicit integrability hypothesis concerns this concrete Hilbert-valued integral. -/
theorem ofReal_norm_integral_frequencyEnergyDatum_sq_le (F : ℝ → 𝓢(ℝ^3, ℝ))
    (hF : Measurable (fun z : ℝ × ℝ^3 ↦ F z.1 z.2)) (hFc : ∀ t, HasCompactSupport (F t : ℝ^3 → ℝ))
    (hA : Integrable (fun t ↦ frequencyEnergyDatum (𝓕 ((F t).postcompCLM Complex.ofRealCLM)) t)) :
    ENNReal.ofReal (‖∫ t, frequencyEnergyDatum (𝓕 ((F t).postcompCLM Complex.ofRealCLM)) t‖ ^ 2) ≤
      ‖(4 * Real.pi)⁻¹‖ₑ * spacetimeNewtonBound *
      (eLpNorm (fun t ↦ eLpNorm (F t) (12 / 11) volume) (4 / 3) volume) ^ 2 := by
  let K := fun t s : ℝ ↦ ∫⁻ x : ℝ^3, (∫⁻ y : ℝ^3,
    ‖exteriorNewtonKernel |t - s| (x - y)‖ₑ * ‖F s y‖ₑ) * ‖F t x‖ₑ
  calc
    _ ≤ ∫⁻ t, ∫⁻ s, ‖(inner ℂ (frequencyEnergyDatum (𝓕 ((F t).postcompCLM Complex.ofRealCLM)) t)
        (frequencyEnergyDatum (𝓕 ((F s).postcompCLM Complex.ofRealCLM)) s)).re‖ₑ :=
      ofReal_norm_integral_sq_le_lintegral_lintegral_re_inner (𝕜 := ℂ) hA
    _ ≤ ∫⁻ t, ∫⁻ s, ‖(4 * Real.pi)⁻¹‖ₑ * K t s := by
      refine lintegral_mono fun t ↦ ?_
      apply lintegral_mono_ae
      filter_upwards [volume.ae_ne t] with s hs
      exact enorm_re_inner_frequencyEnergyDatum_le (F t) (F s) (hFc t) (hFc s) hs.symm
    _ = ‖(4 * Real.pi)⁻¹‖ₑ * ∫⁻ t, ∫⁻ s, K t s := by
      simp_rw [lintegral_const_mul' _ _ enorm_ne_top]
    _ ≤ _ := by
      have h := lintegral_spacetime_exteriorNewtonKernel_mul_le hF.enorm hF.enorm
      have hn (t : ℝ) : eLpNorm (fun x ↦ ‖F t x‖ₑ) (12 / 11) volume =
          eLpNorm (F t) (12 / 11) volume := eLpNorm_enorm _ (F t).continuous.aestronglyMeasurable
      simp_rw [hn] at h
      have h' := mul_le_mul (le_refl ‖(4 * Real.pi)⁻¹‖ₑ) h bot_le bot_le
      simpa only [K, spacetimeNewtonBound, pow_two, mul_assoc] using h'

end WaveEquation.Strichartz
