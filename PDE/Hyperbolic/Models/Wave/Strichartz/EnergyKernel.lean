/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Strichartz.EnergyGram
public import PDE.Hyperbolic.Models.Wave.Strichartz.FourierKernel
public import PDE.Hyperbolic.Models.Wave.Strichartz.CosinePairing

/-!
# Physical kernel of the Fourier energy Gram pairing

The cosine/sine L² energy data pair through the exterior Newtonian wave
kernel. Fourier pairing and the signed Kirchhoff identification give its exact
coefficient; ordinary integral norm bounds then give a positive kernel majorant.
The nonzero time difference is needed only for the exterior-kernel formula.
-/

@[expose] public section

open MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal

namespace WaveEquation.Strichartz

/-- The real Hilbert Gram pairing is the physical Newtonian wave pairing.
Both L² classes and the wave are the Fourier constructions. -/
theorem re_inner_frequencyEnergyDatum_eq_integral_wave
    (f g : 𝓢(ℝ^3, ℝ)) (hfc : HasCompactSupport (f : ℝ^3 → ℝ)) (t s : ℝ) :
    (inner ℂ (frequencyEnergyDatum (𝓕 (f.postcompCLM Complex.ofRealCLM)) t)
      (frequencyEnergyDatum (𝓕 (g.postcompCLM Complex.ofRealCLM)) s)).re =
      ∫ x, f x * (Fourier.waveSolution
        (newtonFrequency (𝓕 (g.postcompCLM Complex.ofRealCLM))) 0 (t - s, x)).re := by
  let fc := f.postcompCLM Complex.ofRealCLM
  let G := newtonFrequency (𝓕 (g.postcompCLM Complex.ofRealCLM))
  have hcont : Continuous (fun x ↦ Fourier.waveSolution G 0 (t - s, x)) :=
    (Fourier.cosine_wave_regular_of_integrable_moments
      (integrable_newtonFrequency _) (integrable_norm_mul_newtonFrequency _)
      (integrable_norm_sq_mul_newtonFrequency _)).1.continuous.comp
        (continuous_const.prodMk continuous_id)
  have hi : Integrable (fun x ↦ f x • Fourier.waveSolution G 0 (t - s, x)) :=
    (f.continuous.smul hcont).integrable_of_hasCompactSupport hfc.smul_right
  have hinner (x : ℝ^3) (z : ℂ) : inner ℂ (fc x) z = f x • z := by
    change inner ℂ (f x : ℂ) z = _
    rw [RCLike.inner_apply', Complex.conj_ofReal, Complex.real_smul]
  rw [inner_frequencyEnergyDatum]
  change (∫ ξ, inner ℂ (𝓕 fc ξ) (Real.cos ((2 * Real.pi * ‖ξ‖) * (t - s)) • G ξ)).re = _
  have hpair : (∫ x, inner ℂ (fc x) (Fourier.waveSolution G 0 (t - s, x))) =
      ∫ ξ, inner ℂ (𝓕 fc ξ) (Real.cos ((2 * Real.pi * ‖ξ‖) * (t - s)) • G ξ) := by
    simpa only [SchwartzMap.fourier_coe] using
      Fourier.integral_inner_cosine_wave_eq (f := (fc : ℝ^3 → ℂ)) (G := G)
        fc.integrable (integrable_newtonFrequency _) (t - s)
  rw [← hpair]
  simp only [hinner]
  simpa only [RCLike.smul_re, RCLike.re_to_complex, G] using (integral_re hi).symm

/-- At unequal times the energy Gram kernel is the exterior Newtonian kernel,
with the exact fundamental-solution coefficient. -/
theorem re_inner_frequencyEnergyDatum_eq_exteriorNewtonKernel
    (f g : 𝓢(ℝ^3, ℝ)) (hfc : HasCompactSupport (f : ℝ^3 → ℝ))
    (hgc : HasCompactSupport (g : ℝ^3 → ℝ)) {t s : ℝ} (hts : t ≠ s) :
    (inner ℂ (frequencyEnergyDatum (𝓕 (f.postcompCLM Complex.ofRealCLM)) t)
      (frequencyEnergyDatum (𝓕 (g.postcompCLM Complex.ofRealCLM)) s)).re =
      (4 * Real.pi)⁻¹ * ∫ x, f x * ∫ y, exteriorNewtonKernel |t - s| (x - y) * g y := by
  rw [re_inner_frequencyEnergyDatum_eq_integral_wave f g hfc]
  simp_rw [re_cosine_wave_newtonFrequency_eq_exteriorNewtonKernel g hgc (sub_ne_zero.mpr hts)]
  simp only [mul_left_comm (f _) ((4 * Real.pi)⁻¹)]
  exact integral_const_mul _ _

/-- The absolute value of the Hilbert Gram pairing is bounded by the
positive exterior-kernel pairing. -/
theorem enorm_re_inner_frequencyEnergyDatum_le
    (f g : 𝓢(ℝ^3, ℝ)) (hfc : HasCompactSupport (f : ℝ^3 → ℝ))
    (hgc : HasCompactSupport (g : ℝ^3 → ℝ)) {t s : ℝ} (hts : t ≠ s) :
    ‖(inner ℂ (frequencyEnergyDatum (𝓕 (f.postcompCLM Complex.ofRealCLM)) t)
      (frequencyEnergyDatum (𝓕 (g.postcompCLM Complex.ofRealCLM)) s)).re‖ₑ ≤
      ‖(4 * Real.pi)⁻¹‖ₑ * ∫⁻ x, (∫⁻ y,
        ‖exteriorNewtonKernel |t - s| (x - y)‖ₑ * ‖g y‖ₑ) * ‖f x‖ₑ := by
  rw [re_inner_frequencyEnergyDatum_eq_exteriorNewtonKernel f g hfc hgc hts, enorm_mul]
  refine mul_le_mul le_rfl ?_ bot_le bot_le
  apply (enorm_integral_le_lintegral_enorm _).trans
  refine lintegral_mono fun x ↦ ?_
  dsimp only
  rw [enorm_mul, mul_comm]
  refine mul_le_mul ?_ le_rfl bot_le bot_le
  simpa only [enorm_mul] using enorm_integral_le_lintegral_enorm
    (fun y ↦ exteriorNewtonKernel |t - s| (x - y) * g y)

end WaveEquation.Strichartz
