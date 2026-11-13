/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.GradientEnergy
public import PDE.Hyperbolic.Models.Wave.Strichartz.EnergyGram
public import PDE.Hyperbolic.Models.Wave.Strichartz.WavePairing

/-!
# Physical wave data and the Fourier energy norm

The displacement component is weighted by 2*pi*|frequency| and the velocity
component is its unweighted Fourier transform. Plancherel identifies the squared
Hilbert norm with exactly one derivative of displacement plus velocity energy,
without a displacement L2 term. Pairing against compact spatial tests recovers
the physical cosine/sine Fourier solution.
-/

@[expose] public section

open MeasureTheory FourierTransform
open scoped SchwartzMap

namespace WaveEquation.Strichartz

/-- The two inverse-frequency test components pair with displacement and velocity
energy to give the full wave multiplier. -/
theorem inner_wave_energy_multiplier {ω : ℝ} (hω : ω ≠ 0) (t : ℝ) (f g h : ℂ) :
    inner ℂ (Real.cos (ω * t) • (ω⁻¹ • f)) (ω • g) + inner ℂ (Real.sin (ω * t) • (ω⁻¹ • f)) h =
      inner ℂ f (Fourier.waveValue ω g h t) := by
  simp only [Fourier.waveValue, Fourier.sineKernel_eq_div hω,
    inner_add_right, inner_smul_left_eq_smul, inner_smul_right_eq_smul, smul_smul, div_eq_mul_inv]
  rw [mul_left_comm ω, mul_inv_cancel₀ hω, mul_one]

/-- The Hilbert energy pairing equals the full cosine/sine frequency
pairing. Input classes have their explicit weighted frequency representatives. -/
theorem inner_frequencyEnergyDatum_input (F : 𝓢(ℝ^3, ℂ)) (G H : ℝ^3 → ℂ)
    (U V : Lp ℂ 2 (volume : Measure (ℝ^3))) (hU : U =ᵐ[volume] fun ξ ↦ (2 * Real.pi * ‖ξ‖) • G ξ)
    (hV : V =ᵐ[volume] H) (t : ℝ) :
    inner ℂ (frequencyEnergyDatum F t) (WithLp.toLp 2 (U, V)) =
      ∫ ξ, inner ℂ (F ξ) (Fourier.waveValue (2 * Real.pi * ‖ξ‖) (G ξ) (H ξ) t) := by
  rw [WithLp.prod_inner_apply]
  change inner ℂ (cosineEnergyDatum F t) U + inner ℂ (sineEnergyDatum F t) V = _
  rw [L2.inner_def, L2.inner_def, ← integral_add
    (L2.integrable_inner (𝕜 := ℂ) (cosineEnergyDatum F t) U)
    (L2.integrable_inner (𝕜 := ℂ) (sineEnergyDatum F t) V)]
  apply integral_congr_ae
  filter_upwards [cosineEnergyDatum_ae_eq F t, sineEnergyDatum_ae_eq F t,
    hU, hV, volume.ae_ne (0 : ℝ^3)] with ξ hcos hsin hu hv hξ
  rw [hcos, hsin, hu, hv]
  have hscale : (2 * Real.pi)⁻¹ * ‖ξ‖ ^ (-1 : ℝ) = (2 * Real.pi * ‖ξ‖)⁻¹ := by
    simp only [Real.rpow_neg (norm_nonneg ξ), Real.rpow_one, mul_inv]
  simp only [smul_smul (2 * Real.pi)⁻¹, hscale]
  exact inner_wave_energy_multiplier
    (mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
      (norm_ne_zero_iff.mpr hξ)) t (F ξ) (G ξ) (H ξ)

/-- The energy pairing for a spatial Schwartz test equals the physical full-wave pairing. -/
theorem inner_frequencyEnergyDatum_input_eq_integral_wave (f : 𝓢(ℝ^3, ℂ)) (G H : ℝ^3 → ℂ)
    (hG : Integrable G) (hH : Integrable H) (U V : Lp ℂ 2 (volume : Measure (ℝ^3)))
    (hU : U =ᵐ[volume] fun ξ ↦ (2 * Real.pi * ‖ξ‖) • G ξ) (hV : V =ᵐ[volume] H) (t : ℝ) :
    inner ℂ (frequencyEnergyDatum (𝓕 f) t) (WithLp.toLp 2 (U, V)) =
      ∫ x, inner ℂ (f x) (Fourier.waveSolution G H (t, x)) := by
  rw [inner_frequencyEnergyDatum_input _ _ _ _ _ hU hV]
  simpa only [SchwartzMap.fourier_coe] using
    (Fourier.integral_inner_wave_eq f.integrable hG hH t).symm

/-- Real compact spatial tests pair with the physical full wave through the
energy datum. Frequency integrability and wave continuity follow from Schwartz data. -/
theorem re_inner_frequencyEnergyDatum_input_eq_integral_wave (f : 𝓢(ℝ^3, ℝ))
    (hfc : HasCompactSupport (f : ℝ^3 → ℝ)) (G H : 𝓢(ℝ^3, ℂ))
    (U V : Lp ℂ 2 (volume : Measure (ℝ^3))) (hU : U =ᵐ[volume] fun ξ ↦ (2 * Real.pi * ‖ξ‖) • G ξ)
    (hV : V =ᵐ[volume] H) (t : ℝ) :
    (inner ℂ (frequencyEnergyDatum (𝓕 (f.postcompCLM Complex.ofRealCLM)) t)
      (WithLp.toLp 2 (U, V))).re = ∫ x, f x * (Fourier.waveSolution G H (t, x)).re := by
  let fc := f.postcompCLM Complex.ofRealCLM
  have hcont : Continuous (fun x ↦ Fourier.waveSolution G H (t, x)) :=
    (Fourier.schwartz_wave_regular G H).1.continuous.comp (continuous_const.prodMk continuous_id)
  have hi : Integrable (fun x ↦ f x • Fourier.waveSolution G H (t, x)) :=
    (f.continuous.smul hcont).integrable_of_hasCompactSupport hfc.smul_right
  have hinner (x : ℝ^3) (z : ℂ) : inner ℂ (fc x) z = f x • z := by
    change inner ℂ (f x : ℂ) z = _
    rw [RCLike.inner_apply', Complex.conj_ofReal, Complex.real_smul]
  change (inner ℂ (frequencyEnergyDatum (𝓕 fc) t) (WithLp.toLp 2 (U, V))).re = _
  rw [inner_frequencyEnergyDatum_input_eq_integral_wave fc G H G.integrable H.integrable U V hU hV]
  simp only [hinner]
  simpa only [RCLike.smul_re, RCLike.re_to_complex] using (integral_re hi).symm

end WaveEquation.Strichartz

open LineDeriv

namespace WaveEquation.Strichartz

/-- The Fourier energy input contains precisely one derivative of displacement
and the unweighted velocity. -/
noncomputable def initialEnergyDatum (g h : 𝓢(ℝ^3, ℂ)) :
    WithLp 2 (Lp ℂ 2 (volume : Measure (ℝ^3)) × Lp ℂ 2 (volume : Measure (ℝ^3))) :=
  WithLp.toLp 2 ((g.memLp_frequency_smul_fourier).toLp _, (𝓕 h).toLp 2 volume)

/-- The displacement component represents the first frequency weight. -/
theorem initialEnergyDatum_fst_ae_eq (g h : 𝓢(ℝ^3, ℂ)) :
    (initialEnergyDatum g h).fst =ᵐ[volume] fun ξ ↦ (2 * Real.pi * ‖ξ‖) • 𝓕 g ξ :=
  (g.memLp_frequency_smul_fourier).coeFn_toLp

/-- The velocity component represents its Fourier transform. -/
theorem initialEnergyDatum_snd_ae_eq (g h : 𝓢(ℝ^3, ℂ)) :
    (initialEnergyDatum g h).snd =ᵐ[volume] (𝓕 h : 𝓢(ℝ^3, ℂ)) :=
  (𝓕 h).coeFn_toLp 2 volume

/-- The squared input norm is exactly the spatial derivative energy plus velocity
energy, in any finite orthonormal basis; no displacement L² term occurs. -/
theorem norm_initialEnergyDatum_sq {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (ℝ^3)) (g h : 𝓢(ℝ^3, ℂ)) :
    ‖initialEnergyDatum g h‖ ^ 2 = (∑ i, ∫ x, ‖∂_{b i} g x‖ ^ 2) + ∫ x, ‖h x‖ ^ 2 := by
  have hsq (u : Lp ℂ 2 (volume : Measure (ℝ^3))) :
      ‖u‖ ^ 2 = ∫ ξ, ‖u ξ‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  rw [WithLp.prod_norm_sq_eq_of_L2, hsq, hsq]
  congr 1
  · calc
      _ = ∫ ξ, (2 * Real.pi * ‖ξ‖) ^ 2 * ‖𝓕 g ξ‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [initialEnergyDatum_fst_ae_eq g h] with ξ hξ
        rw [hξ, norm_smul, mul_pow, Real.norm_of_nonneg (by positivity)]
      _ = _ := (SchwartzMap.sum_integral_norm_sq_lineDerivOp_eq_fourier b g).symm
  · calc
      _ = ∫ ξ, ‖𝓕 h ξ‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [initialEnergyDatum_snd_ae_eq g h] with ξ hξ
        rw [hξ]
      _ = _ := SchwartzMap.integral_norm_sq_fourier h

/-- The Fourier initial energy pairs against each compact real spatial
test as the physical solution with these displacement and velocity data. -/
theorem re_inner_frequencyEnergyDatum_initialEnergyDatum (f : 𝓢(ℝ^3, ℝ))
    (hfc : HasCompactSupport (f : ℝ^3 → ℝ)) (g h : 𝓢(ℝ^3, ℂ)) (t : ℝ) :
    (inner ℂ (frequencyEnergyDatum (𝓕 (f.postcompCLM Complex.ofRealCLM)) t)
      (initialEnergyDatum g h)).re =
        ∫ x, f x * (Fourier.waveSolution (𝓕 g : 𝓢(ℝ^3, ℂ)) (𝓕 h : 𝓢(ℝ^3, ℂ)) (t, x)).re :=
  re_inner_frequencyEnergyDatum_input_eq_integral_wave f hfc (𝓕 g) (𝓕 h)
    (initialEnergyDatum g h).fst (initialEnergyDatum g h).snd
    (initialEnergyDatum_fst_ae_eq g h) (initialEnergyDatum_snd_ae_eq g h) t

end WaveEquation.Strichartz
