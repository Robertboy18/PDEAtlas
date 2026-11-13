/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Distribution.TensorTestUniqueness
public import PDE.Analysis.MeasureTheory.Lp.JointRepresentative.LocalIntegrability
public import PDE.Hyperbolic.Models.Wave.Strichartz.Impulse
public import PDE.Hyperbolic.Models.Wave.Strichartz.Retarded

/-!
# Physical identification of the homogeneous Strichartz operator

Tensor-test uniqueness identifies the mixed Lp output with the physical
Fourier wave for Schwartz displacement and velocity. Consequently the physical
wave has finite L4-in-time L12-in-space norm and the proved TT* bound. The input
energy has exactly the gradient and velocity terms, as established in `Strichartz.InitialEnergy`.
The same identification applies to a time-translated sine impulse.

These give the case `f = 0` of the L⁴L¹² part of the estimate (4) of Evans, §12.4, Theorem 1. The
forced classical estimate, with its L-infinity L6 conclusion, is in `Strichartz.Estimate`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, Theorem 1, equations (3)-(4), and step 2 of its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory FourierTransform
open scoped ENNReal SchwartzMap

namespace WaveEquation.Strichartz

/-- Compact tensor pairings integrate the joint measurable representative. -/
theorem spacetimePairing_compactTensor_eq_jointIntegral
    (u : Lp (Lp ℝ 12 (volume : Measure (ℝ^3))) 4 (volume : Measure ℝ))
    (a : ({w : 𝓢(ℝ, ℝ) // HasCompactSupport (w : ℝ → ℝ)} ×
      {f : 𝓢(ℝ^3, ℝ) // HasCompactSupport (f : ℝ^3 → ℝ)}) →₀ ℝ) :
    spacetimePairing u (SchwartzMap.compactTensorLpLinearMap (4 / 3) (12 / 11) volume volume a) =
      ∫ t, ∫ x,
      SchwartzMap.compactTensorSchwartzLinearMap a t x * Lp.jointRepresentative u (t, x) := by
  rw [spacetimePairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [SchwartzMap.compactTensorLpLinearMap_ae_eq
    (4 / 3) (12 / 11) volume volume a] with t ht
  rw [ht]
  apply integral_congr_ae
  filter_upwards [Lp.jointRepresentative_section u t,
    (SchwartzMap.compactTensorSchwartzLinearMap a t).coeFn_toLp (12 / 11) volume] with x hu ha
  rw [← hu, ha, mul_comm]

/-- Compact tensor pairings identify the mixed representative of any locally
integrable physical field. -/
theorem jointRepresentative_eq_of_compactTensor_pairing
    (u : Lp (Lp ℝ 12 (volume : Measure (ℝ^3))) 4 (volume : Measure ℝ)) {F : ℝ × ℝ^3 → ℝ}
    (hF : LocallyIntegrable F (volume.prod volume))
    (hpair : ∀ a : ({w : 𝓢(ℝ, ℝ) // HasCompactSupport (w : ℝ → ℝ)} ×
      {f : 𝓢(ℝ^3, ℝ) // HasCompactSupport (f : ℝ^3 → ℝ)}) →₀ ℝ,
      spacetimePairing u (SchwartzMap.compactTensorLpLinearMap (4 / 3) (12 / 11) volume volume a) =
      ∫ t, ∫ x, SchwartzMap.compactTensorSchwartzLinearMap a t x * F (t, x)) :
    Lp.jointRepresentative u =ᵐ[volume.prod volume] F := by
  apply (Lp.locallyIntegrable_jointRepresentative u).ae_eq_of_integral_contDiff_tensor_smul_eq hF
  intro a b ha hac hb hbc
  let w : 𝓢(ℝ, ℝ) := hac.toSchwartzMap ha
  let f : 𝓢(ℝ^3, ℝ) := hbc.toSchwartzMap hb
  let v : ({w : 𝓢(ℝ, ℝ) // HasCompactSupport (w : ℝ → ℝ)} ×
      {f : 𝓢(ℝ^3, ℝ) // HasCompactSupport (f : ℝ^3 → ℝ)}) →₀ ℝ :=
    Finsupp.single (⟨w, hac⟩, ⟨f, hbc⟩) 1
  have hp := hpair v
  rw [spacetimePairing_compactTensor_eq_jointIntegral] at hp
  have hw (t : ℝ) : w t = a t := rfl
  have hf (x : ℝ^3) : f x = b x := rfl
  simpa only [v, SchwartzMap.compactTensorSchwartzLinearMap,
    Finsupp.linearCombination_single, one_smul, smul_apply, smul_eq_mul, hw, hf] using hp

/-- The homogeneous mixed Lp output agrees almost everywhere with the
physical Fourier wave, with no assumed spacetime norm of that wave. -/
theorem jointRepresentative_homogeneousWaveOperator_initialEnergyDatum (g h : 𝓢(ℝ^3, ℂ)) :
    Lp.jointRepresentative (homogeneousWaveOperator (initialEnergyDatum g h)) =ᵐ[volume.prod volume]
      fun z ↦ (Fourier.waveSolution (𝓕 g : 𝓢(ℝ^3, ℂ)) (𝓕 h : 𝓢(ℝ^3, ℂ)) z).re := by
  have hc := (Fourier.contDiff_two_schwartz_wave (𝓕 g : 𝓢(ℝ^3, ℂ)) (𝓕 h : 𝓢(ℝ^3, ℂ))).continuous
  exact jointRepresentative_eq_of_compactTensor_pairing _
    (Complex.continuous_re.comp hc).locallyIntegrable
    (spacetimePairing_homogeneousWaveOperator_initialEnergyDatum_compactTensor g h)

/-- The rotated homogeneous output is the physical sine impulse translated in time. -/
theorem jointRepresentative_homogeneousWaveOperator_rotationColumn (H : 𝓢(ℝ^3, ℂ)) (s : ℝ) :
    Lp.jointRepresentative (homogeneousWaveOperator (Lp.rotationColumn measurable_waveFrequency s
      (H.toLp 2 volume))) =ᵐ[volume.prod volume] fun z ↦
      (Fourier.waveSolution (0 : 𝓢(ℝ^3, ℂ)) H (z.1 - s, z.2)).re := by
  have hc := (Fourier.contDiff_two_schwartz_wave (0 : 𝓢(ℝ^3, ℂ)) H).continuous
  exact jointRepresentative_eq_of_compactTensor_pairing _ ((Complex.continuous_re.comp hc).comp
      ((continuous_fst.sub continuous_const).prodMk continuous_snd)).locallyIntegrable
    (spacetimePairing_homogeneousWaveOperator_rotationColumn_compactTensor H s)

/-- The physical Fourier mixed seminorm equals the norm of the constructed quotient output. -/
theorem eLpNorm_fourierWave_eq (g h : 𝓢(ℝ^3, ℂ)) :
    eLpNorm (fun t ↦ eLpNorm (fun x ↦ (Fourier.waveSolution (𝓕 g : 𝓢(ℝ^3, ℂ)) (𝓕 h : 𝓢(ℝ^3, ℂ))
      (t, x)).re) 12 volume) 4 volume = ‖homogeneousWaveOperator (initialEnergyDatum g h)‖ₑ := by
  rw [← Lp.eLpNorm_jointRepresentative]
  apply eLpNorm_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod
    (jointRepresentative_homogeneousWaveOperator_initialEnergyDatum g h)] with t ht
  exact eLpNorm_congr_ae (Filter.EventuallyEq.symm ht)

/-- Physical Fourier waves have finite mixed L4L12 seminorm, derived from TT*. -/
theorem memLp_eLpNorm_fourierWave (g h : 𝓢(ℝ^3, ℂ)) :
    MemLp (fun t ↦ eLpNorm (fun x ↦ (Fourier.waveSolution
      (𝓕 g : 𝓢(ℝ^3, ℂ)) (𝓕 h : 𝓢(ℝ^3, ℂ)) (t, x)).re) 12 volume) 4 volume := by
  change eLpNorm _ _ _ < (∞ : ℝ≥0∞)
  rw [eLpNorm_fourierWave_eq]
  exact enorm_lt_top

/-- The Fourier wave has the proved global L4-in-time L12-in-space bound. -/
theorem mixedNorm_fourierWave_le (g h : 𝓢(ℝ^3, ℂ)) :
    (eLpNorm (fun t ↦ eLpNorm (fun x ↦ (Fourier.waveSolution (𝓕 g : 𝓢(ℝ^3, ℂ)) (𝓕 h : 𝓢(ℝ^3, ℂ))
      (t, x)).re) 12 volume) 4 volume).toReal ≤ energyAdjointBound * ‖initialEnergyDatum g h‖ := by
  rw [eLpNorm_fourierWave_eq, toReal_enorm]
  exact (homogeneousWaveOperator.le_opNorm _).trans
    (mul_le_mul_of_nonneg_right norm_homogeneousWaveOperator_le (norm_nonneg _))

end WaveEquation.Strichartz
