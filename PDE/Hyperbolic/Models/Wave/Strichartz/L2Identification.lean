/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module
public import PDE.Analysis.MeasureTheory.Lp.JointRepresentative.Trajectory
public import PDE.Hyperbolic.Models.Wave.Strichartz.RetardedIdentification
public import PDE.Hyperbolic.Models.Wave.Strichartz.SinePairing

/-!
# Physical identification of arbitrary L2 wave impulses

The constructed homogeneous mixed output is the real part of the
physical Fourier sine wave for arbitrary complex L2 velocity. Compact tensor
tests and local integrability identify the joint representatives almost
everywhere. Causal truncation identifies the retarded impulse with the real
part of the same future-truncated physical wave.
-/

@[expose] public section

open MeasureTheory FourierTransform Filter
open scoped ENNReal SchwartzMap

namespace WaveEquation.Strichartz

/-- Physical sine pairings for arbitrary L2 velocity hold against each finite
compact spacetime tensor. -/
theorem spacetimePairing_homogeneousWaveOperator_rotationColumn_L2_compactTensor
    (u : Lp ℂ 2 (volume : Measure (ℝ^3))) (s : ℝ)
    (a : ({w : 𝓢(ℝ, ℝ) // HasCompactSupport (w : ℝ → ℝ)} ×
      {f : 𝓢(ℝ^3, ℝ) // HasCompactSupport (f : ℝ^3 → ℝ)}) →₀ ℝ) :
    spacetimePairing (homogeneousWaveOperator
      (Lp.rotationColumn measurable_waveFrequency s (𝓕 u)))
      (SchwartzMap.compactTensorLpLinearMap (4 / 3) (12 / 11) volume volume a) =
      ∫ t, (inner ℂ
        (((SchwartzMap.compactTensorSchwartzLinearMap a t).postcompCLM
          Complex.ofRealCLM).toLp 2 volume) (Fourier.sineEvolution (t - s) u)).re := by
  rw [spacetimePairing_homogeneousWaveOperator, energyAdjointOperator_compactTensor]
  have hi := integrable_frequencyEnergyDatum_compactTensor a
  change RCLike.re (inner ℂ (∫ t, frequencyEnergyDatum
    (𝓕 ((SchwartzMap.compactTensorSchwartzLinearMap a t).postcompCLM Complex.ofRealCLM)) t)
    (Lp.rotationColumn measurable_waveFrequency s (𝓕 u))) = _
  rw [inner_re_symm, ← integral_inner hi, ← integral_re (hi.const_inner _)]
  apply integral_congr_ae
  filter_upwards with t
  rw [inner_re_symm]
  exact congrArg Complex.re (inner_frequencyEnergyDatum_rotationColumn_eq_sineEvolution
    ((SchwartzMap.compactTensorSchwartzLinearMap a t).postcompCLM Complex.ofRealCLM) u t s)

/-- Spatial Schwartz testing of a physical L2 class is integration against
any almost-everywhere representative of that class. -/
theorem re_inner_schwartz_L2_eq_integral (f : 𝓢(ℝ^3, ℝ))
    (u : Lp ℂ 2 (volume : Measure (ℝ^3))) {F : ℝ^3 → ℂ} (hF : F =ᵐ[volume] u) :
    (inner ℂ ((f.postcompCLM Complex.ofRealCLM).toLp 2 volume) u).re = ∫ x, f x * (F x).re := by
  rw [L2.inner_def]
  have hi := L2.integrable_inner (𝕜 := ℂ) ((f.postcompCLM Complex.ofRealCLM).toLp 2 volume) u
  change RCLike.re (∫ x, inner ℂ _ _) = _
  rw [← integral_re hi]
  apply integral_congr_ae
  filter_upwards [(f.postcompCLM Complex.ofRealCLM).coeFn_toLp 2 volume, hF] with x hf hx
  rw [hf, ← hx]
  change (inner ℂ (f x : ℂ) (F x)).re = _
  rw [RCLike.inner_apply', Complex.conj_ofReal, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- The physical sine evolution of arbitrary L2 velocity represents the homogeneous
mixed output. Every supplied representative is transported through product AE equality. -/
theorem jointRepresentative_homogeneousWaveOperator_rotationColumn_L2
    (u : Lp ℂ 2 (volume : Measure (ℝ^3))) (s : ℝ) {F : ℝ × ℝ^3 → ℂ} (hF : Measurable F)
    (hsection : ∀ t, (fun x ↦ F (t, x)) =ᵐ[volume] (Fourier.sineEvolution (t - s) u : ℝ^3 → ℂ)) :
    Lp.jointRepresentative (homogeneousWaveOperator (Lp.rotationColumn measurable_waveFrequency s
      (𝓕 u))) =ᵐ[volume.prod volume] fun z ↦ (F z).re := by
  have hc : Continuous (fun t : ℝ ↦ Fourier.sineEvolution (t - s) u) :=
    (Fourier.continuous_sineEvolution_apply u).comp (continuous_id.sub continuous_const)
  have hl := hc.locallyIntegrable_jointLpRepresentative (μ := volume) hF hsection
  have hr : LocallyIntegrable (fun z ↦ (F z).re) (volume.prod volume) :=
    hl.mono (Complex.continuous_re.measurable.comp hF).aestronglyMeasurable
      (.of_forall fun z ↦ by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (F z))
  refine jointRepresentative_eq_of_compactTensor_pairing _ hr fun a ↦ ?_
  rw [spacetimePairing_homogeneousWaveOperator_rotationColumn_L2_compactTensor]
  apply integral_congr_ae
  filter_upwards with t
  exact re_inner_schwartz_L2_eq_integral _ _ (hsection t)

/-- An arbitrary L2 impulse has a physical joint representative of the constructed
mixed output; the representative is measurable and exists at every time. -/
theorem exists_jointRepresentative_homogeneousWaveOperator_rotationColumn_L2
    (u : Lp ℂ 2 (volume : Measure (ℝ^3))) (s : ℝ) :
    ∃ F : ℝ × ℝ^3 → ℂ, Measurable F ∧
      (∀ t, (fun x ↦ F (t, x)) =ᵐ[volume]
        (Fourier.sineEvolution (t - s) u : ℝ^3 → ℂ)) ∧
      Lp.jointRepresentative (homogeneousWaveOperator
        (Lp.rotationColumn measurable_waveFrequency s (𝓕 u)))
          =ᵐ[volume.prod volume] fun z ↦ (F z).re := by
  have hc : Continuous (fun t : ℝ ↦ Fourier.sineEvolution (t - s) u) :=
    (Fourier.continuous_sineEvolution_apply u).comp (continuous_id.sub continuous_const)
  obtain ⟨F, hF, hs⟩ := hc.stronglyMeasurable.exists_jointLpRepresentative
  exact ⟨F, hF, hs, jointRepresentative_homogeneousWaveOperator_rotationColumn_L2 u s hF hs⟩

/-- Causal truncation preserves the arbitrary-L2 sine identification. -/
theorem jointRepresentative_retardedWaveAt_L2 (u : Lp ℂ 2 (volume : Measure (ℝ^3))) (s : ℝ)
    {F : ℝ × ℝ^3 → ℂ} (hF : Measurable F)
    (hsection : ∀ t, (fun x ↦ F (t, x)) =ᵐ[volume] (Fourier.sineEvolution (t - s) u : ℝ^3 → ℂ)) :
    Lp.jointRepresentative (retardedWaveAt s u)
      =ᵐ[volume.prod volume] (Prod.fst ⁻¹' Set.Ici s).indicator (fun z ↦ (F z).re) := by
  have hcut := Lp.jointRepresentative_indicatorCLM (𝕜 := ℝ) (s := Set.Ici s) measurableSet_Ici
    (homogeneousWaveOperator (Lp.rotationColumn measurable_waveFrequency s (𝓕 u)))
  have hp := jointRepresentative_homogeneousWaveOperator_rotationColumn_L2 u s hF hsection
  apply hcut.trans
  filter_upwards [hp] with z hz
  by_cases ht : z ∈ Prod.fst ⁻¹' Set.Ici s
  · simp only [Set.indicator_of_mem ht, hz]
  · simp only [Set.indicator_of_notMem ht]

end WaveEquation.Strichartz
