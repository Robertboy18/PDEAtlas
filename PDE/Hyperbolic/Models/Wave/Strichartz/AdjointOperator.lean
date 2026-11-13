/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Distribution.Schwartz.MixedLp
public import PDE.Analysis.Distribution.Schwartz.TensorLp
public import PDE.Hyperbolic.Models.Wave.Strichartz.EnergyAdjoint
public import PDE.Hyperbolic.Models.Wave.Strichartz.EnergyLinearity

/-!
# The bounded Fourier energy adjoint

Compact spacetime tensors give Bochner integrals of the inverse-frequency
energy datum. The Gram estimate bounds these integrals in the mixed dual norm,
and density extends them to a continuous operator on L^(4/3) time/L^(12/11) space.
The extension retains the integral formula on every compact tensor sum.
-/

@[expose] public section

open MeasureTheory
open scoped SchwartzMap ENNReal

open FourierTransform
namespace WaveEquation.Strichartz

/-- The adjoint energy estimate holds for finite sums of compact time weights and
compact Schwartz spatial tests. Measurability and Bochner integrability are derived. -/
theorem ofReal_norm_integral_frequencyEnergyDatum_finset_sq_le {ι : Type*} (a : Finset ι)
    (w : ι → ℝ → ℝ) (f : ι → 𝓢(ℝ^3, ℝ)) (hw : ∀ i ∈ a, Continuous (w i))
    (hwc : ∀ i ∈ a, HasCompactSupport (w i)) (hfc : ∀ i ∈ a, HasCompactSupport (f i : ℝ^3 → ℝ)) :
    ENNReal.ofReal (‖∫ t, frequencyEnergyDatum
      (𝓕 ((∑ i ∈ a, w i t • f i).postcompCLM Complex.ofRealCLM)) t‖ ^ 2) ≤
      ‖(4 * Real.pi)⁻¹‖ₑ * spacetimeNewtonBound *
        (eLpNorm (fun t ↦ eLpNorm (⇑(∑ i ∈ a, w i t • f i : 𝓢(ℝ^3, ℝ))) (12 / 11) volume)
          (4 / 3) volume) ^ 2 := by
  have hF : Measurable (fun z : ℝ × ℝ^3 ↦ (∑ i ∈ a, w i z.1 • f i) z.2) := by
    have hc : Continuous (fun z : ℝ × ℝ^3 ↦ ∑ i ∈ a, w i z.1 * f i z.2) :=
      continuous_finsetSum a fun i hi ↦
        ((hw i hi).comp continuous_fst).mul ((f i).continuous.comp continuous_snd)
    simpa only [sum_apply, smul_apply, smul_eq_mul] using hc.measurable
  have hFc (t : ℝ) : HasCompactSupport ((∑ i ∈ a, w i t • f i : 𝓢(ℝ^3, ℝ)) : ℝ^3 → ℝ) := by
    have hterms (i : ι) (hi : i ∈ a) : HasCompactSupport (fun x : ℝ^3 ↦ w i t • f i x) :=
      (hfc i hi).smul_left (f := fun _ ↦ w i t)
    have h : HasCompactSupport (∑ i ∈ a, fun x : ℝ^3 ↦ w i t • f i x) :=
      HasCompactSupport.finset_sum (s := a) (f := fun i x ↦ w i t • f i x) hterms
    have he : (∑ i ∈ a, fun x : ℝ^3 ↦ w i t • f i x) =
        ((∑ i ∈ a, w i t • f i : 𝓢(ℝ^3, ℝ)) : ℝ^3 → ℝ) := by
      funext x
      simp only [Finset.sum_apply, sum_apply, smul_apply]
    exact he ▸ h
  have he (t : ℝ) : frequencyEnergyDatum
      (𝓕 ((∑ i ∈ a, w i t • f i).postcompCLM Complex.ofRealCLM)) t =
      ∑ i ∈ a, w i t • frequencyEnergyDatum
        (𝓕 ((f i).postcompCLM Complex.ofRealCLM)) t := by
    let L := (frequencyEnergyDatumLinearMap t).comp
      ((SchwartzMap.fourierTransformCLM ℝ).toLinearMap.comp
        (SchwartzMap.postcompCLM Complex.ofRealCLM).toLinearMap)
    change L (∑ i ∈ a, w i t • f i) = ∑ i ∈ a, w i t • L (f i)
    simp only [map_sum, map_smul]
  have hA : Integrable (fun t ↦ frequencyEnergyDatum
      (𝓕 ((∑ i ∈ a, w i t • f i).postcompCLM Complex.ofRealCLM)) t) := by
    simp_rw [he]
    exact integrable_finsetSum a fun i hi ↦
      integrable_smul_frequencyEnergyDatum _ (hw i hi) (hwc i hi)
  exact ofReal_norm_integral_frequencyEnergyDatum_sq_le _ hF hFc hA

/-- The energy integral has a finite real operator bound on compact
finite tensor sums. Its constant is the square root of the proved kernel bound. -/
theorem norm_integral_frequencyEnergyDatum_finset_le {ι : Type*} (a : Finset ι) (w : ι → ℝ → ℝ)
    (f : ι → 𝓢(ℝ^3, ℝ)) (hw : ∀ i ∈ a, Continuous (w i)) (hwc : ∀ i ∈ a, HasCompactSupport (w i))
    (hfc : ∀ i ∈ a, HasCompactSupport (f i : ℝ^3 → ℝ)) :
    ‖∫ t, frequencyEnergyDatum
      (𝓕 ((∑ i ∈ a, w i t • f i).postcompCLM Complex.ofRealCLM)) t‖ ≤
      Real.sqrt ((‖(4 * Real.pi)⁻¹‖ₑ * spacetimeNewtonBound).toReal) *
        (eLpNorm (fun t ↦ eLpNorm (⇑(∑ i ∈ a, w i t • f i : 𝓢(ℝ^3, ℝ))) (12 / 11) volume)
          (4 / 3) volume).toReal := by
  have hN := SchwartzMap.memLp_eLpNorm_finset_smul
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure (ℝ^3)))
    (p := (4 / 3 : ℝ≥0∞)) (q := (12 / 11 : ℝ≥0∞)) a w f hw hwc
  have he (t : ℝ) : ((∑ i ∈ a, w i t • f i : 𝓢(ℝ^3, ℝ)) : ℝ^3 → ℝ) =
      ∑ i ∈ a, ((w i t • f i : 𝓢(ℝ^3, ℝ)) : ℝ^3 → ℝ) := by
    funext x
    simp only [sum_apply, Finset.sum_apply]
  have hN' : eLpNorm (fun t ↦ eLpNorm
      (⇑(∑ i ∈ a, w i t • f i : 𝓢(ℝ^3, ℝ))) (12 / 11) volume) (4 / 3) volume ≠ ∞ := by
    simpa only [he] using hN.eLpNorm_ne_top
  have hC : ‖(4 * Real.pi)⁻¹‖ₑ * spacetimeNewtonBound ≠ ∞ :=
    ENNReal.mul_ne_top enorm_ne_top spacetimeNewtonBound_lt_top.ne
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hC (ENNReal.pow_ne_top hN'))
    (ofReal_norm_integral_frequencyEnergyDatum_finset_sq_le a w f hw hwc hfc)
  rw [ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_mul, ENNReal.toReal_pow] at h
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) ENNReal.toReal_nonneg)).mp
  simpa only [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg] using h

end WaveEquation.Strichartz

open MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal

namespace WaveEquation.Strichartz

/-- The explicit norm bound supplied by the Fourier Gram kernel estimate. -/
noncomputable def energyAdjointBound : ℝ :=
  Real.sqrt ((‖(4 * Real.pi)⁻¹‖ₑ * spacetimeNewtonBound).toReal)

/-- The energy integral, extended linearly over finite compact tensors. -/
noncomputable def energyAdjointTensorLinearMap :
    (({w : 𝓢(ℝ, ℝ) // HasCompactSupport (w : ℝ → ℝ)} ×
      {f : 𝓢(ℝ^3, ℝ) // HasCompactSupport (f : ℝ^3 → ℝ)}) →₀ ℝ) →ₗ[ℝ]
      WithLp 2 (Lp ℂ 2 (volume : Measure (ℝ^3)) × Lp ℂ 2 (volume : Measure (ℝ^3))) :=
  Finsupp.linearCombination ℝ fun z ↦ ∫ t, z.1.1 t •
    frequencyEnergyDatum (𝓕 (z.2.1.postcompCLM Complex.ofRealCLM)) t

/-- The finite algebraic map is exactly the Fourier energy integral of its section. -/
theorem energyAdjointTensorLinearMap_eq_integral
    (a : ({w : 𝓢(ℝ, ℝ) // HasCompactSupport (w : ℝ → ℝ)} ×
      {f : 𝓢(ℝ^3, ℝ) // HasCompactSupport (f : ℝ^3 → ℝ)}) →₀ ℝ) :
    energyAdjointTensorLinearMap a = ∫ t, frequencyEnergyDatum
      (𝓕 ((SchwartzMap.compactTensorSchwartzLinearMap a t).postcompCLM Complex.ofRealCLM)) t := by
  rw [energyAdjointTensorLinearMap, Finsupp.linearCombination_apply, Finsupp.sum]
  simp_rw [← integral_smul]
  have hi (z) (_ : z ∈ a.support) : Integrable (fun t ↦ a z • (z.1.1 t • frequencyEnergyDatum
        (𝓕 (z.2.1.postcompCLM Complex.ofRealCLM)) t)) := by
    simpa only [Pi.mul_apply, mul_smul] using integrable_smul_frequencyEnergyDatum
        (𝓕 (z.2.1.postcompCLM Complex.ofRealCLM)) (continuous_const.mul z.1.1.continuous)
        (z.1.2.mul_left (f := fun _ ↦ a z))
  rw [← integral_finsetSum a.support hi]
  apply integral_congr_ae
  filter_upwards with t
  let L := (frequencyEnergyDatumLinearMap t).comp
    ((SchwartzMap.fourierTransformCLM ℝ).toLinearMap.comp
      (SchwartzMap.postcompCLM Complex.ofRealCLM).toLinearMap)
  simp only [SchwartzMap.compactTensorSchwartzLinearMap,
    Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply]
  change (∑ z ∈ a.support, a z • (z.1.1 t • L z.2.1)) = L (∑ z ∈ a.support, a z • (z.1.1 t • z.2.1))
  simp only [map_sum, map_smul]

/-- The true energy integral is bounded by the quotient mixed norm on finite tensors. -/
theorem norm_energyAdjointTensorLinearMap_le
    (a : ({w : 𝓢(ℝ, ℝ) // HasCompactSupport (w : ℝ → ℝ)} ×
      {f : 𝓢(ℝ^3, ℝ) // HasCompactSupport (f : ℝ^3 → ℝ)}) →₀ ℝ) :
    ‖energyAdjointTensorLinearMap a‖ ≤ energyAdjointBound *
      ‖SchwartzMap.compactTensorLpLinearMap (4 / 3) (12 / 11) volume volume a‖ := by
  rw [energyAdjointTensorLinearMap_eq_integral, SchwartzMap.norm_compactTensorLpLinearMap]
  have hw (z) (_ : z ∈ a.support) : Continuous (fun t ↦ a z * z.1.1 t) :=
    continuous_const.mul z.1.1.continuous
  have hwc (z) (_ : z ∈ a.support) : HasCompactSupport (fun t ↦ a z * z.1.1 t) :=
    z.1.2.mul_left (f := fun _ ↦ a z)
  have h := norm_integral_frequencyEnergyDatum_finset_le a.support
    (fun z t ↦ a z * z.1.1 t) (fun z ↦ z.2.1) hw hwc (fun z _ ↦ z.2.2)
  simpa only [energyAdjointBound, SchwartzMap.compactTensorSchwartzLinearMap,
    Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply,
    smul_smul] using h

/-- The adjoint wave energy operator on the mixed Lebesgue quotient space. -/
noncomputable def energyAdjointOperator :
    Lp (Lp ℝ (12 / 11) (volume : Measure (ℝ^3))) (4 / 3) (volume : Measure ℝ) →L[ℝ]
      WithLp 2 (Lp ℂ 2 (volume : Measure (ℝ^3)) × Lp ℂ 2 (volume : Measure (ℝ^3))) :=
  energyAdjointTensorLinearMap.extendOfNorm
    (SchwartzMap.compactTensorLpLinearMap (4 / 3) (12 / 11) volume volume)

/-- On every compact tensor sum the bounded operator equals the energy integral. -/
theorem energyAdjointOperator_compactTensor
    (a : ({w : 𝓢(ℝ, ℝ) // HasCompactSupport (w : ℝ → ℝ)} ×
      {f : 𝓢(ℝ^3, ℝ) // HasCompactSupport (f : ℝ^3 → ℝ)}) →₀ ℝ) :
    energyAdjointOperator (SchwartzMap.compactTensorLpLinearMap (4 / 3) (12 / 11) volume volume a) =
      ∫ t, frequencyEnergyDatum
      (𝓕 ((SchwartzMap.compactTensorSchwartzLinearMap a t).postcompCLM Complex.ofRealCLM)) t := by
  rw [← energyAdjointTensorLinearMap_eq_integral]
  have hd : DenseRange (SchwartzMap.compactTensorLpLinearMap
      (D := ℝ) (E := ℝ^3) (F := ℝ) (4 / 3) (12 / 11) volume volume) :=
    SchwartzMap.denseRange_compactTensorLpLinearMap (4 / 3) (12 / 11) volume volume
      (by finiteness) (by finiteness)
  exact LinearMap.extendOfNorm_eq (f := energyAdjointTensorLinearMap) hd
    ⟨energyAdjointBound, norm_energyAdjointTensorLinearMap_le⟩ a

/-- The adjoint operator has the explicit square-root Gram bound. -/
theorem norm_energyAdjointOperator_le : ‖energyAdjointOperator‖ ≤ energyAdjointBound := by
  have hd : DenseRange (SchwartzMap.compactTensorLpLinearMap
      (D := ℝ) (E := ℝ^3) (F := ℝ) (4 / 3) (12 / 11) volume volume) :=
    SchwartzMap.denseRange_compactTensorLpLinearMap (4 / 3) (12 / 11) volume volume
      (by finiteness) (by finiteness)
  exact LinearMap.opNorm_extendOfNorm_le (f := energyAdjointTensorLinearMap) hd
    (Real.sqrt_nonneg _) norm_energyAdjointTensorLinearMap_le

end WaveEquation.Strichartz
