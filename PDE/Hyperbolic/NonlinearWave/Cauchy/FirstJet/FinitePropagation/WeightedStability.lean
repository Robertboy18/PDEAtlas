/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.WeightedEstimates
public import PDE.Analysis.Evolution.Time.AbsoluteContinuity
public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.EnergyApproximation

/-!
# Weighted stability of the first-jet wave

H² persistence justifies the local energy calculation for generator-domain
data. Grönwall bounds the weighted difference of two solutions by the
weighted difference of their data. No derivative of the reaction occurs.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution Hyperbolic.Variational

variable {n : ℕ} {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}
variable {hf : LipschitzWith L f} {hf0 : f 0 = 0}

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric

/-- Generator-domain data satisfy weighted stability for every nonnegative
bounded Sobolev weight whose relative first derivatives are bounded. -/
theorem IsEnergySolution.weighted_sub_le_exp_of_generator {x y : H¹(ℝ^n) × DerivLp n 2 univ}
    {u v : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)} (hu : IsEnergySolution hf hf0 x u)
    (hv : IsEnergySolution hf hf0 y v) {Ax Ay : EnergyState n}
    (hx : (linearSemigroup n).HasGeneratorAt ((C).symm x) Ax)
    (hy : (linearSemigroup n).HasGeneratorAt ((C).symm y) Ay) (χ : W^{1,∞}(ℝ^n)) {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (ha : ∀ᵐ y ∂domainMeasure n univ, 0 ≤ (χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) y)
    (hd : ∀ i : Fin n, ∀ᵐ y ∂domainMeasure n univ, |(χ : WkpAmbientOn n 1 ∞ univ)
      (singleDerivIndex n i) y| ≤ ρ * (χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) y)
    {T : ℝ} (hT : 0 ≤ T) :
    let a := (χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1); weightedEnergyForm a (u T - v T)
      (u T - v T) ≤
      weightedEnergyForm a (x - y) (x - y) * Real.exp ((2 + (L : ℝ) ^ 2 + (n : ℝ) * ρ) * T) := by
  obtain ⟨U₁, V₁, A₁, _, hV₁, hA₁, hrep₁⟩ := hu.exists_memLp_h2_lifts hx T
  obtain ⟨U₂, V₂, A₂, _, hV₂, hA₂, hrep₂⟩ := hv.exists_memLp_h2_lifts hy T
  obtain ⟨huAC, hdu⟩ := hu.absolutelyContinuous_of_lifts hT hV₁ hA₁
    (fun t ht ↦ (hrep₁ t ht).2.1) (fun t ht ↦ (hrep₁ t ht).2.2.1)
  obtain ⟨hvAC, hdv⟩ := hv.absolutelyContinuous_of_lifts hT hV₂ hA₂
    (fun t ht ↦ (hrep₂ t ht).2.1) (fun t ht ↦ (hrep₂ t ht).2.2.1)
  let a := (χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)
  let w := fun t ↦ u t - v t
  let d := fun t ↦ (V₁ t, A₁ t) - (V₂ t, A₂ t)
  let e := fun t ↦ weightedEnergyForm a (w t) (w t)
  have hwAC : AbsolutelyContinuousOnInterval w 0 T := huAC.sub hvAC
  have hB : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ weightedEnergyForm a) 0 T :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  have heAC : AbsolutelyContinuousOnInterval e 0 T :=
    PDE.Analysis.Evolution.AbsolutelyContinuousOnInterval.clm_apply
      (PDE.Analysis.Evolution.AbsolutelyContinuousOnInterval.clm_apply hB hwAC) hwAC
  have hstate (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      (lowerOrderCLM (by decide : 1 ≤ 2) (U₁ t - U₂ t),
        wkpBaseCoordinateCLM (V₁ t - V₂ t)) = w t := by
    apply Prod.ext
    · rw [map_sub, (hrep₁ t ht).1, (hrep₂ t ht).1]
      rfl
    · change wkpBaseCoordinateCLM (V₁ t - V₂ t) = (u t).2 - (v t).2
      rw [map_sub, show wkpBaseCoordinateCLM (V₁ t) = (u t).2 from (hrep₁ t ht).2.1,
        show wkpBaseCoordinateCLM (V₂ t) = (v t).2 from (hrep₂ t ht).2.1]
  have hdiff (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : (V₁ t - V₂ t, wkpLaplacianCLM (U₁ t - U₂ t) -
        (reaction hf hf0 (u t) - reaction hf hf0 (v t))) = d t := by
    apply Prod.ext
    · rfl
    change _ = A₁ t - A₂ t
    rw [map_sub, (hrep₁ t ht).2.2.2, (hrep₂ t ht).2.2.2,
      laplacian_eq_wkpLaplacianCLM, laplacian_eq_wkpLaplacianCLM]
    abel_nf
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : 2 * weightedEnergyForm a (w t) (d t) ≤
        (2 + (L : ℝ) ^ 2 + (n : ℝ) * ρ) * e t := by
    have hr := reaction_sub_sq_le_energyDensity_ae hf hf0 (u t) (v t)
    change ∀ᵐ y ∂domainMeasure n univ, ((reaction hf hf0 (u t) - reaction hf hf0 (v t)) y) ^ 2 ≤
        (L : ℝ) ^ 2 * energyDensity (w t) y at hr
    rw [← hstate t ht] at hr
    have h := weightedEnergyForm_wave_le χ (U₁ t - U₂ t) (V₁ t - V₂ t)
      (reaction hf hf0 (u t) - reaction hf hf0 (v t)) hρ ha hd hr
    dsimp only at h
    rwa [hstate t ht, hdiff t ht] at h
  have hderiv : ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      deriv e t ≤ (2 + (L : ℝ) ^ 2 + (n : ℝ) * ρ) * e t + 0 := by
    have hdu' : ∀ᵐ t ∂volume.restrict (Ioc 0 T), HasDerivAt u (V₁ t, A₁ t) t := by
      simpa only [← restrict_Ioo_eq_restrict_Ioc] using hdu
    have hdv' : ∀ᵐ t ∂volume.restrict (Ioc 0 T), HasDerivAt v (V₂ t, A₂ t) t := by
      simpa only [← restrict_Ioo_eq_restrict_Ioc] using hdv
    filter_upwards [hdu', hdv', ae_restrict_mem measurableSet_Ioc] with t hdu hdv ht
    have hw : HasDerivAt w (d t) t := hdu.sub hdv
    have he := ((weightedEnergyForm a).hasFDerivAt.comp_hasDerivAt t hw).clm_apply hw
    have he' : HasDerivAt e (2 * weightedEnergyForm a (w t) (d t)) t := by
      change HasDerivAt e (weightedEnergyForm a (d t) (w t) +
        weightedEnergyForm a (w t) (d t)) t at he
      rwa [weightedEnergyForm_symmetric a (d t) (w t), ← two_mul] at he
    rw [he'.deriv, add_zero]
    exact hbound t (Ioc_subset_Icc_self ht)
  have hK : 0 ≤ 2 + (L : ℝ) ^ 2 + (n : ℝ) * ρ := by positivity
  have he := le_mul_exp_of_absolutelyContinuousOnInterval_deriv_le hT heAC
    (intervalIntegrable_const (c := (0 : ℝ))) (Eventually.of_forall fun _ ↦ le_rfl) hK hderiv
    T ⟨hT, le_rfl⟩
  simpa only [e, w, hu.initial, hv.initial, intervalIntegral.integral_zero, add_zero,
    sub_zero] using he

/-- Weighted stability holds for arbitrary natural energy data. The passage
from generator-domain data uses energy convergence, not extra differentiability
of either the data or the reaction. -/
theorem IsEnergySolution.weighted_sub_le_exp {x y : H¹(ℝ^n) × DerivLp n 2 univ}
    {u v : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)} (hu : IsEnergySolution hf hf0 x u)
    (hv : IsEnergySolution hf hf0 y v) (χ : W^{1,∞}(ℝ^n)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (ha : ∀ᵐ y ∂domainMeasure n univ, 0 ≤ (χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) y)
    (hd : ∀ i : Fin n, ∀ᵐ y ∂domainMeasure n univ, |(χ : WkpAmbientOn n 1 ∞ univ)
      (singleDerivIndex n i) y| ≤ ρ * (χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) y)
    {T : ℝ} (hT : 0 ≤ T) :
    let a := (χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1); weightedEnergyForm a (u T - v T)
      (u T - v T) ≤
      weightedEnergyForm a (x - y) (x - y) * Real.exp ((2 + (L : ℝ) ^ 2 + (n : ℝ) * ρ) * T) := by
  obtain ⟨xj, Ax, uj, hxgen, huj, hxlim, hulim⟩ := hu.exists_generator_approximation
  obtain ⟨yj, Ay, vj, hygen, hvj, hylim, hvlim⟩ := hv.exists_generator_approximation
  let a := (χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)
  have hcont : Continuous (fun z : H¹(ℝ^n) × DerivLp n 2 univ ↦ weightedEnergyForm a z z) :=
    (weightedEnergyForm a).continuous.clm_apply continuous_id
  have hl := (hcont.tendsto (u T - v T)).comp ((hulim T hT).sub (hvlim T hT))
  have hr := ((hcont.tendsto (x - y)).comp (hxlim.sub hylim)).mul_const
    (Real.exp ((2 + (L : ℝ) ^ 2 + (n : ℝ) * ρ) * T))
  exact le_of_tendsto_of_tendsto hl hr (Eventually.of_forall fun j ↦
    (huj j).weighted_sub_le_exp_of_generator (hvj j) (hxgen j) (hygen j) χ hρ ha hd hT)

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
