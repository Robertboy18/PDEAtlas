/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.HigherMemLp
public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.HigherWeak
public import PDE.Hyperbolic.NonlinearWave.Cauchy.IntegrableLinear
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.HigherIntegrable
import PDE.Analysis.MeasureTheory.Lp.Continuous

/-!
# Bounded weak first-jet waves at the sharp Sobolev order

The weak class requires only essential boundedness in the higher
Sobolev norm. Linear identification of its square-integrable load recovers
a continuous higher representative, so the mild uniqueness theorem
applies to this larger weak class.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Sobolev SobolevSpace.WholeSpaceHilbert ENNReal Interval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution Hyperbolic.Variational

variable {n k : ℕ} [NeZero n] {f : (ℝ^n × ℝ × ℝ) → ℝ}

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric

/-- A weak first-jet wave with an L-infinity higher Sobolev bound.
The Gelfand identities impose the PDE and both initial traces; continuity
of the chosen higher representative is not part of this definition. -/
structure IsHigherBochnerWeakSolutionOn (hk : (n : ℝ) < 2 * (k : ℝ))
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) (τ : NNReal)
    (u : ℝ → W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) : Prop where
  bounded : MemLp u ∞ (volume.restrict (Ioc 0 (τ : ℝ)))
  weak : ∃ (ell : Lp (StrongDual ℝ H¹(ℝ^n)) 2 (volume.restrict (Ioc 0 (τ : ℝ))))
      (q : Lp H¹(ℝ^n) 2 (volume.restrict (Ioc 0 (τ : ℝ))))
      (p : Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc 0 (τ : ℝ))))
      (acc : Lp (StrongDual ℝ H¹(ℝ^n)) 2 (volume.restrict (Ioc 0 (τ : ℝ)))),
      (ell : ℝ → StrongDual ℝ H¹(ℝ^n)) =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))]
        (fun t ↦ -(energyTriple n).pivotToDual
          (wkpBaseCoordinateCLM (higherReaction hk hf hf0 (u t)))) ∧
      (q : ℝ → H¹(ℝ^n)) =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))]
        (fun t ↦ (higherCoordinatesCLM (u t)).1) ∧
      (p : ℝ → DerivLp n 2 univ) =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))]
        (fun t ↦ (higherCoordinatesCLM (u t)).2) ∧
      IsGelfandWeakWaveSolution (energyTriple n) (fun _ ↦ gradientForm n)
        ell q p acc (higherCoordinatesCLM x).1 (higherCoordinatesCLM x).2

/-- Every bounded higher weak wave has a continuous higher representative
satisfying the mild equation at exactly the same Sobolev order. -/
theorem IsHigherBochnerWeakSolutionOn.exists_continuous_mild {hk : (n : ℝ) < 2 * (k : ℝ)}
    {hf : ContDiff ℝ (⊤ : ℕ∞) f} {hf0 : f 0 = 0} {x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)} {τ : NNReal}
    {u : ℝ → W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)} (hu : IsHigherBochnerWeakSolutionOn hk hf hf0 x τ u) :
    ∃ U : C(Icc (0 : ℝ) (τ : ℝ), W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)),
      (higherLinearSemigroup n k).IsMildSolutionOn (higherMap hk hf hf0) x τ U ∧
      u =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))] IccExtend τ.coe_nonneg U := by
  obtain ⟨ell, q, p, acc, hell, hq, hp, hw⟩ := hu.weak
  have hs : MemLp (fun t ↦ higherMap hk hf hf0 (u t)) 2 (volume.restrict (Ioc 0 (τ : ℝ))) :=
    (memLp_top_higherMap hk hf hf0 hu.bounded).mono_exponent le_top
  let F := (Ioc 0 (τ : ℝ)).indicator (fun t ↦ higherMap hk hf hf0 (u t))
  have hFAE : F =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))]
      fun t ↦ higherMap hk hf hf0 (u t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact indicator_of_mem ht _
  have hF₂ : MemLp F 2 (volume.restrict (Ioc 0 (τ : ℝ))) := hs.ae_eq hFAE.symm
  have hF : LocallyIntegrable F volume :=
    (IntegrableOn.integrable_indicator (hs.integrable (by norm_num))
      measurableSet_Ioc).locallyIntegrable
  have hFzero (t : ℝ) : (F t).1 = 0 := by
    by_cases ht : t ∈ Ioc 0 (τ : ℝ)
    · rw [show F t = higherMap hk hf hf0 (u t) from indicator_of_mem ht _]
      rfl
    · rw [show F t = 0 from indicator_of_notMem ht _]
      rfl
  let J : (W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) →L[ℝ] DerivLp n 2 univ :=
    wkpBaseCoordinateCLM.comp (ContinuousLinearMap.snd ℝ _ _)
  let Fe := fun t ↦ J (F t)
  have hFe : LocallyIntegrable Fe volume := fun t ↦ J.integrableAtFilter_comp (hF t)
  have hFe₂ : MemLp Fe 2 (volume.restrict (Ioc 0 (τ : ℝ))) := J.comp_memLp' hF₂
  have hload := (energyTriple n).pivotToDual.comp_memLp' hFe₂
  let ellM := hload.toLp (fun t ↦ (energyTriple n).pivotToDual (Fe t))
  have hloadAE : (ellM : ℝ → StrongDual ℝ H¹(ℝ^n)) =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))]
      fun t ↦ (energyTriple n).pivotToDual (Fe t) := hload.coeFn_toLp
  have hmass : IsGelfandWeakWaveSolution (energyTriple n) (fun _ ↦ massForm n)
      ellM q p acc (higherCoordinatesCLM x).1 (higherCoordinatesCLM x).2 := by
    refine ⟨hw.interval_nonempty, hw.displacementIdentity, hw.velocityIdentity, ?_⟩
    filter_upwards [hw.equationAE, hell, hq, hloadAE, hFAE] with t ht he hqt hm hFt
    have ha : acc t = higherAcceleration hk hf hf0 (u t) := by
      rw [he, hqt] at ht
      exact eq_sub_of_add_eq ht
    rw [ha, hqt, hm]
    change higherAcceleration hk hf hf0 (u t) + massForm n (higherCoordinatesCLM (u t)).1 =
      (energyTriple n).pivotToDual (wkpBaseCoordinateCLM (F t).2)
    rw [hFt, ← higherSource_sub_massForm]
    exact sub_add_cancel _ _
  have hlinear := weakWave_eq_duhamel_of_memLp hFe hFe₂ hloadAE (higherEnergyInclusionCLM n k x)
    (by simpa only [← higherCoordinatesCLM_eq_coordinates] using hmass)
  let z := fun t ↦ (higherLinearSemigroup n k).realOrbit x t +
    (higherLinearSemigroup n k).duhamel F t
  have hz : Continuous z := ((higherLinearSemigroup n k).continuous_realOrbit x).add
    (continuous_duhamel_of_locallyIntegrable (higherLinearSemigroup n k)
      (norm_higherLinearSemigroup_le n k) hF)
  have hprojF : (fun s ↦ higherEnergyInclusionCLM n k (F s)) =
      (fun s ↦ (C).symm (0, Fe s)) := by
    funext s
    change (C).symm (lowerOrderCLM (by omega : 1 ≤ k + 1) (F s).1, wkpBaseCoordinateCLM (F s).2) = _
    rw [hFzero, map_zero]
    rfl
  have hproj (t : ℝ) : higherCoordinatesCLM (z t) =
      C ((linearSemigroup n).realOrbit (higherEnergyInclusionCLM n k x) t +
        (linearSemigroup n).duhamel (fun s ↦ (C).symm (0, Fe s)) t) := by
    rw [higherCoordinatesCLM_eq_coordinates]
    dsimp only [z]
    rw [higherEnergyInclusionCLM_forced_of_locallyIntegrable n k x hF, hprojF]
  have huz : u =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))] z := by
    filter_upwards [hlinear, hq, hp] with t ht hqt hpt
    have he : higherCoordinatesCLM (u t) = higherCoordinatesCLM (z t) :=
      (Prod.ext hqt hpt).symm.trans (ht.trans (hproj t).symm)
    apply higherEnergyInclusionCLM_injective n k
    apply (C).injective
    simpa only [← higherCoordinatesCLM_eq_coordinates] using he
  let U : C(Icc (0 : ℝ) (τ : ℝ), W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :=
    ⟨fun t ↦ z t, hz.comp continuous_subtype_val⟩
  have hU (t : ℝ) (ht : t ∈ Icc 0 (τ : ℝ)) : IccExtend τ.coe_nonneg U t = z t :=
    IccExtend_of_mem τ.coe_nonneg U ht
  refine ⟨U, ?_, ?_⟩
  · intro t
    change z t = (higherLinearSemigroup n k) (t : ℝ).toNNReal x + _
    dsimp only [z, StronglyContinuousSemigroup.realOrbit]
    congr 1
    unfold StronglyContinuousSemigroup.duhamel
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le t.property.1]
    have hforce : F =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))]
        fun s ↦ higherMap hk hf hf0 (IccExtend τ.coe_nonneg U s) := by
      filter_upwards [hFAE, huz, ae_restrict_mem measurableSet_Ioc] with s hs he hmem
      rw [hs, he, hU s (Ioc_subset_Icc_self hmem)]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (Ioc_subset_Ioc le_rfl t.property.2) hforce] with s hs
    rw [hs]
    rfl
  · filter_upwards [huz, ae_restrict_mem measurableSet_Ioc] with t ht hmem
    exact ht.trans (hU t (Ioc_subset_Icc_self hmem)).symm

/-- A continuous higher weak trajectory belongs to the Bochner weak class,
with both original Cauchy data encoded by endpoint time tests. -/
theorem IsHigherWeakSolutionOn.isHigherBochnerWeakSolutionOn {hk : (n : ℝ) < 2 * (k : ℝ)}
    {hf : ContDiff ℝ (⊤ : ℕ∞) f} {hf0 : f 0 = 0} {x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)} {τ : NNReal}
    {u : C(Icc (0 : ℝ) (τ : ℝ), W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n))}
    (hu : IsHigherWeakSolutionOn hk hf hf0 x τ u) (hτ : 0 < (τ : ℝ)) :
    IsHigherBochnerWeakSolutionOn hk hf hf0 x τ (IccExtend τ.coe_nonneg u) := by
  let U : C(ℝ, W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :=
    ⟨IccExtend τ.coe_nonneg u, u.continuous.Icc_extend'⟩
  have hbounded : MemLp U ∞ (volume.restrict (Ioc 0 (τ : ℝ))) :=
    U.continuous.continuousOn.memLp_of_subset_isCompact
      isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self
  let J : W^{k,2}(ℝ^n) →L[ℝ] StrongDual ℝ H¹(ℝ^n) :=
    -(energyTriple n).pivotToDual.comp wkpBaseCoordinateCLM
  let ell := fun t ↦ J (higherReaction hk hf hf0 (U t))
  have hell : MemLp ell 2 (volume.restrict (Ioc 0 (τ : ℝ))) :=
    (J.comp_memLp' (memLp_top_higherReaction hk hf hf0 hbounded)).mono_exponent le_top
  obtain ⟨ellLp, q, p, acc, he, hq, hp, _, hw⟩ :=
    exists_weakWave_of_integrable_integral_equations (energyTriple n) (gradientForm n)
      hell (higherCoordinatesCLM.continuous.comp U.continuous) (higherCoordinatesCLM x) hτ
      (fun t ht ↦ hu.displacement t ht) (fun t ht ↦ hu.velocity t ht)
  exact ⟨hbounded, ellLp, q, p, acc, he, hq, hp, hw⟩

/-- Uniqueness holds among arbitrary essentially bounded high Sobolev weak
trajectories, without assuming time continuity of either representative. -/
theorem IsHigherBochnerWeakSolutionOn.ae_eq {hk : (n : ℝ) < 2 * (k : ℝ)}
    {hf : ContDiff ℝ (⊤ : ℕ∞) f} {hf0 : f 0 = 0} {x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)} {τ : NNReal}
    {u v : ℝ → W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)} (hu : IsHigherBochnerWeakSolutionOn hk hf hf0 x τ u)
    (hv : IsHigherBochnerWeakSolutionOn hk hf hf0 x τ v) :
    u =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))] v := by
  obtain ⟨U, hU, heU⟩ := hu.exists_continuous_mild
  obtain ⟨V, hV, heV⟩ := hv.exists_continuous_mild
  have heq : U = V := StronglyContinuousSemigroup.IsMildSolutionOn.eq_of_locallyLipschitz
      (T := higherLinearSemigroup n k) (F := higherMap hk hf hf0)
      (locallyLipschitz_higherSource hk hf hf0) hU hV
  rw [heq] at heU
  exact heU.trans heV.symm

/-- The smooth full-first-jet wave has a unique local Bochner weak solution
for arbitrary H^(s+1) × H^s data with exactly s > n/2. The solution is bounded
at these orders, and uniqueness covers the essentially bounded weak
class. Continuity of a representative is obtained as a conclusion. -/
theorem exists_unique_higher_bochnerWeak (hk : (n : ℝ) < 2 * (k : ℝ)) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf0 : f 0 = 0) (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :
    ∃ τ : NNReal, 0 < τ ∧
      ∃ u : C(Icc (0 : ℝ) (τ : ℝ), W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)),
        IsHigherWeakSolutionOn hk hf hf0 x τ u ∧
        IsHigherBochnerWeakSolutionOn hk hf hf0 x τ (IccExtend τ.coe_nonneg u) ∧
        ∀ v, IsHigherBochnerWeakSolutionOn hk hf hf0 x τ v →
          v =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))] IccExtend τ.coe_nonneg u := by
  obtain ⟨τ, hτ, u, hu, _, _⟩ := exists_unique_higher_weak hk hf hf0 x
  have hb := hu.isHigherBochnerWeakSolutionOn hτ
  exact ⟨τ, hτ, u, hu, hb, fun _ hv ↦ hv.ae_eq hb⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
