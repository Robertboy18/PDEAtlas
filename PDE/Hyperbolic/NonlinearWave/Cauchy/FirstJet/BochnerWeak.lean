/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.IntegrableLinear
public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FiniteInterval

/-!
# Energy representatives of first-jet Bochner weak waves

An arbitrary square-integrable weak wave with globally Lipschitz full-first-jet
reaction has a continuous energy representative. The linear identification uses
the square-integrable reaction as its forcing, so continuity is a
conclusion rather than a restriction on the competing weak solution.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Interval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Evolution Hyperbolic.Variational

variable {n : ℕ} {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric

/-- Every Bochner weak first-jet wave admits a continuous energy representative
on its full closed time interval, with both original initial data. -/
theorem exists_energySolutionOn_of_weakWave (hf : LipschitzWith L f) (hf0 : f 0 = 0) {τ : NNReal}
    {ell : Lp (StrongDual ℝ H¹(ℝ^n)) 2 (volume.restrict (Ioc 0 (τ : ℝ)))}
    {q : Lp H¹(ℝ^n) 2 (volume.restrict (Ioc 0 (τ : ℝ)))}
    {p : Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc 0 (τ : ℝ)))}
    {acc : Lp (StrongDual ℝ H¹(ℝ^n)) 2 (volume.restrict (Ioc 0 (τ : ℝ)))}
    {x : H¹(ℝ^n) × DerivLp n 2 univ}
    (hell : (ell : ℝ → StrongDual ℝ H¹(ℝ^n)) =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))] fun t ↦
      -(energyTriple n).pivotToDual (reaction hf hf0 (q t, p t)))
    (hw : IsGelfandWeakWaveSolution (energyTriple n) (fun _ ↦ gradientForm n) ell q p acc x.1 x.2) :
    ∃ u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ), IsEnergySolutionOn hf hf0 x τ u ∧
      (fun t ↦ (q t, p t)) =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))] u := by
  let B := ContinuousLinearMap.id ℝ (H¹(ℝ^n) × DerivLp n 2 univ)
  have hpair : MemLp (fun t ↦ (q t, p t)) 2 (volume.restrict (Ioc 0 (τ : ℝ))) :=
    (Lp.memLp (B.compLpPair (q, p))).ae_eq (B.coeFn_compLpPair q p)
  have hzero : source hf hf0 0 = 0 := by
    simp only [source, Prod.fst_zero, reaction, map_zero, LipschitzWith.compLp_zero, sub_zero]
  have hs : MemLp (fun t ↦ source hf hf0 (q t, p t)) 2 (volume.restrict (Ioc 0 (τ : ℝ))) :=
    (source_lipschitz hf hf0).comp_memLp hzero hpair
  let F := (Ioc 0 (τ : ℝ)).indicator (fun t ↦ source hf hf0 (q t, p t))
  have hFAE : F =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))]
      fun t ↦ source hf hf0 (q t, p t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using indicator_of_mem ht _
  have hF₂ : MemLp F 2 (volume.restrict (Ioc 0 (τ : ℝ))) := hs.ae_eq hFAE.symm
  have hF : LocallyIntegrable F volume :=
    (IntegrableOn.integrable_indicator (hs.integrable (by norm_num))
      measurableSet_Ioc).locallyIntegrable
  have hload := (energyTriple n).pivotToDual.comp_memLp' hF₂
  let ellM := hload.toLp (fun t ↦ (energyTriple n).pivotToDual (F t))
  have hloadAE : (ellM : ℝ → StrongDual ℝ H¹(ℝ^n)) =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))]
      fun t ↦ (energyTriple n).pivotToDual (F t) := hload.coeFn_toLp
  have hmass : IsGelfandWeakWaveSolution (energyTriple n) (fun _ ↦ massForm n)
      ellM q p acc x.1 x.2 := by
    refine ⟨hw.interval_nonempty, hw.displacementIdentity, hw.velocityIdentity, ?_⟩
    filter_upwards [hw.equationAE, hell, hloadAE, hFAE] with t ht he hm hFval
    rw [hm, hFval, source, map_sub]
    change acc t + massForm n (q t) = (energyTriple n).energyToDual (q t) -
        (energyTriple n).pivotToDual (reaction hf hf0 (q t, p t))
    rw [he] at ht
    change acc t + (massForm n (q t) - (energyTriple n).energyToDual (q t)) = _ at ht
    have hh : acc t + massForm n (q t) =
        -(energyTriple n).pivotToDual (reaction hf hf0 (q t, p t)) +
          (energyTriple n).energyToDual (q t) :=
      eq_add_of_sub_eq (by rw [add_sub_assoc]; exact ht)
    exact hh.trans (by abel)
  let y := (C).symm x
  let z := fun t ↦ C ((linearSemigroup n).realOrbit y t +
    (linearSemigroup n).duhamel (fun s ↦ (C).symm (0, F s)) t)
  have hae : (fun t ↦ (q t, p t)) =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))] z :=
    weakWave_eq_duhamel_of_memLp hF hF₂ hloadAE y
      (by simpa only [y, ContinuousLinearEquiv.apply_symm_apply] using hmass)
  let J : DerivLp n 2 univ →L[ℝ] EnergyState n := (C).symm.toContinuousLinearMap.comp
      ((0 : DerivLp n 2 univ →L[ℝ] H¹(ℝ^n)).prod (.id ℝ _))
  have hj : LocallyIntegrable (fun r ↦ (C).symm (0, F r)) volume :=
    fun r ↦ J.integrableAtFilter_comp (hF r)
  have hS : ∀ r, ‖linearSemigroup n r‖ ≤ 1 :=
    waveContractionSemigroup_isContraction (energyTriple n) (massForm n)
      (massForm_coercive n) massForm_symmetric
  have hz : Continuous z := (C).continuous.comp (((linearSemigroup n).continuous_realOrbit y).add
      (continuous_duhamel_of_locallyIntegrable (linearSemigroup n) hS hj))
  refine ⟨⟨z, hz⟩, ⟨hz.continuousOn, ?_, ?_, ?_⟩, hae⟩
  · simp only [ContinuousMap.coe_mk, z, StronglyContinuousSemigroup.realOrbit_zero,
      StronglyContinuousSemigroup.duhamel_zero, add_zero, y, ContinuousLinearEquiv.apply_symm_apply]
  · intro t ht
    simpa only [ContinuousMap.coe_mk, z, y, ContinuousLinearEquiv.apply_symm_apply] using
      (linear_forced_integral_of_locallyIntegrable hF y ht.1).1
  · intro t ht
    have hvel := (linear_forced_integral_of_locallyIntegrable hF y ht.1).2
    simp only [y, ContinuousLinearEquiv.apply_symm_apply] at hvel
    refine Eq.trans ?_ hvel
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le ht.1]
    have hfz : F =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))]
        fun s ↦ source hf hf0 (z s) := by
      filter_upwards [hFAE, hae] with s hs he using hs.trans (congrArg (source hf hf0) he)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc le_rfl ht.2) hfz] with s hs
    change acceleration hf hf0 (z s) = (energyTriple n).pivotToDual (F s) - massForm n (z s).1
    rw [hs, source_sub_massForm]

/-- A Bochner weak solution and an energy-continuous solution with the same
initial data agree almost everywhere. -/
theorem weakWave_eq_energySolution (hf : LipschitzWith L f) (hf0 : f 0 = 0) {τ : NNReal}
    {ell : Lp (StrongDual ℝ H¹(ℝ^n)) 2 (volume.restrict (Ioc 0 (τ : ℝ)))}
    {q : Lp H¹(ℝ^n) 2 (volume.restrict (Ioc 0 (τ : ℝ)))}
    {p : Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc 0 (τ : ℝ)))}
    {acc : Lp (StrongDual ℝ H¹(ℝ^n)) 2 (volume.restrict (Ioc 0 (τ : ℝ)))}
    {x : H¹(ℝ^n) × DerivLp n 2 univ}
    (hell : (ell : ℝ → StrongDual ℝ H¹(ℝ^n)) =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))] fun t ↦
      -(energyTriple n).pivotToDual (reaction hf hf0 (q t, p t)))
    (hw : IsGelfandWeakWaveSolution (energyTriple n) (fun _ ↦ gradientForm n) ell q p acc x.1 x.2)
    {u : ℝ → H¹(ℝ^n) × DerivLp n 2 univ} (hu : IsEnergySolutionOn hf hf0 x τ u) :
    (fun t ↦ (q t, p t)) =ᵐ[volume.restrict (Ioc 0 (τ : ℝ))] u := by
  obtain ⟨v, hv, hae⟩ := exists_energySolutionOn_of_weakWave hf hf0 hell hw
  have heq := hv.eqOn hu
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioc] with t ht hmem
  exact ht.trans (heq (Ioc_subset_Icc_self hmem))

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
