/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.LocalCutoff
public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.LocalBochnerWeak
public import PDE.Hyperbolic.NonlinearWave.Cauchy.WeakTimeTests
public import PDE.Hyperbolic.NonlinearWave.Cauchy.IntegrableLinear

/-!
# Whole-space representatives of compactly localized weak waves

A local square-integrable weak energy trajectory becomes a whole-space forced
wave after multiplication by a compact spatial cutoff. The commutator belongs
to spatial L². Linear weak-wave uniqueness then supplies a continuous energy
representative without any assumed time continuity of the local solution.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal InnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.GraphSpace.ZeroTrace
open PDE.Analysis.Evolution Hyperbolic.Variational

variable {n : ℕ} {Ω : Set (ℝ^n)} {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}

/-- Compact localization of both components of an energy state. -/
def localCutoffStateCLM (hΩ : IsOpen Ω)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ Ω) :
    (H¹(Ω) × DerivLp n 2 Ω) →L[ℝ] (H¹(ℝ^n) × DerivLp n 2 univ) :=
  ((localCutoffDisplacementCLM hΩ η hη).comp (.fst ℝ _ _)).prod
    ((localCutoffVelocityCLM hΩ.measurableSet η).comp (.snd ℝ _ _))

/-- The spatial L² forcing of the compactly localized massive wave. -/
def localCutoffForcing (hΩ : IsOpen Ω)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ Ω)
    (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (z : H¹(Ω) × DerivLp n 2 Ω) : DerivLp n 2 univ :=
  localCutoffVelocityCLM hΩ.measurableSet η
    (wkpBaseCoordinateCLM z.1 - localReaction hf hf0 z) -
      localCutoffCommutatorCLM hΩ η hη z.1

/-- The local first-jet reaction preserves square-integrability in time. -/
theorem memLp_localReaction (hf : LipschitzWith L f) (hf0 : f 0 = 0) {μ : Measure ℝ}
    {u : ℝ → H¹(Ω) × DerivLp n 2 Ω} (hu : MemLp u 2 μ) :
    MemLp (fun t ↦ localReaction hf hf0 (u t)) 2 μ := by
  have hz : localReaction (Ω := Ω) hf hf0 0 = 0 := by
    unfold localReaction
    rw [map_zero, hf.compLp_zero hf0]
  exact (localReaction_lipschitz hf hf0).comp_memLp
    (g := localReaction (Ω := Ω) hf hf0) (f := u) hz hu

/-- The local massive source is square-integrable in time at the energy level. -/
theorem memLp_localMassSource (hf : LipschitzWith L f) (hf0 : f 0 = 0) {μ : Measure ℝ}
    {u : ℝ → H¹(Ω) × DerivLp n 2 Ω} (hu : MemLp u 2 μ) :
    MemLp (fun t ↦ wkpBaseCoordinateCLM (u t).1 - localReaction hf hf0 (u t)) 2 μ := by
  let Q : (H¹(Ω) × DerivLp n 2 Ω) →L[ℝ] DerivLp n 2 Ω := wkpBaseCoordinateCLM.comp (.fst ℝ _ _)
  exact (Q.comp_memLp' hu).sub (memLp_localReaction hf hf0 hu)

/-- Local L²-time energy control suffices for L²-time control of the cutoff force. -/
theorem memLp_localCutoffForcing (hΩ : IsOpen Ω) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hη : tsupport η.toFun ⊆ Ω) (hf : LipschitzWith L f) (hf0 : f 0 = 0) {μ : Measure ℝ}
    {u : ℝ → H¹(Ω) × DerivLp n 2 Ω} (hu : MemLp u 2 μ) :
    MemLp (fun t ↦ localCutoffForcing hΩ η hη hf hf0 (u t)) 2 μ := by
  let A : (H¹(Ω) × DerivLp n 2 Ω) →L[ℝ] DerivLp n 2 univ :=
    (localCutoffCommutatorCLM hΩ η hη).comp (.fst ℝ _ _)
  have hA : MemLp (fun t ↦ A (u t)) 2 μ := A.comp_memLp' hu
  have hB := (localCutoffVelocityCLM hΩ.measurableSet η).comp_memLp'
    (memLp_localMassSource hf hf0 hu)
  exact hB.sub hA

/-- The localized acceleration is exactly the original weak spatial pairing
against the localized test function. -/
theorem localCutoffForcing_sub_massForm (hΩ : IsOpen Ω) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hη : tsupport η.toFun ⊆ Ω) (hf : LipschitzWith L f) (hf0 : f 0 = 0) (z : H¹(Ω) × DerivLp n 2 Ω)
    (φ : H¹(ℝ^n)) :
    ((energyTriple n).pivotToDual (localCutoffForcing hΩ η hη hf hf0 z) -
      massForm n (localCutoffDisplacementCLM hΩ η hη z.1)) φ =
      -localSpatialPairing hf hf0 z (localCutoffTestCLM hΩ η hη φ) := by
  have hg := gradientForm_localCutoffDisplacementCLM hΩ η hη z.1 φ
  change massForm n (localCutoffDisplacementCLM hΩ η hη z.1) φ -
    ⟪wkpBaseCoordinateCLM (localCutoffDisplacementCLM hΩ η hη z.1),
      wkpBaseCoordinateCLM φ⟫_ℝ = _ at hg
  rw [localCutoffDisplacementCLM_base] at hg
  simp only [localCutoffForcing, sub_apply, GelfandTriple.pivotToDual_apply, map_sub]
  change (⟪localCutoffVelocityCLM hΩ.measurableSet η (wkpBaseCoordinateCLM z.1),
      wkpBaseCoordinateCLM φ⟫_ℝ -
    ⟪localCutoffVelocityCLM hΩ.measurableSet η (localReaction hf hf0 z), wkpBaseCoordinateCLM φ⟫_ℝ -
    ⟪localCutoffCommutatorCLM hΩ η hη z.1, wkpBaseCoordinateCLM φ⟫_ℝ) - _ = _
  rw [inner_localCutoffVelocityCLM hΩ η hη (localReaction hf hf0 z) φ]
  dsimp only [localSpatialPairing]
  simp only [wkpCoordinateCLM_apply] at hg
  linarith only [hg]

/-- The endpoint time tests of a local weak wave give a whole-space
Gelfand weak wave after compact localization. -/
theorem IsLocalBochnerWeakCurveOn.exists_cutoff_weakWave (hΩ : IsOpen Ω)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ Ω) {hf : LipschitzWith L f}
    {hf0 : f 0 = 0} {x : H¹(Ω) × DerivLp n 2 Ω} {T : ℝ} {u : ℝ → H¹(Ω) × DerivLp n 2 Ω}
    (hu : IsLocalBochnerWeakCurveOn hf hf0 x T u) :
    ∃ (ell : Lp (StrongDual ℝ H¹(ℝ^n)) 2 (volume.restrict (Ioc 0 T)))
      (q : Lp H¹(ℝ^n) 2 (volume.restrict (Ioc 0 T)))
      (p : Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc 0 T)))
      (acc : Lp (StrongDual ℝ H¹(ℝ^n)) 2 (volume.restrict (Ioc 0 T))),
      (ell : ℝ → StrongDual ℝ H¹(ℝ^n)) =ᵐ[volume.restrict (Ioc 0 T)]
        (fun t ↦ (energyTriple n).pivotToDual (localCutoffForcing hΩ η hη hf hf0 (u t))) ∧
      (fun t ↦ (q t, p t)) =ᵐ[volume.restrict (Ioc 0 T)]
        (fun t ↦ localCutoffStateCLM hΩ η hη (u t)) ∧
      IsGelfandWeakWaveSolution (energyTriple n) (fun _ ↦ massForm n)
        ell q p acc (localCutoffStateCLM hΩ η hη x).1
          (localCutoffStateCLM hΩ η hη x).2 := by
  let D := localCutoffStateCLM hΩ η hη
  let F := fun t ↦ (energyTriple n).pivotToDual (localCutoffForcing hΩ η hη hf hf0 (u t))
  have hF : MemLp F 2 (volume.restrict (Ioc 0 T)) := (energyTriple n).pivotToDual.comp_memLp'
      (memLp_localCutoffForcing hΩ η hη hf hf0 hu.integrable)
  have hd : ∀ (φ : H¹(ℝ^n)) (τ : TimeTest 0 T), -(∫ t in (0 : ℝ)..T,
        ⟪(energyTriple n).inclusion (D (u t)).1, (energyTriple n).inclusion φ⟫_ℝ * τ.derivFun t) =
        (∫ t in (0 : ℝ)..T, ⟪(D (u t)).2, (energyTriple n).inclusion φ⟫_ℝ * τ.toFun t) +
          ⟪(energyTriple n).inclusion (D x).1, (energyTriple n).inclusion φ⟫_ℝ * τ.toFun 0 := by
    intro φ τ
    have hid := hu.displacement (localCutoffTestCLM hΩ η hη φ) τ
    change -(∫ t in (0 : ℝ)..T, ⟪wkpBaseCoordinateCLM (localCutoffDisplacementCLM hΩ η hη (u t).1),
        wkpBaseCoordinateCLM φ⟫_ℝ * τ.derivFun t) = (∫ t in (0 : ℝ)..T,
        ⟪localCutoffVelocityCLM hΩ.measurableSet η (u t).2, wkpBaseCoordinateCLM φ⟫_ℝ * τ.toFun t) +
        ⟪wkpBaseCoordinateCLM (localCutoffDisplacementCLM hΩ η hη x.1),
          wkpBaseCoordinateCLM φ⟫_ℝ * τ.toFun 0
    simp_rw [localCutoffDisplacementCLM_base, inner_localCutoffVelocityCLM hΩ η hη]
    have hswap (b : DerivLp n 2 Ω) :
        ⟪b, wkpBaseCoordinateCLM (localCutoffTestCLM hΩ η hη φ : H¹(Ω))⟫_ℝ =
          ⟪wkpBaseCoordinateCLM (localCutoffTestCLM hΩ η hη φ : H¹(Ω)), b⟫_ℝ := real_inner_comm _ _
    simp_rw [hswap]
    exact hid
  have hv : ∀ (φ : H¹(ℝ^n)) (τ : TimeTest 0 T),
      -(∫ t in (0 : ℝ)..T, ⟪(D (u t)).2, (energyTriple n).inclusion φ⟫_ℝ * τ.derivFun t) =
        (∫ t in (0 : ℝ)..T, (F t - massForm n (D (u t)).1) φ * τ.toFun t) +
          ⟪(D x).2, (energyTriple n).inclusion φ⟫_ℝ * τ.toFun 0 := by
    intro φ τ
    have hid := hu.velocity (localCutoffTestCLM hΩ η hη φ) τ
    change -(∫ t in (0 : ℝ)..T,
      ⟪localCutoffVelocityCLM hΩ.measurableSet η (u t).2, wkpBaseCoordinateCLM φ⟫_ℝ *
        τ.derivFun t) = (∫ t in (0 : ℝ)..T,
        ((energyTriple n).pivotToDual (localCutoffForcing hΩ η hη hf hf0 (u t)) -
          massForm n (localCutoffDisplacementCLM hΩ η hη (u t).1)) φ * τ.toFun t) +
        ⟪localCutoffVelocityCLM hΩ.measurableSet η x.2, wkpBaseCoordinateCLM φ⟫_ℝ * τ.toFun 0
    simp_rw [inner_localCutoffVelocityCLM hΩ η hη, localCutoffForcing_sub_massForm hΩ η hη hf hf0]
    have hswap (b : DerivLp n 2 Ω) :
        ⟪b, wkpBaseCoordinateCLM (localCutoffTestCLM hΩ η hη φ : H¹(Ω))⟫_ℝ =
          ⟪wkpBaseCoordinateCLM (localCutoffTestCLM hΩ η hη φ : H¹(Ω)), b⟫_ℝ := real_inner_comm _ _
    simp_rw [hswap]
    exact hid
  obtain ⟨ell, q, p, acc, hell, hq, hp, _, hw⟩ :=
    exists_weakWave_of_memLp_timeTests (energyTriple n) (massForm n) hF
      (D.comp_memLp' hu.integrable) (D x) hu.interval_nonempty hd hv
  refine ⟨ell, q, p, acc, hell, ?_, hw⟩
  filter_upwards [hq, hp] with t hqt hpt
  exact Prod.ext hqt hpt

/-- Every compact localization of a local weak wave has a continuous energy
representative, equal to the linear Duhamel solution with its cutoff force. -/
theorem IsLocalBochnerWeakCurveOn.exists_continuous_cutoff (hΩ : IsOpen Ω)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ Ω) {hf : LipschitzWith L f}
    {hf0 : f 0 = 0} {x : H¹(Ω) × DerivLp n 2 Ω} {T : ℝ} {u : ℝ → H¹(Ω) × DerivLp n 2 Ω}
    (hu : IsLocalBochnerWeakCurveOn hf hf0 x T u) :
    let C := WaveEnergySpace.coordinates
      (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric
    let F := (Ioc 0 T).indicator (fun t ↦ localCutoffForcing hΩ η hη hf hf0 (u t))
    ∃ z : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ),
      (fun t ↦ localCutoffStateCLM hΩ η hη (u t)) =ᵐ[volume.restrict (Ioc 0 T)] z ∧
      ∀ t, z t = C ((linearSemigroup n).realOrbit
        (C.symm (localCutoffStateCLM hΩ η hη x)) t +
          (linearSemigroup n).duhamel (fun s ↦ C.symm (0, F s)) t) := by
  intro C F
  have hs := memLp_localCutoffForcing hΩ η hη hf hf0 hu.integrable
  have hFAE : F =ᵐ[volume.restrict (Ioc 0 T)]
      fun t ↦ localCutoffForcing hΩ η hη hf hf0 (u t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact indicator_of_mem ht _
  have hF₂ : MemLp F 2 (volume.restrict (Ioc 0 T)) := hs.ae_eq hFAE.symm
  have hF : LocallyIntegrable F volume :=
    (IntegrableOn.integrable_indicator (hs.integrable (by norm_num))
      measurableSet_Ioc).locallyIntegrable
  obtain ⟨ell, q, p, acc, hell, hqp, hw⟩ := hu.exists_cutoff_weakWave hΩ η hη
  have hell' : (ell : ℝ → StrongDual ℝ H¹(ℝ^n)) =ᵐ[volume.restrict (Ioc 0 T)]
      fun t ↦ (energyTriple n).pivotToDual (F t) := by
    filter_upwards [hell, hFAE] with t ht hft
    exact ht.trans (congrArg (energyTriple n).pivotToDual hft.symm)
  let y := C.symm (localCutoffStateCLM hΩ η hη x)
  let z := fun t ↦ C ((linearSemigroup n).realOrbit y t +
    (linearSemigroup n).duhamel (fun s ↦ C.symm (0, F s)) t)
  have hae : (fun t ↦ (q t, p t)) =ᵐ[volume.restrict (Ioc 0 T)] z :=
    weakWave_eq_duhamel_of_memLp hF hF₂ hell' y
      (by simpa only [y, C, ContinuousLinearEquiv.apply_symm_apply] using hw)
  let J : DerivLp n 2 univ →L[ℝ] EnergyState n := C.symm.toContinuousLinearMap.comp
      ((0 : DerivLp n 2 univ →L[ℝ] H¹(ℝ^n)).prod (.id ℝ _))
  have hJ : LocallyIntegrable (fun s ↦ C.symm (0, F s)) volume :=
    fun s ↦ J.integrableAtFilter_comp (hF s)
  have hS : ∀ r, ‖linearSemigroup n r‖ ≤ 1 :=
    waveContractionSemigroup_isContraction (energyTriple n) (massForm n)
      (massForm_coercive n) massForm_symmetric
  have hz : Continuous z := C.continuous.comp (((linearSemigroup n).continuous_realOrbit y).add
      (continuous_duhamel_of_locallyIntegrable (linearSemigroup n) hS hJ))
  exact ⟨⟨z, hz⟩, hqp.symm.trans hae, fun _ ↦ rfl⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
