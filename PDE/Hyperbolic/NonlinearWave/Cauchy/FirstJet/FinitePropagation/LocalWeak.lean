/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.LocalRegularity

/-!
# Local weak PDE for the patched first-jet wave

On each bounded open set the local energy curve satisfies the displacement
identity in L² and the wave identity against every H¹₀ spatial test. These
identities use the local weak gradient and first-jet reaction. Existence is derived from the patched
models.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.GraphSpace.ZeroTrace
open PDE.Analysis.Evolution Hyperbolic.Variational

variable {n : ℕ} {Ω : Set (ℝ^n)} {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}

/-- The spatial weak form of `-Δu + f(Du,v,u)` on a subdomain. -/
def localSpatialPairing (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (z : W^{1,2}(Ω) × DerivLp n 2 Ω) (ψ : H¹₀(Ω)) : ℝ :=
  (∑ i : Fin n, ⟪z.1.val (singleDerivIndex n i),
    (ψ : W^{1,2}(Ω)).val (singleDerivIndex n i)⟫_ℝ) +
      ⟪localReaction hf hf0 z, wkpBaseCoordinateCLM (ψ : W^{1,2}(Ω))⟫_ℝ

/-- The two integrated weak wave equations on one finite cylinder. No
boundary condition is imposed on the solution; only the tests vanish on
the spatial boundary. -/
structure IsLocalWeakCurveOn (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (q : C(ℝ, W^{1,2}(Ω) × DerivLp n 2 Ω)) (T : ℝ) : Prop where
  displacement : ∀ t ∈ Icc (0 : ℝ) T,
    (∫ s in (0 : ℝ)..t, (q s).2) =
      wkpBaseCoordinateCLM (q t).1 - wkpBaseCoordinateCLM (q 0).1
  velocity : ∀ t ∈ Icc (0 : ℝ) T, ∀ ψ : H¹₀(Ω),
    -(∫ s in (0 : ℝ)..t, localSpatialPairing hf hf0 (q s) ψ) =
      ⟪(q t).2, wkpBaseCoordinateCLM (ψ : W^{1,2}(Ω))⟫_ℝ -
        ⟪(q 0).2, wkpBaseCoordinateCLM (ψ : W^{1,2}(Ω))⟫_ℝ

/-- Local weak solutions have continuous local energy representatives, the
prescribed two initial traces, and both integrated PDE identities on every
bounded finite cylinder. This definition is independent of the construction. -/
def IsLocalWeakSolution (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (g v : ℝ^n → ℝ) (w : ℝ → ℝ^n → ℝ × ℝ) : Prop :=
  ∀ (Ω : Set (ℝ^n)), IsOpen Ω → Bornology.IsBounded Ω → ∀ T : ℝ, 0 ≤ T →
    ∃ q : C(ℝ, W^{1,2}(Ω) × DerivLp n 2 Ω),
      (∀ t ∈ Icc (0 : ℝ) T,
        w t =ᵐ[domainMeasure n Ω] fun y ↦ (baseRepresentative (q t).1 y, (q t).2 y)) ∧
      (baseRepresentative (q 0).1 =ᵐ[domainMeasure n Ω] g) ∧
      ((q 0).2 : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] v ∧
      IsLocalWeakCurveOn hf hf0 q T

/-- Restricting a whole-space wave yields the local integrated PDE against
all zero-boundary spatial tests. -/
theorem IsEnergySolution.isLocalWeakCurveOn {hf : LipschitzWith L f} {hf0 : f 0 = 0}
    {x : H¹(ℝ^n) × DerivLp n 2 univ} {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (hu : IsEnergySolution hf hf0 x u) (hΩ : IsOpen Ω) (T : ℝ) :
    IsLocalWeakCurveOn hf hf0 ⟨fun t ↦ restrictStateCLM hΩ.measurableSet (u t),
      (restrictStateCLM hΩ.measurableSet).continuous.comp u.continuous⟩ T := by
  let R : DerivLp n 2 univ →L[ℝ] DerivLp n 2 Ω := restrictDerivLp (subset_univ Ω)
  constructor
  · intro t ht
    have h := congrArg R (hu.displacement t ht.1)
    rw [map_sub, ← R.intervalIntegral_comp_comm
      (u.continuous.snd.intervalIntegrable (μ := volume) 0 t)] at h
    change (∫ s in (0 : ℝ)..t, R (u s).2) = R ((energyTriple n).inclusion (u t).1) -
        R ((energyTriple n).inclusion (u 0).1)
    rwa [hu.initial]
  · intro t ht ψ
    let φ : H¹(ℝ^n) := (zeroExtendH10ToSuperset hΩ isOpen_univ (subset_univ Ω) ψ : H¹₀(ℝ^n))
    have hc (z : DerivLp n 2 univ) (a : DerivIndex n 1) :
        ⟪z, φ.val a⟫_ℝ = ⟪R z, (ψ : W^{1,2}(Ω)).val a⟫_ℝ :=
      inner_zeroExtendH10ToSuperset_coordinate_eq_inner_restrict
        hΩ isOpen_univ (subset_univ Ω) z ψ a
    have hp (s : ℝ) : acceleration hf hf0 (u s) φ =
        -localSpatialPairing hf hf0 (restrictStateCLM hΩ.measurableSet (u s)) ψ := by
      rw [acceleration_apply]
      rw [show (energyTriple n).inclusion φ = φ.val (baseIndex n 1) from rfl]
      simp only [localSpatialPairing, localReaction_restrict, hc, wkpBaseCoordinateCLM_apply]
      rfl
    have hi := congrArg (fun ℓ : StrongDual ℝ H¹(ℝ^n) ↦ ℓ φ) (hu.velocity t ht.1)
    have ha : Continuous (fun s ↦ acceleration hf hf0 (u s)) :=
      (continuous_acceleration hf hf0).comp u.continuous
    change (∫ s in (0 : ℝ)..t, acceleration hf hf0 (u s)) φ = _ at hi
    rw [ContinuousLinearMap.intervalIntegral_apply (ha.intervalIntegrable (μ := volume) 0 t)] at hi
    simp only [hp, intervalIntegral.integral_neg, sub_apply, GelfandTriple.pivotToDual_apply] at hi
    change -(∫ s in (0 : ℝ)..t,
      localSpatialPairing hf hf0 (restrictStateCLM hΩ.measurableSet (u s)) ψ) =
        ⟪R (u t).2, wkpBaseCoordinateCLM (ψ : W^{1,2}(Ω))⟫_ℝ -
          ⟪R (u 0).2, wkpBaseCoordinateCLM (ψ : W^{1,2}(Ω))⟫_ℝ
    rw [hu.initial]
    simpa only [show (energyTriple n).inclusion φ = φ.val (baseIndex n 1) from rfl,
      hc, wkpBaseCoordinateCLM_apply] using hi

/-- The patched fields satisfy the local weak PDE with the original local
Cauchy data. The construction property is used only in this proof. -/
theorem HasLocalEnergyModels.isLocalWeakSolution {hf : LipschitzWith L f} {hf0 : f 0 = 0}
    {g v : ℝ^n → ℝ} {w : ℝ → ℝ^n → ℝ × ℝ} (hw : HasLocalEnergyModels hf hf0 w)
    (hw0 : ∀ i : ℕ, w 0 =ᵐ[volume.restrict (Metric.ball 0 ((i : ℝ) + 1))] fun y ↦ (g y, v y)) :
    IsLocalWeakSolution hf hf0 g v w := by
  intro Ω hΩ hb T hT
  obtain ⟨x, u, hu, heq⟩ := hw hb T
  let q : C(ℝ, W^{1,2}(Ω) × DerivLp n 2 Ω) := ⟨fun t ↦ restrictStateCLM hΩ.measurableSet (u t),
      (restrictStateCLM hΩ.measurableSet).continuous.comp u.continuous⟩
  have hq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      w t =ᵐ[domainMeasure n Ω] fun y ↦ (baseRepresentative (q t).1 y, (q t).2 y) :=
    (heq t ht).trans (restrictStateCLM_representative_ae hΩ.measurableSet (u t)).symm
  obtain ⟨i, _, hi⟩ := exists_exhaustion_cylinder hb T
  have hzero : (fun y ↦ (baseRepresentative (q 0).1 y, (q 0).2 y))
      =ᵐ[domainMeasure n Ω] fun y ↦ (g y, v y) :=
    (hq 0 ⟨le_rfl, hT⟩).symm.trans (ae_restrict_of_ae_restrict_of_subset hi (hw0 i))
  exact ⟨q, hq, hzero.mono (fun _ h ↦ congrArg Prod.fst h),
    hzero.mono (fun _ h ↦ congrArg Prod.snd h), hu.isLocalWeakCurveOn hΩ T⟩

/-- Arbitrary local H¹ × L² data give a global forward weak first-jet wave.
Its restrictions are strongly continuous in local energy, hence bounded on
each finite time interval, and both Cauchy traces are attained. -/
theorem exists_localWeakSolution (hf : LipschitzWith L f) (hf0 : f 0 = 0) {g v : ℝ^n → ℝ}
    (hg : IsLocallyWkpOn 1 2 univ g) (hv : IsLocallyWkpOn 0 2 univ v) :
    ∃ w : ℝ → ℝ^n → ℝ × ℝ, IsLocalWeakSolution hf hf0 g v w ∧ HasLocalEnergyModels hf hf0 w := by
  obtain ⟨w, hw0, hw⟩ := exists_patched_local_energy_fields hf hf0 hg hv
  exact ⟨w, HasLocalEnergyModels.isLocalWeakSolution hw hw0, hw⟩

/-- Local H² × H¹ data give a local weak solution with the exact bounded
H²/H¹/L² persistence and time derivatives. The reaction may be
nondifferentiable; only its global first-jet Lipschitz bound is used. -/
theorem exists_localWeakSolution_h2 (hf : LipschitzWith L f) (hf0 : f 0 = 0) {g v : ℝ^n → ℝ}
    (hg : IsLocallyWkpOn 2 2 univ g) (hv : IsLocallyWkpOn 1 2 univ v) :
    ∃ w : ℝ → ℝ^n → ℝ × ℝ, IsLocalWeakSolution hf hf0 g v w ∧ HasLocalH2Regularity hf hf0 w := by
  obtain ⟨w, hw0, hw, hr⟩ := exists_patched_local_h2_fields hf hf0 hg hv
  exact ⟨w, hw.isLocalWeakSolution hw0, hr⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
