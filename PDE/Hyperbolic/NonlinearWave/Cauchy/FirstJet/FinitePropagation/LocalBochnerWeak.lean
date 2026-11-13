/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.LocalWeak
public import PDE.Hyperbolic.NonlinearWave.Cauchy.IntegrableTrajectory

/-!
# Local Bochner weak equations for full first-jet waves

The local weak equations are stated for square-integrable energy trajectories,
with both Cauchy traces encoded by endpoint time tests. Continuous local energy
solutions satisfy these equations. The definition itself assumes neither time
continuity nor a whole-space model.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.GraphSpace.ZeroTrace
open PDE.Analysis.Evolution

variable {n : ℕ} {Ω : Set (ℝ^n)} {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}

/-- The local spatial weak pairing is continuous in the natural energy state. -/
theorem continuous_localSpatialPairing (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (ψ : H¹₀(Ω)) : Continuous (fun z ↦ localSpatialPairing hf hf0 z ψ) := by
  apply Continuous.add
  · apply continuous_finsetSum
    intro i _
    exact ((wkpCoordinateCLM (singleDerivIndex n i)).continuous.comp continuous_fst).inner
      continuous_const
  · exact (localReaction_lipschitz hf hf0).continuous.inner continuous_const

/-- The local distributional wave equations with both initial traces, for
an arbitrary square-integrable local energy trajectory. Spatial tests in the
velocity equation vanish on the boundary; the solution has no boundary condition. -/
structure IsLocalBochnerWeakCurveOn (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (x : W^{1,2}(Ω) × DerivLp n 2 Ω) (T : ℝ)
    (u : ℝ → W^{1,2}(Ω) × DerivLp n 2 Ω) : Prop where
  interval_nonempty : 0 < T
  integrable : MemLp u 2 (volume.restrict (Ioc 0 T))
  displacement : ∀ (ψ : W^{1,2}(Ω)) (τ : TimeTest 0 T),
    -(∫ t in (0 : ℝ)..T,
      ⟪wkpBaseCoordinateCLM ψ, wkpBaseCoordinateCLM (u t).1⟫_ℝ * τ.derivFun t) =
      (∫ t in (0 : ℝ)..T, ⟪wkpBaseCoordinateCLM ψ, (u t).2⟫_ℝ * τ.toFun t) +
        ⟪wkpBaseCoordinateCLM ψ, wkpBaseCoordinateCLM x.1⟫_ℝ * τ.toFun 0
  velocity : ∀ (ψ : H¹₀(Ω)) (τ : TimeTest 0 T),
    -(∫ t in (0 : ℝ)..T,
      ⟪wkpBaseCoordinateCLM (ψ : W^{1,2}(Ω)), (u t).2⟫_ℝ * τ.derivFun t) =
      (∫ t in (0 : ℝ)..T, -localSpatialPairing hf hf0 (u t) ψ * τ.toFun t) +
        ⟪wkpBaseCoordinateCLM (ψ : W^{1,2}(Ω)), x.2⟫_ℝ * τ.toFun 0

/-- Continuous local weak curves satisfy all endpoint time tests. -/
theorem IsLocalWeakCurveOn.isLocalBochnerWeakCurveOn {hf : LipschitzWith L f} {hf0 : f 0 = 0}
    {u : C(ℝ, W^{1,2}(Ω) × DerivLp n 2 Ω)} {T : ℝ} (hu : IsLocalWeakCurveOn hf hf0 u T)
    (hT : 0 < T) :
    IsLocalBochnerWeakCurveOn hf hf0 (u 0) T u := by
  refine ⟨hT, memLp_restrict_Ioc_of_continuousOn u.continuous.continuousOn, ?_, ?_⟩
  · intro ψ τ
    let A : DerivLp n 2 Ω →L[ℝ] ℝ := innerSL ℝ (wkpBaseCoordinateCLM ψ)
    apply initial_identity_of_integrable_primitive hT.le τ
      ((A.continuous.comp u.continuous.snd).intervalIntegrable (μ := volume) 0 T)
    intro t ht
    change (∫ s in (0 : ℝ)..t, A ((u s).2)) = _
    rw [A.intervalIntegral_comp_comm (u.continuous.snd.intervalIntegrable (μ := volume) 0 t),
      hu.displacement t ht, map_sub]
    rfl
  · intro ψ τ
    have hg : Continuous (fun t ↦ -localSpatialPairing hf hf0 (u t) ψ) :=
      ((continuous_localSpatialPairing hf hf0 ψ).comp u.continuous).neg
    apply initial_identity_of_integrable_primitive hT.le τ (hg.intervalIntegrable (μ := volume) 0 T)
    intro t ht
    rw [intervalIntegral.integral_neg, hu.velocity t ht ψ]
    rw [real_inner_comm (u t).2, real_inner_comm (u 0).2]

/-- Square-integrable local weak solutions with prescribed Cauchy data on
every bounded finite cylinder. All field identifications are almost everywhere. -/
def IsLocalBochnerWeakSolution (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (g v : ℝ^n → ℝ) (w : ℝ → ℝ^n → ℝ × ℝ) : Prop :=
  ∀ (Ω : Set (ℝ^n)), IsOpen Ω → Bornology.IsBounded Ω → ∀ T : ℝ, 0 < T →
    ∃ (x : W^{1,2}(Ω) × DerivLp n 2 Ω) (u : ℝ → W^{1,2}(Ω) × DerivLp n 2 Ω),
      (baseRepresentative x.1 =ᵐ[domainMeasure n Ω] g) ∧
      ((x.2 : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] v) ∧
      (∀ᵐ t ∂volume.restrict (Ioc 0 T),
        w t =ᵐ[domainMeasure n Ω] fun y ↦ (baseRepresentative (u t).1 y, (u t).2 y)) ∧
      IsLocalBochnerWeakCurveOn hf hf0 x T u

/-- The local energy representative gives a Bochner weak solution in the
same local Sobolev spaces, with both original initial data. -/
theorem IsLocalWeakSolution.isLocalBochnerWeakSolution {hf : LipschitzWith L f} {hf0 : f 0 = 0}
    {g v : ℝ^n → ℝ} {w : ℝ → ℝ^n → ℝ × ℝ} (hw : IsLocalWeakSolution hf hf0 g v w) :
    IsLocalBochnerWeakSolution hf hf0 g v w := by
  intro Ω hΩ hb T hT
  obtain ⟨u, hu, hg, hv, hweak⟩ := hw Ω hΩ hb T hT.le
  refine ⟨u 0, u, hg, hv, ?_, hweak.isLocalBochnerWeakCurveOn hT⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact hu t (Ioc_subset_Icc_self ht)

/-- Arbitrary local H¹ displacement and local L² velocity admit a forward
Bochner weak wave for every globally Lipschitz full first-jet reaction fixing zero. -/
theorem exists_localBochnerWeakSolution (hf : LipschitzWith L f) (hf0 : f 0 = 0) {g v : ℝ^n → ℝ}
    (hg : IsLocallyWkpOn 1 2 univ g) (hv : IsLocallyWkpOn 0 2 univ v) :
    ∃ w : ℝ → ℝ^n → ℝ × ℝ, IsLocalBochnerWeakSolution hf hf0 g v w := by
  obtain ⟨w, hw, _⟩ := exists_localWeakSolution hf hf0 hg hv
  exact ⟨w, hw.isLocalBochnerWeakSolution⟩

/-- The same local Bochner weak solution has bounded H²/H¹/L² persistence when its data have local
H²/H¹ regularity. -/
theorem exists_localBochnerWeakSolution_h2 (hf : LipschitzWith L f) (hf0 : f 0 = 0) {g v : ℝ^n → ℝ}
    (hg : IsLocallyWkpOn 2 2 univ g) (hv : IsLocallyWkpOn 1 2 univ v) :
    ∃ w : ℝ → ℝ^n → ℝ × ℝ,
      IsLocalBochnerWeakSolution hf hf0 g v w ∧ HasLocalH2Regularity hf hf0 w := by
  obtain ⟨w, hw, hr⟩ := exists_localWeakSolution_h2 hf hf0 hg hv
  exact ⟨w, hw.isLocalBochnerWeakSolution, hr⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
