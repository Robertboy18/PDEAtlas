/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Smooth.Classical.WeakSolution.Equation
public import PDE.Hyperbolic.HigherRegularity.Smooth.Compatibility.Forcing
public import PDE.Hyperbolic.WeakWave.Classical.Trajectory

/-!
# Classical waves belong to the original weak class

Smoothness and literal zero lateral values construct the energy curve.
The pointwise equation supplies its acceleration, while the initial
values supply the initial terms of both weak identities.
-/

@[expose] public noncomputable section

open PDE (SpaceTime)

open scoped Sobolev

namespace Hyperbolic.HigherRegularity.SmoothWave.IsClassicalSolution

open Filter MeasureTheory Set PDE.Common SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity SobolevSpace.Evolution.Classical
open PDE.Analysis.Evolution

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- A classical solution determines a weak wave with the original forcing and
initial data. The spatial and temporal almost-everywhere identifications
refer to the given classical function itself. -/
theorem exists_weakWave {P : SmoothFullCoefficients n Ω} (hn : 0 < n) {hopen : IsOpen Ω}
    (hbounded : Bornology.IsBounded Ω) (hgraph : Boundary.HasC1GraphBoundary Ω) (hab : a < b)
    {f U : SpaceTime n → ℝ} {g h : ℝ^n → ℝ}
    {hf : ∀ k, ContDiffUpToBoundary k f (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b))}
    {hg : ∀ k, ContDiffUpToBoundary k g Ω} {hh : ∀ k, ContDiffUpToBoundary k h Ω}
    (hU : IsClassicalSolution P hopen hf hg hh U) :
    ∃ (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
      (v : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
      (w : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b)))
      (q₀ : H¹₀(Ω)) (p₀ : DerivLp n 2 Ω),
      Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hopen)
        (fun _ ↦ P.form hopen hbounded)
        (dirichletLoadTimeLp hopen (forcingJet hopen hbounded hab hf 0 0).head)
        u v w q₀ p₀ ∧
      (∀ᵐ t ∂volume.restrict (Ioo a b),
        (fun x ↦ U (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω]
          baseRepresentative (h10SubtypeL (u t))) ∧
      (baseCoordCLM q₀ : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] g ∧
      (p₀ : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] h := by
  let : Fact (0 < n) := ⟨hn⟩
  let q := zeroBoundaryCurve hopen hbounded hgraph hab hU.smooth hU.continuous hU.boundary 0
  let p := fun t ↦ wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU.smooth 1 1 t)
  let ell := fun t ↦ (h10L2GelfandTriple hopen).pivotToDual
    (wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hf 0 0 t))
  have hq := continuousOn_zeroBoundaryCurve hopen hbounded hgraph hab hU.smooth
    hU.continuous hU.boundary 0
  have hp : ContinuousOn p (Icc a b) := wkpBaseCoordinateCLM.continuous.comp_continuousOn
    (continuousOn_sobolevCurve hopen hbounded hab hU.smooth 1 1)
  have hell : ContinuousOn ell (Icc a b) :=
    (h10L2GelfandTriple hopen).pivotToDual.continuous.comp_continuousOn
      (wkpBaseCoordinateCLM.continuous.comp_continuousOn
        (continuousOn_sobolevCurve hopen hbounded hab hf 0 0))
  have hdq := (hasWeakTimeDerivativeOn_sobolevCurve hopen hbounded hab hU.smooth 1 0).map
    (wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Ω))
  obtain ⟨ellLp, u, v, w, hl, hu, _, _, hw⟩ :=
    Variational.exists_weakWave_of_continuousOn_weak_derivatives
      (h10L2GelfandTriple hopen) (P.form hopen hbounded) hab hq hp hell hdq
      (hU.velocity_hasWeakTimeDerivativeOn hbounded hab hgraph)
  have hforcing : ellLp =
      dirichletLoadTimeLp hopen (forcingJet hopen hbounded hab hf 0 0).head := by
    apply Lp.ext
    filter_upwards [hl,
      dirichletLoadTimeLp_apply_ae hopen (forcingJet hopen hbounded hab hf 0 0).head,
      sobolevTimeDerivative_ae hopen hbounded hab hf 0 0] with t hl ht hs
    rw [hl, ht]
    change _ = loadFunctional
      (wkpBaseCoordinateCLM (sobolevTimeDerivative hopen hbounded hab hf 0 0 t))
    rw [hs]
    rfl
  rw [hforcing] at hw
  refine ⟨u, v, w, q a, p a, hw, ?_, ?_, ?_⟩
  · have hu' := hu.filter_mono (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self))
    filter_upwards [hu', ae_restrict_mem measurableSet_Ioo] with t ht hti
    rw [ht]
    have htcc := Ioo_subset_Icc_self hti
    filter_upwards [wkpBaseCoordinate_sobolevCurve_ae hopen hbounded hab hU.smooth 1 0 htcc,
      ae_restrict_mem hopen.measurableSet] with x hx hxΩ
    exact (derivativeSlice_nil hopen hab hU.smooth hU.continuous htcc
      (subset_closure hxΩ)).symm.trans hx.symm
  · filter_upwards [wkpBaseCoordinate_sobolevCurve_ae hopen hbounded hab hU.smooth 1 0
      (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩), ae_restrict_mem hopen.measurableSet] with x hx hxΩ
    exact hx.trans ((derivativeSlice_nil hopen hab hU.smooth hU.continuous
      ⟨le_rfl, hab.le⟩ (subset_closure hxΩ)).trans ((hU.initial_value x (subset_closure hxΩ)).trans
          ((hg 0).continuousRepresentative_eqOn hxΩ)))
  · filter_upwards [wkpBaseCoordinate_sobolevCurve_ae hopen hbounded hab hU.smooth 1 1
      (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩), ae_restrict_mem hopen.measurableSet] with x hx hxΩ
    exact hx.trans ((hU.initial_velocity x (subset_closure hxΩ)).trans
      ((hh 0).continuousRepresentative_eqOn hxΩ))

end Hyperbolic.HigherRegularity.SmoothWave.IsClassicalSolution
