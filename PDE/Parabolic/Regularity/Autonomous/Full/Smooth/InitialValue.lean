/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Full.Smooth.Equation.Sobolev

/-!
# Initial values of the smooth parabolic representative

The continuous Sobolev curve of the representative equals the original weak
solution's continuous pivot trace. Its initial slice therefore has the prescribed
initial class. Spatial continuity recovers the initial values pointwise,
including on the boundary whenever the datum is continuous on the spatial
closure.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.Smooth

open Filter MeasureTheory Set PDE.Common PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.GraphSpace.BoundaryRegularity
open SobolevSpace.Evolution.Classical HigherOrder

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

local notation "Q" => splitSpaceTime ⁻¹' Set.prod Ω (Ioo a b)
local notation "K" => splitSpaceTime ⁻¹' Set.prod (closure Ω) (Icc a b)

/-- The initial Sobolev slice is the prescribed pivot datum of the original
weak solution. No separate initial trace is assumed. -/
theorem initial_sobolev_value (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    {f U : SpaceTime n → ℝ}
    (hf : ∀ k, ContDiffUpToBoundary k f Q)
    (hU : ∀ k, ContDiffUpToBoundary k U Q) (hc : ContinuousOn U K)
    (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
    (hae : ∀ᵐ t ∂volume.restrict (Ioo a b),
      (fun x ↦ U (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω]
        baseRepresentative (h10SubtypeL (u t)))
    {g : DerivLp n 2 Ω}
    (hu : IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
      (fun _ ↦ P.form hopen hbounded)
      ((h10L2GelfandTriple hopen).pivotToDual.compLpL 2 (volume.restrict (Ioc a b))
        (forcingJet hopen hbounded hab hf 0 0).headBase) u g) (r : ℕ) :
    wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU r 0 a) = g := by
  obtain ⟨v, E, _, hinit, _⟩ := hu.exists_continuousPivotEvolutionOn_initial_L2
    (fun _ ↦ aestronglyMeasurable_const) ‖P.form hopen hbounded‖
    (Eventually.of_forall fun _ ↦ le_rfl) hab
  have hE : E.representative =ᵐ[volume.restrict (Ioo a b)]
      fun t ↦ baseCoordCLM (u t) := by
    have h := E.ae_eq_inclusion
    rw [uIcc_of_le hab.le] at h
    exact h.filter_mono (ae_mono (volume.restrict_mono_set Ioo_subset_Icc_self))
  have heq : (fun t ↦ wkpBaseCoordinateCLM
      (sobolevCurve hopen hbounded hab hU r 0 t)) =ᵐ[volume.restrict (Icc a b)]
        E.representative := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    filter_upwards [hae, hE, ae_restrict_mem measurableSet_Ioo] with t ht hEt htm
    exact (wkpBaseCoordinate_sobolevCurve_zero_eq hopen hbounded hab hU hc r
      (Ioo_subset_Icc_self htm) ht).trans hEt.symm
  have hon := Measure.eqOn_Icc_of_ae_eq volume hab.ne heq
    (wkpBaseCoordinateCLM.continuous.comp_continuousOn
      (continuousOn_sobolevCurve hopen hbounded hab hU r 0))
    (by simpa only [uIcc_of_le hab.le] using E.continuousOn)
  exact (hon ⟨le_rfl, hab.le⟩).trans hinit

/-- Continuous initial data are attained pointwise on the entire spatial
closure by the one smooth representative of the original weak solution. -/
theorem pointwise_initial_value (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    {f U : SpaceTime n → ℝ}
    (hf : ∀ k, ContDiffUpToBoundary k f Q)
    (hU : ∀ k, ContDiffUpToBoundary k U Q) (hc : ContinuousOn U K)
    (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
    (hae : ∀ᵐ t ∂volume.restrict (Ioo a b),
      (fun x ↦ U (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω]
        baseRepresentative (h10SubtypeL (u t)))
    {g : ℝ^n → ℝ} (hg : ContDiffUpToBoundary 0 g Ω)
    (hgc : ContinuousOn g (closure Ω))
    (hu : IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
      (fun _ ↦ P.form hopen hbounded)
      ((h10L2GelfandTriple hopen).pivotToDual.compLpL 2 (volume.restrict (Ioc a b))
        (forcingJet hopen hbounded hab hf 0 0).headBase)
      u (hg.toLp hopen hbounded 2)) :
    ∀ x ∈ closure Ω, U (timeSpaceCons a x) = g x := by
  have hinit := initial_sobolev_value P hopen hbounded hab hf hU hc u hae hu 0
  have hslice : ContinuousOn (fun x ↦ U (timeSpaceCons a x)) (closure Ω) :=
    hc.comp ((spaceTimeContinuousLinearEquiv n).symm.continuous.comp
      (continuous_id.prodMk continuous_const)).continuousOn
      (by
        intro x hx
        change splitSpaceTime (joinSpaceTime (x, a)) ∈ closure Ω ×ˢ Icc a b
        rw [split_joinSpaceTime]
        exact ⟨hx, le_rfl, hab.le⟩)
  have hs : (fun x ↦ U (timeSpaceCons a x)) =ᵐ[domainMeasure n Ω] g := by
    have hclass := wkpBaseCoordinate_sobolevCurve_ae hopen hbounded hab hU 0 0
      (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩)
    rw [hinit] at hclass
    filter_upwards [hclass, hg.toLp_coeFn hopen hbounded 2,
      ae_restrict_mem hopen.measurableSet] with x hx hgx hxΩ
    exact (derivativeSlice_nil hopen hab hU hc ⟨le_rfl, hab.le⟩
      (subset_closure hxΩ)).symm.trans (hx.symm.trans hgx)
  exact (Measure.eqOn_open_of_ae_eq hs hopen (hslice.mono subset_closure)
    (hgc.mono subset_closure)).of_subset_closure hslice hgc subset_closure Subset.rfl

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.Smooth
