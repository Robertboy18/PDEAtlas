/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Full.Smooth.Equation.Pointwise
public import PDE.Spaces.Sobolev.Evolution.Classical.Data.ZeroBoundary
public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Distributional
public import PDE.Analysis.Evolution.Integrated.WeakEquation

/-!
# Every smooth classical solution is a weak solution

Zero lateral values give an `H¹₀` trajectory and its time derivative. The
classical full equation identifies its variational residual, and the
continuous initial slice gives the integrated weak formulation, in
`isWeakSolution_of_pointwise`. Classical uniqueness then follows from weak
uniqueness.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.Smooth

open Filter MeasureTheory Set PDE.Common PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.GraphSpace.BoundaryRegularity
open SobolevSpace.Evolution.Classical HigherOrder

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {a b : ℝ}

local notation "Q" => splitSpaceTime ⁻¹' Set.prod Ω (Ioo a b)
local notation "K" => splitSpaceTime ⁻¹' Set.prod (closure Ω) (Icc a b)

/-- The pointwise classical PDE and zero lateral values imply the integrated
weak equation, with initial value the continuous initial slice. -/
theorem isWeakSolution_of_pointwise (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) (hab : a < b)
    {f U : SpaceTime n → ℝ}
    (hf : ∀ k, ContDiffUpToBoundary k f Q)
    (hU : ∀ k, ContDiffUpToBoundary k U Q) (hc : ContinuousOn U K)
    (hzero : ∀ t ∈ Icc a b, ∀ x ∈ frontier Ω, U (timeSpaceCons t x) = 0)
    (heq : ∀ t ∈ Ioo a b, ∀ x ∈ Ω,
      (∂[0] U) (timeSpaceCons t x) +
          P.classicalLoad (fun y ↦ U (timeSpaceCons t y)) x =
        f (timeSpaceCons t x)) :
    IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
      (fun _ ↦ P.form hopen hbounded)
      ((h10L2GelfandTriple hopen).pivotToDual.compLpL 2 (volume.restrict (Ioc a b))
        (forcingJet hopen hbounded hab hf 0 0).headBase)
      (zeroBoundaryTimeDerivative hopen hbounded hgraph hab hU hc hzero 0)
      (wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU 1 0 a)) := by
  let T := h10L2GelfandTriple hopen
  let u := zeroBoundaryTimeDerivative hopen hbounded hgraph hab hU hc hzero 0
  let v := zeroBoundaryTimeDerivative hopen hbounded hgraph hab hU hc hzero 1
  let du := T.energyToDual.compLpL 2 (volume.restrict (Ioc a b)) v
  let ell := T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b))
    (forcingJet hopen hbounded hab hf 0 0).headBase
  have hweak : HasGelfandWeakTimeDerivativeOn T u du :=
    (hasWeakTimeDerivativeOn_zeroBoundaryTimeDerivative hopen hbounded hgraph hab
      hU hc hzero 0).hasGelfandWeakTimeDerivativeOn T hab
  have huAE := zeroBoundaryTimeDerivative_ae hopen hbounded hgraph hab hU hc hzero 0
  have hvAE := zeroBoundaryTimeDerivative_ae hopen hbounded hgraph hab hU hc hzero 1
  apply hweak.integrated_solution_of_ae_equation hab (MB := ‖P.form hopen hbounded‖)
    (wkpBaseCoordinateCLM.continuous.comp_continuousOn
      (continuousOn_sobolevCurve hopen hbounded hab hU 1 0))
  · filter_upwards [huAE] with t ht
    change _ = baseCoordCLM (u t)
    rw [ht]
    rfl
  · exact fun _ ↦ aestronglyMeasurable_const
  · exact Eventually.of_forall fun _ ↦ le_rfl
  · have heqAE : ∀ᵐ t ∂volume.restrict (Ioo a b),
        du t + P.form hopen hbounded (u t) = ell t := by
      filter_upwards [(T.energyToDual.coeFn_compLpL v).filter_mono
          (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)),
        huAE.filter_mono (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)),
        hvAE.filter_mono (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)),
        (T.pivotToDual.coeFn_compLpL
          (forcingJet hopen hbounded hab hf 0 0).headBase).filter_mono
            (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)),
        (forcingJet hopen hbounded hab hf 0 0).headBase_ae.filter_mono
          (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)),
        (sobolevTimeDerivative_ae hopen hbounded hab hf 0 0).filter_mono
          (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)),
        ae_restrict_mem measurableSet_Ioo] with t hd hu₀ hv₀ hell hf₀ hf₁ ht
      have hclass := sobolev_equation_of_pointwise P hopen hbounded hab hf hU hc heq t ht
      have hbase : wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU 2 0 t) =
          baseCoordCLM (u t) := by
        rw [hu₀]
        change wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU 2 0 t) =
          wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU 1 0 t)
        rw [wkpBaseCoordinate_sobolevCurve hopen hbounded hab hU 2 0
          (Ioo_subset_Icc_self ht), wkpBaseCoordinate_sobolevCurve hopen hbounded hab hU 1 0
          (Ioo_subset_Icc_self ht)]
      have hform : P.form hopen hbounded (u t) = T.pivotToDual (wkpBaseCoordinateCLM
          (P.load hopen hbounded 0 (sobolevCurve hopen hbounded hab hU 2 0 t))) := by
        ext z
        exact P.form_eq_load hopen hbounded 0 _ (u t) z hbase
      rw [hd, hv₀, hform, hell, hf₀, head_forcingJet, hf₁]
      change T.pivotToDual (wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU 1 1 t)) +
        T.pivotToDual _ = T.pivotToDual _
      rw [← map_add, hclass]
    rwa [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at heqAE

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.Smooth
