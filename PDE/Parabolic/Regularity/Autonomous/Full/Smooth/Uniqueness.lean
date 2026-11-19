/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Full.Smooth.Solution
public import PDE.Parabolic.Regularity.Autonomous.Full.Smooth.Equation.Weak
public import PDE.Analysis.Evolution.Classical.Uniqueness
import PDE.Analysis.Evolution.Integrated.PivotPerturbation
import PDE.Analysis.Evolution.Integrated.Uniqueness

/-!
# Classical uniqueness through the original weak equation

Every classical solution gives an `H¹₀` weak trajectory with its pointwise
initial datum. Gårding uniqueness identifies this trajectory with every original
weak solution. Continuity then identifies the scalar function on the whole
closed cylinder, including both time endpoints.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.Smooth

open Filter MeasureTheory Set PDE.Common PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.GraphSpace.BoundaryRegularity
open SobolevSpace.Evolution.Classical HigherOrder

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {a b : ℝ}
  {P : SmoothFullCoefficients n Ω} {f U V : SpaceTime n → ℝ} {g : ℝ^n → ℝ}

local notation "Q" => splitSpaceTime ⁻¹' Set.prod Ω (Ioo a b)
local notation "K" => splitSpaceTime ⁻¹' Set.prod (closure Ω) (Icc a b)

/-- The pointwise classical initial value gives the initial class of the
integrated weak problem. -/
theorem IsClassicalSolution.isWeakSolution (hU : IsClassicalSolution P f g a b U)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (hg : ContDiffUpToBoundary 0 g Ω) :
    IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
      (fun _ ↦ P.form hopen hbounded)
      ((h10L2GelfandTriple hopen).pivotToDual.compLpL 2 (volume.restrict (Ioc a b))
        (forcingJet hopen hbounded hab hf 0 0).headBase)
      (zeroBoundaryTimeDerivative hopen hbounded hgraph hab
        hU.smooth hU.continuous hU.lateral 0)
      (hg.toLp hopen hbounded 2) := by
  have hinit : wkpBaseCoordinateCLM
      (sobolevCurve hopen hbounded hab hU.smooth 1 0 a) =
        hg.toLp hopen hbounded 2 := by
    apply wkpBaseCoordinate_sobolevCurve_zero_eq hopen hbounded hab
      hU.smooth hU.continuous 1 ⟨le_rfl, hab.le⟩
    filter_upwards [ae_restrict_mem hopen.measurableSet, hg.toLp_coeFn hopen hbounded 2]
      with x hx hgx
    exact (hU.initial x (subset_closure hx)).trans hgx.symm
  simpa only [hinit] using isWeakSolution_of_pointwise P hopen hbounded hgraph hab
    hf hU.smooth hU.continuous hU.lateral hU.equation

/-- A classical solution represents every original weak solution with the same
data. The hypotheses require no weak trajectory of the classical solution. -/
theorem IsClassicalSolution.represents_weakSolution
    (hU : IsClassicalSolution P f g a b U)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) (hab : a < b)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (hg : ContDiffUpToBoundary 0 g Ω)
    (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
    (hu : IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
      (fun _ ↦ P.form hopen hbounded)
      ((h10L2GelfandTriple hopen).pivotToDual.compLpL 2 (volume.restrict (Ioc a b))
        (forcingJet hopen hbounded hab hf 0 0).headBase)
      u (hg.toLp hopen hbounded 2)) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      (fun x ↦ U (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω]
        baseRepresentative (h10SubtypeL (u t)) := by
  obtain ⟨A, R, C, hC, hform, hcoercive⟩ :=
    P.exists_coercive_decomposition hopen hbounded halpha hell
  have hGarding := garding_bound_of_coercive_principal
    (h10L2GelfandTriple hopen) A R hC hcoercive
  have hstate : zeroBoundaryTimeDerivative hopen hbounded hgraph hab
      hU.smooth hU.continuous hU.lateral 0 = u := by
    apply IsGelfandIntegratedWeakSolution.unique_of_garding (gamma := ‖R‖ ^ 2 / (2 * C))
      (fun _ ↦ aestronglyMeasurable_const) ‖P.form hopen hbounded‖
      (Eventually.of_forall fun _ ↦ le_rfl) (half_pos hC).le
      (fun _ _ v ↦ ?_) (hU.isWeakSolution hopen hbounded hgraph hab hf hg) hu hab
    rw [hform]
    exact hGarding v
  have hae := zeroBoundaryTimeDerivative_represents hopen hbounded hgraph hab
    hU.smooth hU.continuous hU.lateral
  rwa [hstate] at hae

/-- Any two smooth classical solutions of the same signed full problem agree
at every point of the closed cylinder. -/
theorem IsClassicalSolution.eqOn (hU : IsClassicalSolution P f g a b U)
    (hV : IsClassicalSolution P f g a b V)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) (hab : a < b)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (hg : ContDiffUpToBoundary 0 g Ω) :
    EqOn U V K := by
  have hUV := hU.represents_weakSolution hopen hbounded hgraph hab halpha hell hf hg
    _ (hV.isWeakSolution hopen hbounded hgraph hab hf hg)
  have hVrep := zeroBoundaryTimeDerivative_represents hopen hbounded hgraph hab
    hV.smooth hV.continuous hV.lateral
  apply eqOn_closed_spaceTime_cylinder_of_ae_eq hopen hab hU.continuous hV.continuous
  filter_upwards [hUV, hVrep] with t ht hVt
  exact ht.trans hVt.symm

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.Smooth
