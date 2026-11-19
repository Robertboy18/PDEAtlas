/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Full.Smooth.Regularity
public import PDE.Parabolic.Regularity.Autonomous.Full.HigherOrder.Forcing.Uniqueness

/-!
# Finite estimates for the derivatives of the smooth solution

Weak derivative uniqueness identifies every finite tuple given by parabolic
regularity with the time derivatives of the smooth representative. The finite
norm sum therefore bounds those derivatives, with the same constant, fixed
before the initial data, forcing and solution.
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

/-- A finite regularity tuple of the original solution consists of the time
derivatives of any smooth closure representative of that solution. -/
theorem forcingJet_eq_of_representative
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    {U : SpaceTime n → ℝ} (hU : ∀ k, ContDiffUpToBoundary k U Q)
    (hc : ContinuousOn U K) (u : ℝ → H¹₀(Ω))
    (hae : ∀ᵐ t ∂volume.restrict (Ioo a b),
      (fun x ↦ U (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω]
        baseRepresentative (h10SubtypeL (u t)))
    {m : ℕ} (F : ForcingJet n Ω a b m) (hF : F.HasWeakDerivatives)
    (hbase : ∀ᵐ t ∂volume.restrict (Ioc a b),
      wkpBaseCoordinateCLM (F.head t) = baseCoordCLM (u t)) :
    forcingJet hopen hbounded hab hU m 0 = F := by
  apply ForcingJet.eq_of_headBase_eq hopen
    (forcingJet_hasWeakDerivatives hopen hbounded hab hU m 0) hF
  apply Lp.ext
  have hae' : ∀ᵐ t ∂volume.restrict (Ioc a b),
      (fun x ↦ U (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω]
        baseRepresentative (h10SubtypeL (u t)) := by
    rwa [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at hae
  filter_upwards [(forcingJet hopen hbounded hab hU m 0).headBase_ae,
    F.headBase_ae, sobolevTimeDerivative_ae hopen hbounded hab hU (2 * m) 0,
    hbase, hae', ae_restrict_mem measurableSet_Ioc] with t hclass hFclass hcurve ht hrep htm
  rw [hclass, head_forcingJet, hcurve, hFclass, ht]
  exact wkpBaseCoordinate_sobolevCurve_zero_eq hopen hbounded hab hU hc (2 * m)
    (Ioc_subset_Icc_self htm) hrep

/-- The full sum of the Sobolev norms of the smooth solution's time derivatives
has the finite parabolic bound at every order, including order zero. -/
theorem exists_derivative_normSum_bound [Fact (0 < n)] (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : ∀ r : ℕ, Boundary.HasContDiffGraphBoundary r Ω) (hab : a < b)
    (hsymm : ∀ x ∈ Ω, ∀ i j, P.principal x i j = P.principal x j i)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : SpaceTime n → ℝ) (hf : ∀ k, ContDiffUpToBoundary k f Q)
        (g : ℝ^n → ℝ) (hg : ∀ r, ContDiffUpToBoundary r g Ω),
      (∀ j x, x ∈ frontier Ω →
        initialBoundaryValue P hopen hbounded
          (initialForcingValue_regular hopen hbounded hab hf) hg j x = 0) →
      ∀ (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
        (U : SpaceTime n → ℝ) (hU : ∀ k, ContDiffUpToBoundary k U Q),
      ContinuousOn U K →
      (∀ᵐ t ∂volume.restrict (Ioo a b),
        (fun x ↦ U (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω]
          baseRepresentative (h10SubtypeL (u t))) →
      IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
        (fun _ ↦ P.form hopen hbounded)
        ((h10L2GelfandTriple hopen).pivotToDual.compLpL 2 (volume.restrict (Ioc a b))
          (forcingJet hopen hbounded hab hf 0 0).headBase)
        u ((hg 0).toLp hopen hbounded 2) →
      (forcingJet hopen hbounded hab hU (m + 1) 0).normSum ≤ C *
        (‖(hg (2 * m + 1)).toWkpSpaceOn hopen hbounded 2‖ +
          (forcingJet hopen hbounded hab hf m 0).normSum) := by
  obtain ⟨C, hC, hreg⟩ :=
    exists_finite_regularity P hopen hbounded hgraph hab hsymm halpha hell m
  refine ⟨C, hC, ?_⟩
  intro f hf g hg hzero u U hU hc hae hu
  obtain ⟨F, hF, hbase, hnorm⟩ := hreg f hf g hg hzero u hu
  rwa [forcingJet_eq_of_representative hopen hbounded hab hU hc u hae F hF hbase]

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.Smooth
