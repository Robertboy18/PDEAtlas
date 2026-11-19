/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Full.Smooth.Compatibility.Sobolev
public import PDE.Parabolic.Regularity.Autonomous.Full.Smooth.FiniteRegularity
public import PDE.Parabolic.Regularity.Autonomous.Full.HigherOrder.AllOrders

/-!
# Smooth parabolic regularity from compatible data

The forcing derivatives and initial compatibility values are computed from
the smooth data `f` and `g`. Pointwise zero boundary values imply the Sobolev
compatibility conditions `Compatible` at every order. The finite estimates apply to
the same original weak solution, and identify one smooth representative on the
closed cylinder.

This is the regularity step of Evans's §7.1.3, Theorem 7, whose proof applies
Theorem 6 for every `m`. The classical equation and initial and boundary values are
proved in `PDE.Parabolic.Regularity.Autonomous.Full.Smooth.Existence`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.3, Theorem 6 (Higher regularity), p. 386, and Theorem 7
  (Infinite differentiability) and its proof, p. 388.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.Smooth

open Filter MeasureTheory Set PDE.Common PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.GraphSpace.BoundaryRegularity HigherOrder

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {a b : ℝ}

local notation "Q" => splitSpaceTime ⁻¹' Set.prod Ω (Ioo a b)

/-- Every finite estimate holds for the original weak solution. Its constant
depends only on the operator, domain, time interval and derivative order. -/
theorem exists_finite_regularity (P : SmoothFullCoefficients n Ω)
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
      ∀ u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)),
      IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
        (fun _ ↦ P.form hopen hbounded)
        ((h10L2GelfandTriple hopen).pivotToDual.compLpL 2 (volume.restrict (Ioc a b))
          (forcingJet hopen hbounded hab hf 0 0).headBase)
        u ((hg 0).toLp hopen hbounded 2) →
      ∃ U : ForcingJet n Ω a b (m + 1), U.HasWeakDerivatives ∧
        (∀ᵐ t ∂volume.restrict (Ioc a b),
          wkpBaseCoordinateCLM (U.head t) = baseCoordCLM (u t)) ∧
        U.normSum ≤ C *
          (‖(hg (2 * m + 1)).toWkpSpaceOn hopen hbounded 2‖ +
            (forcingJet hopen hbounded hab hf m 0).normSum) := by
  obtain ⟨C, hC, hreg⟩ :=
    exists_all_order_regularity P hopen hbounded hgraph hab hsymm halpha hell m
  refine ⟨C, hC, ?_⟩
  intro f hf g hg hzero u hu
  have hcompat := compatible_forcingJet_of_initial_zero P hopen hbounded (hgraph 2) hab hf hg
    (fun j ↦ initialSobolevValue_zeroBoundary_of_eq_zero P hopen hbounded
      ((hgraph 1).hasC1GraphBoundary le_rfl) _ hg 1 j (hzero j)) m 0
  apply hreg _ (forcingJet_hasWeakDerivatives hopen hbounded hab hf m 0) _ hcompat u
  simpa only [headBase_forcingJet, base_initialSobolevValue_zero] using hu

/-- Smooth forcing and recursively derived zero boundary compatibility
construct a unique smooth closure representative of every original weak solution. -/
theorem exists_joint_smooth_representative (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : ∀ r : ℕ, Boundary.HasContDiffGraphBoundary r Ω) (hab : a < b)
    (hsymm : ∀ x ∈ Ω, ∀ i j, P.principal x i j = P.principal x j i)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (f : SpaceTime n → ℝ) (hf : ∀ k, ContDiffUpToBoundary k f Q)
    (g : ℝ^n → ℝ) (hg : ∀ r, ContDiffUpToBoundary r g Ω)
    (hzero : ∀ j x, x ∈ frontier Ω →
      initialBoundaryValue P hopen hbounded
        (initialForcingValue_regular hopen hbounded hab hf) hg j x = 0)
    (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
    (hu : IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
      (fun _ ↦ P.form hopen hbounded)
      ((h10L2GelfandTriple hopen).pivotToDual.compLpL 2 (volume.restrict (Ioc a b))
        (forcingJet hopen hbounded hab hf 0 0).headBase)
      u ((hg 0).toLp hopen hbounded 2)) :
    ∃ U : SpaceTime n → ℝ,
      ContinuousOn U (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)) ∧
      (∀ k : ℕ, ContDiffUpToBoundary k U Q) ∧
      (∀ᵐ t ∂volume.restrict (Ioo a b),
        (fun x ↦ U (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω]
          baseRepresentative (h10SubtypeL (u t))) ∧
      ∀ V : SpaceTime n → ℝ,
        ContinuousOn V (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)) →
        (∀ᵐ t ∂volume.restrict (Ioo a b),
          (fun x ↦ V (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω]
            baseRepresentative (h10SubtypeL (u t))) →
        EqOn V U (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)) := by
  apply exists_joint_smooth_representative_of_finite_regularity (Fact.out : 0 < n)
    hopen hbounded ((hgraph 1).hasC1GraphBoundary le_rfl) hab u
  intro m
  obtain ⟨_, _, hreg⟩ :=
    exists_finite_regularity P hopen hbounded hgraph hab hsymm halpha hell m
  obtain ⟨U, hU, hbase, _⟩ := hreg f hf g hg hzero u hu
  exact ⟨U, hU, hbase⟩

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.Smooth
