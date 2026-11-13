/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Full.Smooth.Compatibility.Identification
public import PDE.Parabolic.Regularity.Autonomous.Full.Smooth.Estimates
public import PDE.Parabolic.Regularity.Autonomous.Full.Smooth.Uniqueness
public import PDE.Spaces.Sobolev.Evolution.Classical.Boundary

/-!
# Smooth parabolic solutions from compatible data

Smooth forcing and initial data satisfying every recursively derived zero-boundary
compatibility condition give one smooth classical solution on the entire closed cylinder,
for the full signed autonomous operator. This is Evans's §7.1.3, Theorem 7 (Infinite
differentiability). The solution represents every original weak solution and is unique
among classical solutions. The main result is
`exists_unique_classical_solution_with_bounds`.

The constants in the finite derivative norm sums are chosen before all data.
All derivative classes in those sums come from the one scalar
solution. Boundary derivatives and compatibility values mean the unique
continuous extensions of the interior derivatives; no ambient smooth extension
is assumed.

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
open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.GraphSpace.BoundaryRegularity
open SobolevSpace.Evolution.Classical HigherOrder

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {a b : ℝ}

local notation "Q" => splitSpaceTime ⁻¹' Set.prod Ω (Ioo a b)
local notation "K" => splitSpaceTime ⁻¹' Set.prod (closure Ω) (Icc a b)

private theorem exists_weak_solution (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b))) (g : DerivLp n 2 Ω) :
    ∃ u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)),
      IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
        (fun _ ↦ P.form hopen hbounded)
        ((h10L2GelfandTriple hopen).pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f)
        u g := by
  obtain ⟨A, R, c, hc, hform, hcoercive⟩ :=
    P.exists_coercive_decomposition hopen hbounded halpha hell
  obtain ⟨C, hC, hexists⟩ :=
    exists_full_form_solution_with_bound hopen hbounded A R hc hab hcoercive
  obtain ⟨W, hW⟩ := hexists f g
  refine ⟨W.state, ?_⟩
  have h := W.properties.solution
  simpa only [← hform] using h

/-- Every original weak solution for compatible smooth data has a smooth
classical representative, which attains the initial and lateral values
pointwise. -/
theorem exists_classical_representative (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : ∀ r : ℕ, Boundary.HasContDiffGraphBoundary r Ω) (hab : a < b)
    (hsymm : ∀ x ∈ Ω, ∀ i j, P.principal x i j = P.principal x j i)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (f : SpaceTime n → ℝ) (hf : ∀ k, ContDiffUpToBoundary k f Q)
    (g : ℝ^n → ℝ) (hg : ∀ r, ContDiffUpToBoundary r g Ω)
    (hgc : ContinuousOn g (closure Ω))
    (hcompat : ∀ j x, x ∈ frontier Ω →
      initialBoundaryValue P hopen hbounded
        (initialForcingValue_regular hopen hbounded hab hf) hg j x = 0)
    (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
    (hu : IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
      (fun _ ↦ P.form hopen hbounded)
      ((h10L2GelfandTriple hopen).pivotToDual.compLpL 2 (volume.restrict (Ioc a b))
        (forcingJet hopen hbounded hab hf 0 0).headBase)
      u ((hg 0).toLp hopen hbounded 2)) :
    ∃ U : SpaceTime n → ℝ, IsClassicalSolution P f g a b U ∧
      (∀ᵐ t ∂volume.restrict (Ioo a b),
        (fun x ↦ U (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω]
          baseRepresentative (h10SubtypeL (u t))) := by
  obtain ⟨U, hc, hU, hae, _⟩ := exists_joint_smooth_representative P hopen hbounded
    hgraph hab hsymm halpha hell f hf g hg hcompat u hu
  refine ⟨U, ⟨hc, hU, ?_, ?_, ?_⟩, hae⟩
  · exact pointwise_equation P hopen hbounded hab hf hU hc u hae hu
  · exact pointwise_initial_value P hopen hbounded hab hf hU hc u hae (hg 0) hgc hu
  · exact eq_zero_on_lateral_boundary hopen hbounded
      ((hgraph 1).hasC1GraphBoundary le_rfl) hab u hc hae

/-- Existence and uniqueness on the closed cylinder, with every finite
derivative norm sum bounded and every original weak solution identified.
The positive constants depend only on the order, domain, time interval and
coefficients, and are chosen before the forcing and initial data.

Compatibility uses only the recursively derived initial values, built from the
traces of the forcing derivatives. The hypotheses concern `f` and `g` alone:
no solution trajectory, derivative family or approximation is assumed. -/
theorem exists_unique_classical_solution_with_bounds (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : ∀ r : ℕ, Boundary.HasContDiffGraphBoundary r Ω) (hab : a < b)
    (hsymm : ∀ x ∈ Ω, ∀ i j, P.principal x i j = P.principal x j i)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (f : SpaceTime n → ℝ) (hf : ∀ k, ContDiffUpToBoundary k f Q)
        (g : ℝ^n → ℝ) (hg : ∀ r, ContDiffUpToBoundary r g Ω),
      ContinuousOn g (closure Ω) →
      (∀ j x, x ∈ frontier Ω →
        initialBoundaryValue P hopen hbounded
          (initialForcingValue_regular hopen hbounded hab hf) hg j x = 0) →
      ∃ (U : SpaceTime n → ℝ) (hU : IsClassicalSolution P f g a b U),
        (∀ m : ℕ,
          (forcingJet hopen hbounded hab hU.smooth (m + 1) 0).normSum ≤ C m *
            (‖(hg (2 * m + 1)).toWkpSpaceOn hopen hbounded 2‖ +
              (forcingJet hopen hbounded hab hf m 0).normSum)) ∧
        (∀ j : ℕ, EqOn (derivativeSlice hopen hU.smooth (List.replicate j 0) a)
          (initialBoundaryValue P hopen hbounded
            (initialForcingValue_regular hopen hbounded hab hf) hg j) (closure Ω)) ∧
        (ContinuousOn f K → ∀ t ∈ Icc a b, ∀ x ∈ Ω,
          derivativeSlice hopen hU.smooth [0] t x +
              P.classicalLoad (fun y ↦ U (timeSpaceCons t y)) x =
            f (timeSpaceCons t x)) ∧
        (∀ V : SpaceTime n → ℝ, IsClassicalSolution P f g a b V → EqOn V U K) ∧
        ∀ u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)),
          IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
            (fun _ ↦ P.form hopen hbounded)
            ((h10L2GelfandTriple hopen).pivotToDual.compLpL 2 (volume.restrict (Ioc a b))
              (forcingJet hopen hbounded hab hf 0 0).headBase)
            u ((hg 0).toLp hopen hbounded 2) →
          (∀ᵐ t ∂volume.restrict (Ioo a b),
            (fun x ↦ U (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω]
              baseRepresentative (h10SubtypeL (u t))) := by
  choose C hC hbound using
    fun m ↦ exists_derivative_normSum_bound P hopen hbounded hgraph hab hsymm halpha hell m
  refine ⟨C, hC, ?_⟩
  intro f hf g hg hgc hcompat
  obtain ⟨u, hu⟩ := exists_weak_solution P hopen hbounded hab halpha hell
    (forcingJet hopen hbounded hab hf 0 0).headBase
    ((hg 0).toLp hopen hbounded 2)
  obtain ⟨U, hU, hae⟩ := exists_classical_representative P hopen hbounded hgraph hab hsymm
    halpha hell f hf g hg hgc hcompat u hu
  refine ⟨U, hU, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    exact hbound m f hf g hg hcompat u U hU.smooth hU.continuous hae hu
  · exact initial_derivative_value_all_orders P hopen hbounded hab hf hg
      hU.smooth hU.continuous u hae hu
  · intro hfc
    exact pointwise_equation_closed_time P hopen hbounded hab hf hfc
      hU.smooth hU.continuous u hae hu
  · intro V hV
    exact hV.eqOn hU hopen hbounded ((hgraph 1).hasC1GraphBoundary le_rfl)
      hab halpha hell hf (hg 0)
  · intro u hu
    exact hU.represents_weakSolution hopen hbounded ((hgraph 1).hasC1GraphBoundary le_rfl)
      hab halpha hell hf (hg 0) u hu

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.Smooth
