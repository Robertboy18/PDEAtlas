/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.GreenPotential
public import PDE.Fluid.Boussinesq.VorticityStream.Symmetry
import PDE.FDeriv.Calculus
import PDE.FDeriv.Reflection.Coordinate

/-!
# Symmetry transfer for the half-plane Dirichlet Poisson problem

The streamfunction of the Chen–Hou upper-half-plane model inherits the parity of its source in
two ways. If the source is odd under reflection in the vertical axis, reflected negation sends
a Dirichlet Poisson solution to another solution with the same source, so uniqueness in a
specified admissible class forces the streamfunction to be odd
(`IsClassicalUpperHalfPlaneDirichletPoissonSolution.tangentiallyOdd_of_mem`).

The admissible class is explicit because unrestricted classical uniqueness is
false on the unbounded half-plane: one may add nondecaying harmonic functions
with zero boundary trace. Applications must supply the appropriate decay,
energy, or representation class and its uniqueness theorem.

The second route uses the method-of-images Green potential
`GreenFunction.halfSpaceGreenPotential`: it vanishes on the horizontal boundary, is odd for an
odd source with integrable kernel or with finite mass and logarithmic moment
(`halfSpaceGreenPotential_tangentiallyOdd`,
`halfSpaceGreenPotential_tangentiallyOdd_of_integrable_log_weight`), and for compactly supported
normally odd data is a classical Dirichlet Poisson solution
(`halfSpaceGreenPotential_isClassicalDirichletSolution_of_normalOdd`).

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 2, (2.3c), for the Dirichlet
  Poisson problem, and Section 2.1, (Sym), for the parity.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

open PDE (laplacian)

namespace Boussinesq

open SobolevSpace
open PDE.Common

set_option linter.missingDocs true

noncomputable section

/-- Negated pullback by reflection in the vertical axis. This is the
transformation preserving the Dirichlet Poisson equation for an odd source. -/
def tangentialReflectedNegation (f : ℝ^2 → ℝ) : ℝ^2 → ℝ :=
  fun x ↦ -f (tangentialReflection x)

/-- A classical solution of the upper-half-plane Dirichlet Poisson problem
`-Δφ = source` with zero horizontal boundary trace. -/
def IsClassicalUpperHalfPlaneDirichletPoissonSolution
    (source streamFunction : ℝ^2 → ℝ) : Prop :=
  ContDiff ℝ 2 streamFunction ∧
    (∀ ⦃x : ℝ^2⦄, x ∈ upperHalfPlane →
      -laplacian streamFunction x = source x) ∧
    VanishesOnCoordinateHyperplane (1 : Fin 2) streamFunction

namespace IsClassicalUpperHalfPlaneDirichletPoissonSolution

/-- Extract the spatial regularity of a classical Dirichlet Poisson solution. -/
theorem contDiff_two
    {source streamFunction : ℝ^2 → ℝ}
    (h : IsClassicalUpperHalfPlaneDirichletPoissonSolution
      source streamFunction) :
    ContDiff ℝ 2 streamFunction :=
  h.1

/-- Extract the Poisson equation in the open upper half-plane. -/
theorem poisson_equation
    {source streamFunction : ℝ^2 → ℝ}
    (h : IsClassicalUpperHalfPlaneDirichletPoissonSolution
      source streamFunction)
    {x : ℝ^2} (hx : x ∈ upperHalfPlane) :
    -laplacian streamFunction x = source x :=
  h.2.1 hx

/-- Extract the zero horizontal boundary trace. -/
theorem zero_boundary
    {source streamFunction : ℝ^2 → ℝ}
    (h : IsClassicalUpperHalfPlaneDirichletPoissonSolution
      source streamFunction) :
    VanishesOnCoordinateHyperplane (1 : Fin 2) streamFunction :=
  h.2.2

end IsClassicalUpperHalfPlaneDirichletPoissonSolution

/-- Reflected negation preserves classical Dirichlet Poisson solutions when
the source is tangentially odd. -/
theorem IsClassicalUpperHalfPlaneDirichletPoissonSolution.reflectedNegation
    {source streamFunction : ℝ^2 → ℝ}
    (hsolution :
      IsClassicalUpperHalfPlaneDirichletPoissonSolution source streamFunction)
    (hsource : IsOddUnderCoordinateReflection (0 : Fin 2) source) :
    IsClassicalUpperHalfPlaneDirichletPoissonSolution source
      (tangentialReflectedNegation streamFunction) := by
  refine ⟨?_, ?_, ?_⟩
  · have hreflection : ContDiff ℝ 2 tangentialReflection := by
      change ContDiff ℝ 2 (PDE.Common.coordinateReflection (0 : Fin 2))
      exact PDE.Common.contDiff_coordinateReflection (0 : Fin 2) 2
    change ContDiff ℝ 2
      (fun x ↦ -streamFunction (tangentialReflection x))
    simpa [Function.comp_def] using
      (hsolution.contDiff_two.comp hreflection).neg
  · intro x hx
    have hequation := hsolution.poisson_equation
      (tangentialReflection_mem_upperHalfPlane_iff.mpr hx)
    have hodd : source (tangentialReflection x) = -source x := by
      simpa [tangentialReflection] using hsource x
    rw [show tangentialReflectedNegation streamFunction =
        -(fun y ↦ streamFunction (tangentialReflection y)) by rfl]
    rw [PDE.laplacian_neg]
    rw [show
      laplacian (fun y ↦ streamFunction (tangentialReflection y)) x =
        laplacian streamFunction (tangentialReflection x) by
      simpa [tangentialReflection] using
        PDE.Common.laplacian_comp_coordinateReflection
          (0 : Fin 2) streamFunction x hsolution.contDiff_two]
    linarith
  · intro x hx
    have hreflectedMem :
        tangentialReflection x ∈
          PDE.Common.coordinateHyperplane (1 : Fin 2) := by
      change PDE.Common.coordinateReflection (0 : Fin 2) x 1 = 0
      rw [PDE.Common.coordinateReflection_apply_of_ne]
      · exact hx
      · decide
    simp [tangentialReflectedNegation,
      hsolution.zero_boundary hreflectedMem]

/-- Uniqueness in a reflection-stable admissible class transfers odd source
parity to a classical upper-half-plane Dirichlet Poisson solution. -/
theorem IsClassicalUpperHalfPlaneDirichletPoissonSolution.tangentiallyOdd_of_mem
    {source streamFunction : ℝ^2 → ℝ}
    (hsolution :
      IsClassicalUpperHalfPlaneDirichletPoissonSolution source streamFunction)
    (hsource : IsOddUnderCoordinateReflection (0 : Fin 2) source)
    {admissible : Set (ℝ^2 → ℝ)}
    (hstreamAdmissible : streamFunction ∈ admissible)
    (hreflectedNegationMem : ∀ ⦃f : ℝ^2 → ℝ⦄, f ∈ admissible →
      tangentialReflectedNegation f ∈ admissible)
    (hunique : ∀ ⦃f g : ℝ^2 → ℝ⦄,
      f ∈ admissible → g ∈ admissible →
      IsClassicalUpperHalfPlaneDirichletPoissonSolution source f →
      IsClassicalUpperHalfPlaneDirichletPoissonSolution source g →
      f = g) :
    IsOddUnderCoordinateReflection (0 : Fin 2) streamFunction := by
  have hreflectedEq :
      tangentialReflectedNegation streamFunction = streamFunction :=
    hunique
      (hreflectedNegationMem hstreamAdmissible)
      hstreamAdmissible
      (hsolution.reflectedNegation hsource)
      hsolution
  intro x
  have hx := congrFun hreflectedEq x
  change -streamFunction (tangentialReflection x) = streamFunction x at hx
  change streamFunction (tangentialReflection x) = -streamFunction x
  linarith

/-- The half-space Green potential of a tangentially odd source with an
integrable Green kernel is tangentially odd.

This is a concrete alternative to the abstract uniqueness argument
`IsClassicalUpperHalfPlaneDirichletPoissonSolution.tangentiallyOdd_of_mem` when the
streamfunction is defined by the method-of-images integral. -/
theorem halfSpaceGreenPotential_tangentiallyOdd
    (source : ℝ^2 → ℝ)
    (hsource : IsOddUnderCoordinateReflection (0 : Fin 2) source)
    (hintegrable : GreenFunction.HasIntegrableHalfSpaceGreenPotential source) :
    IsOddUnderCoordinateReflection (0 : Fin 2)
      (GreenFunction.halfSpaceGreenPotential source) := by
  have hi : (0 : Fin 2) ≠ PDE.Common.lastIndex (n := 2) := by
    norm_num [PDE.Common.lastIndex]
  intro x
  have hparity :=
    GreenFunction.halfSpaceGreenPotential_coordinateReflection_of_odd
      (n := 2) hi source x
      (fun y _hy ↦ hsource y)
      (hintegrable x)
  simpa [tangentialReflection] using hparity.2

/-- A continuous source with both tangential oddness and normal
odd-extension parity produces a tangentially odd Green potential whenever it
has finite absolute mass and finite logarithmic moment.

The theorem permits noncompact support subject to these integrability assumptions. -/
theorem halfSpaceGreenPotential_tangentiallyOdd_of_integrable_log_weight
    (source : ℝ^2 → ℝ)
    (htangentialOdd : IsOddUnderCoordinateReflection (0 : Fin 2) source)
    (hnormalOdd : ∀ y : ℝ^2,
      source (HalfSpace.reflect 2 y) = -source y)
    (hcontinuous : Continuous source)
    (hintegrable : MeasureTheory.Integrable source)
    (hlogIntegrable : MeasureTheory.Integrable
      (fun y : ℝ^2 ↦ Real.log (1 + ‖y‖) * source y)) :
    IsOddUnderCoordinateReflection (0 : Fin 2)
      (GreenFunction.halfSpaceGreenPotential source) :=
  halfSpaceGreenPotential_tangentiallyOdd source htangentialOdd
    (GreenFunction.hasIntegrableHalfSpaceGreenPotential_of_odd_of_integrable_log_weight
      source hnormalOdd hcontinuous hintegrable hlogIntegrable)

/-- A compactly supported planar source represented by an odd extension
across the horizontal boundary has a `C²` half-space Green potential. -/
theorem contDiff_two_halfSpaceGreenPotential_of_normalOdd
    (source : TestFunction
      (⊤ : TopologicalSpace.Opens (ℝ^2)) ℝ 2)
    (hnormalOdd : ∀ y : ℝ^2,
      source (HalfSpace.reflect 2 y) = -source y) :
    ContDiff ℝ 2 (GreenFunction.halfSpaceGreenPotential source) := by
  have hpotential : GreenFunction.halfSpaceGreenPotential source =
      PoissonEquation.fundamentalSolutionConvolution 2 source := by
    funext x
    exact
      GreenFunction.halfSpaceGreenPotential_eq_fundamentalSolutionConvolution_of_odd
        source hnormalOdd x
  rw [hpotential]
  exact PoissonEquation.contDiff_two_fundamentalSolutionConvolution 2 source

/-- Under the same odd-extension hypothesis, the half-space Green potential
solves the streamfunction equation `-Δφ = ω` throughout the upper
half-plane. -/
theorem halfSpaceGreenPotential_satisfiesPoissonEquation_of_normalOdd
    (source : TestFunction
      (⊤ : TopologicalSpace.Opens (ℝ^2)) ℝ 2)
    (hnormalOdd : ∀ y : ℝ^2,
      source (HalfSpace.reflect 2 y) = -source y) :
    ∀ ⦃x : ℝ^2⦄, x ∈ upperHalfPlane →
      -laplacian (GreenFunction.halfSpaceGreenPotential source) x = source x := by
  intro x _hx
  exact GreenFunction.negative_laplacian_halfSpaceGreenPotential_of_odd
    source hnormalOdd x

/-- Compactly supported data with both the normal odd extension and the
Chen–Hou tangential parity produce a classical odd Dirichlet Poisson
streamfunction. -/
theorem halfSpaceGreenPotential_tangentiallyOdd_of_testFunction
    (source : TestFunction
      (⊤ : TopologicalSpace.Opens (ℝ^2)) ℝ 2)
    (htangentialOdd : IsOddUnderCoordinateReflection (0 : Fin 2) source)
    (hnormalOdd : ∀ y : ℝ^2,
      source (HalfSpace.reflect 2 y) = -source y) :
    IsOddUnderCoordinateReflection (0 : Fin 2)
      (GreenFunction.halfSpaceGreenPotential source) :=
  halfSpaceGreenPotential_tangentiallyOdd source htangentialOdd
    (GreenFunction.hasIntegrableHalfSpaceGreenPotential_of_odd
      source hnormalOdd)

/-- Every half-space Green potential has the zero horizontal boundary trace
required by the Boussinesq streamfunction formulation. -/
theorem halfSpaceGreenPotential_vanishesOnHorizontalBoundary
    (source : ℝ^2 → ℝ) :
    VanishesOnCoordinateHyperplane (1 : Fin 2)
      (GreenFunction.halfSpaceGreenPotential source) := by
  intro x hx
  exact GreenFunction.halfSpaceGreenPotential_boundary source
    (by
      simpa [PDE.Common.coordinateHyperplane, HalfSpace.boundary,
        PDE.Common.lastIndex] using hx)

/-- The Green potential of compactly supported normally odd data is a
classical upper-half-plane Dirichlet Poisson solution. -/
theorem halfSpaceGreenPotential_isClassicalDirichletSolution_of_normalOdd
    (source : TestFunction
      (⊤ : TopologicalSpace.Opens (ℝ^2)) ℝ 2)
    (hnormalOdd : ∀ y : ℝ^2,
      source (HalfSpace.reflect 2 y) = -source y) :
    IsClassicalUpperHalfPlaneDirichletPoissonSolution source
      (GreenFunction.halfSpaceGreenPotential source) := by
  exact ⟨
    contDiff_two_halfSpaceGreenPotential_of_normalOdd source hnormalOdd,
    halfSpaceGreenPotential_satisfiesPoissonEquation_of_normalOdd
      source hnormalOdd,
    halfSpaceGreenPotential_vanishesOnHorizontalBoundary source⟩

end

end Boussinesq
