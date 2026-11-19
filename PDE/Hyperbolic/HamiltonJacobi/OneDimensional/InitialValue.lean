/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.Viscosity
public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.InitialValue
public import PDE.Common.Euclidean.SpaceTime.Scalar

/-!
# Evans viscosity initial-value problems for one-dimensional Hamilton–Jacobi equations

We formalize the viscosity initial-value problem of Evans, §10.1.1, for

`u_t + H(u_x, x) = 0`, `u(0, x) = g(x)`.

The Hamiltonian may depend on the spatial point. The predicates encode the two analytic
conditions in Evans's definition: boundedness and uniform continuity on every finite
closed time slab, and the initial trace at `t = 0`. They use the domain-relative
viscosity inequalities of `OneDimensional.Viscosity`. Slab regularity uses the general
Hamilton–Jacobi definition after the change from `(t, x)` to `(x, t)` coordinates.
Evans tests with smooth functions; the differentiable-test inequalities admit more tests.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.1.1, definition of viscosity solution.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HamiltonJacobi1D

noncomputable section

open PDE.Common

open scoped Topology

/-- The closed forward spacetime slab `0 ≤ t ≤ T`. -/
def closedTimeSlab (T : ℝ) : Set ℝ^2 :=
  scalarSpaceTimeEquiv ⁻¹' HamiltonJacobi.closedTimeSlab T

/-- A viscosity subsolution of `u_t + H(u_x, x) = 0` satisfying the upper
initial condition `u(0, x) ≤ g(x)`. -/
def IsDifferentiableTestInitialSubsolution
    (H : ℝ → ℝ → ℝ) (g : ℝ → ℝ) (u : ℝ^2 → ℝ) : Prop :=
  HamiltonJacobi.IsBoundedUniformContinuousOnSlabs (u ∘ scalarSpaceTimeEquiv.symm) ∧
    IsSpatialDifferentiableTestSubsolution H positiveTimeDomain u ∧
      ∀ x, u !₂[0, x] ≤ g x

/-- A viscosity supersolution of `u_t + H(u_x, x) = 0` satisfying the lower
initial condition `g(x) ≤ u(0, x)`. -/
def IsDifferentiableTestInitialSupersolution
    (H : ℝ → ℝ → ℝ) (g : ℝ → ℝ) (u : ℝ^2 → ℝ) : Prop :=
  HamiltonJacobi.IsBoundedUniformContinuousOnSlabs (u ∘ scalarSpaceTimeEquiv.symm) ∧
    IsSpatialDifferentiableTestSupersolution H positiveTimeDomain u ∧
      ∀ x, g x ≤ u !₂[0, x]

/-- The bounded, uniformly continuous touching-test solution class for the
initial-value problem.

The candidate is bounded and uniformly continuous on every slab
`[0, T] × ℝ`, satisfies the viscosity equation on `t > 0`, and agrees
pointwise with the initial datum at `t = 0`. Tests need only be differentiable at contact. -/
def IsDifferentiableTestInitialSolution
    (H : ℝ → ℝ → ℝ) (g : ℝ → ℝ) (u : ℝ^2 → ℝ) : Prop :=
  HamiltonJacobi.IsBoundedUniformContinuousOnSlabs (u ∘ scalarSpaceTimeEquiv.symm) ∧
    IsSpatialDifferentiableTestSolution H positiveTimeDomain u ∧
      ∀ x, u !₂[0, x] = g x

/-- A viscosity solution of the initial-value problem is, in particular, a
subsolution with the corresponding upper initial trace. -/
theorem IsDifferentiableTestInitialSolution.subsolution {H : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {u : ℝ^2 → ℝ}
    (hu : IsDifferentiableTestInitialSolution H g u) :
    IsDifferentiableTestInitialSubsolution H g u :=
  ⟨hu.1, hu.2.1.1, fun x ↦ (hu.2.2 x).le⟩

/-- A viscosity solution of the initial-value problem is, in particular, a
supersolution with the corresponding lower initial trace. -/
theorem IsDifferentiableTestInitialSolution.supersolution {H : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {u : ℝ^2 → ℝ}
    (hu : IsDifferentiableTestInitialSolution H g u) :
    IsDifferentiableTestInitialSupersolution H g u :=
  ⟨hu.1, hu.2.1.2, fun x ↦ (hu.2.2 x).ge⟩

/-- A viscosity solution of the initial-value problem attains its prescribed
initial datum pointwise. -/
theorem IsDifferentiableTestInitialSolution.initial_eq {H : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {u : ℝ^2 → ℝ}
    (hu : IsDifferentiableTestInitialSolution H g u) (x : ℝ) :
    u !₂[0, x] = g x :=
  hu.2.2 x

/-- The full IVP solution notion is exactly the conjunction of its
comparison-compatible subsolution and supersolution notions. -/
theorem isDifferentiableTestInitialSolution_iff_sub_and_super
    {H : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {u : ℝ^2 → ℝ} :
    IsDifferentiableTestInitialSolution H g u ↔ IsDifferentiableTestInitialSubsolution H g u ∧
      IsDifferentiableTestInitialSupersolution H g u := by
  constructor
  · exact fun hu ↦ ⟨hu.subsolution, hu.supersolution⟩
  · rintro ⟨⟨hBUC, hsub, hsubtrace⟩, ⟨_hBUC', hsuper, hsupertrace⟩⟩
    exact ⟨hBUC, ⟨hsub, hsuper⟩, fun x ↦ le_antisymm (hsubtrace x) (hsupertrace x)⟩

/-- A classical solution with the stated slab regularity and initial trace
is a viscosity solution of the complete initial-value problem. -/
theorem isDifferentiableTestInitialSolution_of_classical {H : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {u : ℝ^2 → ℝ}
    (hBUC : HamiltonJacobi.IsBoundedUniformContinuousOnSlabs (u ∘ scalarSpaceTimeEquiv.symm))
    (hu : ∀ z ∈ positiveTimeDomain, DifferentiableAt ℝ u z)
    (hpde : ∀ z ∈ positiveTimeDomain, (∂[(0 : Fin 2)] u) z + H ((∂[(1 : Fin 2)] u) z) (z 1) = 0)
    (htrace : ∀ x, u !₂[0, x] = g x) :
    IsDifferentiableTestInitialSolution H g u :=
  ⟨hBUC, isSpatialDifferentiableTestSolution_of_classical isOpen_positiveTimeDomain hu hpde, htrace⟩

/-- Constant data satisfy every differentiable touching test whenever
`H(0, x) = 0`. -/
theorem constant_isDifferentiableTestInitialSolution (H : ℝ → ℝ → ℝ) (c : ℝ) (hH : ∀ x, H 0 x = 0) :
    IsDifferentiableTestInitialSolution H (fun _ ↦ c) (fun _ : ℝ^2 ↦ c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    constructor
    · apply Set.Finite.isBounded
      exact (Set.finite_singleton c).subset fun y hy ↦ by
        rcases hy with ⟨z, _hz, rfl⟩
        simp
    · exact uniformContinuous_const.uniformContinuousOn
  · apply isSpatialDifferentiableTestSolution_of_classical isOpen_positiveTimeDomain
    · exact fun z hz ↦ differentiableAt_const c
    · intro z hz
      simp [PDE.partialDeriv_const, hH]
  · intro x
    rfl

end

end HamiltonJacobi1D
