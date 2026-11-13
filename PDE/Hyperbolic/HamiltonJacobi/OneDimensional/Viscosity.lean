/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.Characteristics
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Differentiable-test viscosity solutions of one-dimensional Hamilton–Jacobi equations

We define differentiable-test subsolution and supersolution predicates for the
1D Hamilton–Jacobi equation

`u_t + H(u_x) = 0`

on spacetime `ℝ^2` and prove the basic facts:

* the domain-relative predicates allow Hamiltonians `H(p, x)` and use test functions touching
  relative to an open PDE domain;
* auxiliary ambient-local predicates support proofs by classical differentiation;
* on an open domain, every ambient-local solution satisfies the domain-relative predicate.

The position-dependent predicates are named `IsSpatialDifferentiableTest*`.
`IsDifferentiableTestSolution` specializes the spatial solution predicate to `H(p, x) = H(p)`.
The `IsAmbientDifferentiableTest*` predicates use the ambient-local touching condition needed
by the Hopf–Lax proofs.

Test functions here need only be differentiable at the touching point.
The resulting inequalities apply to every `C¹` test. Theorems assuming these predicates therefore
use a stronger test hypothesis. Viscosity solutions are defined in Evans, §10.1.1, with smooth
test functions.

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

/-- Differentiable-test subsolution test-function inequality for `u_t + H(u_x) = 0` on a domain `U`.

This is the ambient-local inequality core: the test function must touch `u` from above in the
ambient spacetime topology, not merely relative to `U`. Continuity/upper-semicontinuity of `u` is
not included in this predicate. -/
def IsAmbientDifferentiableTestSubsolution
    (H : ℝ → ℝ) (U : Set ℝ^2) (u : ℝ^2 → ℝ) : Prop :=
  ∀ x ∈ U, ∀ φ : ℝ^2 → ℝ, DifferentiableAt ℝ φ x →
    IsLocalMax (fun y ↦ u y - φ y) x →
      (∂[(0 : Fin 2)] φ) x + H ((∂[(1 : Fin 2)] φ) x) ≤ 0

/-- Differentiable-test supersolution inequality for `u_t + H(u_x) = 0` on a domain `U`.

This is the ambient-local inequality core: the test function must touch `u` from below in the
ambient spacetime topology, not merely relative to `U`. Continuity/lower-semicontinuity of `u` is
not included in this predicate. -/
def IsAmbientDifferentiableTestSupersolution
    (H : ℝ → ℝ) (U : Set ℝ^2) (u : ℝ^2 → ℝ) : Prop :=
  ∀ x ∈ U, ∀ φ : ℝ^2 → ℝ, DifferentiableAt ℝ φ x →
    IsLocalMin (fun y ↦ u y - φ y) x →
      0 ≤ (∂[(0 : Fin 2)] φ) x + H ((∂[(1 : Fin 2)] φ) x)

/-- Ambient-local viscosity-solution inequality core: both subsolution and supersolution
inequalities.

This is the inequality core; regularity assumptions on `u` remain external hypotheses. -/
def IsAmbientDifferentiableTestSolution
    (H : ℝ → ℝ) (U : Set ℝ^2) (u : ℝ^2 → ℝ) : Prop :=
  IsAmbientDifferentiableTestSubsolution H U u ∧ IsAmbientDifferentiableTestSupersolution H U u

/-- Domain-relative viscosity subsolution inequality for `u_t + H(u_x, x) = 0`.

Only differentiability at the touching point is required. This is the local
first-order viscosity condition on an open spacetime domain. -/
def IsSpatialDifferentiableTestSubsolution
    (H : ℝ → ℝ → ℝ) (U : Set ℝ^2) (u : ℝ^2 → ℝ) : Prop :=
  IsOpen U ∧
    ∀ z ∈ U, ∀ φ : ℝ^2 → ℝ, DifferentiableAt ℝ φ z →
      IsLocalMaxOn (fun y ↦ u y - φ y) U z →
        (∂[(0 : Fin 2)] φ) z +
            H ((∂[(1 : Fin 2)] φ) z) (z 1) ≤ 0

/-- Domain-relative viscosity supersolution inequality for `u_t + H(u_x, x) = 0`. -/
def IsSpatialDifferentiableTestSupersolution
    (H : ℝ → ℝ → ℝ) (U : Set ℝ^2) (u : ℝ^2 → ℝ) : Prop :=
  IsOpen U ∧
    ∀ z ∈ U, ∀ φ : ℝ^2 → ℝ, DifferentiableAt ℝ φ z →
      IsLocalMinOn (fun y ↦ u y - φ y) U z →
        0 ≤ (∂[(0 : Fin 2)] φ) z +
          H ((∂[(1 : Fin 2)] φ) z) (z 1)

/-- The pair of domain-relative viscosity inequalities for `u_t + H(u_x, x) = 0`. -/
def IsSpatialDifferentiableTestSolution
    (H : ℝ → ℝ → ℝ) (U : Set ℝ^2) (u : ℝ^2 → ℝ) : Prop :=
  IsSpatialDifferentiableTestSubsolution H U u ∧
    IsSpatialDifferentiableTestSupersolution H U u

/-- Differentiable-test solution of `u_t + H(u_x) = 0` on an open domain.

Continuity is stated separately below. -/
def IsDifferentiableTestSolution (H : ℝ → ℝ) (U : Set ℝ^2) (u : ℝ^2 → ℝ) : Prop :=
  IsSpatialDifferentiableTestSolution (fun p _x ↦ H p) U u

/-- A continuous solution certified against every test differentiable at contact. -/
def IsContinuousDifferentiableTestSolution
    (H : ℝ → ℝ) (U : Set ℝ^2) (u : ℝ^2 → ℝ) : Prop :=
  ContinuousOn u U ∧ IsDifferentiableTestSolution H U u

/-- At a local extremum of `u - φ`, differentiable `u` and `φ` have equal partial derivatives. -/
private theorem partialDeriv_eq_of_isLocalExtr {u φ : ℝ^2 → ℝ} {z : ℝ^2}
    (hu : DifferentiableAt ℝ u z) (hφ : DifferentiableAt ℝ φ z)
    (h : IsLocalExtr (fun y ↦ u y - φ y) z) (i : Fin 2) :
    (∂[i] u) z = (∂[i] φ) z :=
  PDE.partialDeriv_eq_of_fderiv_eq
    (sub_eq_zero.mp (h.hasFDerivAt_eq_zero (hu.hasFDerivAt.sub hφ.hasFDerivAt))) i

/-- A classical pointwise solution of `u_t + H(u_x, x) = 0` on an open
domain satisfies both domain-relative viscosity inequalities. -/
theorem isSpatialDifferentiableTestSolution_of_classical {H : ℝ → ℝ → ℝ} {U : Set ℝ^2} {u : ℝ^2 → ℝ}
    (hU : IsOpen U) (hu : ∀ z ∈ U, DifferentiableAt ℝ u z)
    (hpde : ∀ z ∈ U, (∂[(0 : Fin 2)] u) z + H ((∂[(1 : Fin 2)] u) z) (z 1) = 0) :
    IsSpatialDifferentiableTestSolution H U u := by
  refine ⟨⟨hU, fun z hz φ hφ hmax ↦ ?_⟩, ⟨hU, fun z hz φ hφ hmin ↦ ?_⟩⟩
  · have h := partialDeriv_eq_of_isLocalExtr (hu z hz) hφ (.inr (hmax.isLocalMax (hU.mem_nhds hz)))
    exact le_of_eq (by simpa [h] using hpde z hz)
  · have h := partialDeriv_eq_of_isLocalExtr (hu z hz) hφ (.inl (hmin.isLocalMin (hU.mem_nhds hz)))
    exact le_of_eq (by simpa [h] using (hpde z hz).symm)

/-- On an open domain, an ambient-local solution is a viscosity solution. -/
theorem IsAmbientDifferentiableTestSolution.toSpatial {H : ℝ → ℝ} {U : Set ℝ^2} {u : ℝ^2 → ℝ}
    (hU : IsOpen U) (hu : IsAmbientDifferentiableTestSolution H U u) :
    IsDifferentiableTestSolution H U u :=
  ⟨⟨hU, fun x hx φ hφ hmax ↦ hu.1 x hx φ hφ (hmax.isLocalMax (hU.mem_nhds hx))⟩,
    ⟨hU, fun x hx φ hφ hmin ↦ hu.2 x hx φ hφ (hmin.isLocalMin (hU.mem_nhds hx))⟩⟩

/-- Classical pointwise solutions satisfy the viscosity inequality core. -/
theorem isAmbientDifferentiableTestSolution_of_classical {H : ℝ → ℝ} {U : Set ℝ^2} {u : ℝ^2 → ℝ}
    (hu : ∀ x ∈ U, DifferentiableAt ℝ u x)
    (hpde : ∀ x ∈ U, (∂[(0 : Fin 2)] u) x + H ((∂[(1 : Fin 2)] u) x) = 0) :
    IsAmbientDifferentiableTestSolution H U u := by
  refine ⟨fun x hx φ hφ hmax ↦ ?_, fun x hx φ hφ hmin ↦ ?_⟩
  · have h := partialDeriv_eq_of_isLocalExtr (hu x hx) hφ (.inr hmax)
    exact le_of_eq (by simpa [h] using hpde x hx)
  · have h := partialDeriv_eq_of_isLocalExtr (hu x hx) hφ (.inl hmin)
    exact le_of_eq (by simpa [h] using (hpde x hx).symm)

/-- Classical pointwise solutions are continuous viscosity solutions on an open domain. -/
theorem isContinuousDifferentiableTestSolution_of_classical {H : ℝ → ℝ} {U : Set ℝ^2} {u : ℝ^2 → ℝ}
    (hU : IsOpen U) (hu : ∀ x ∈ U, DifferentiableAt ℝ u x)
    (hpde : ∀ x ∈ U, (∂[(0 : Fin 2)] u) x + H ((∂[(1 : Fin 2)] u) x) = 0) :
    IsContinuousDifferentiableTestSolution H U u :=
  ⟨fun x hx ↦ (hu x hx).continuousAt.continuousWithinAt,
    (isAmbientDifferentiableTestSolution_of_classical hu hpde).toSpatial hU⟩

/-- Constant profiles give Hamilton–Jacobi viscosity solutions on open domains whenever
`H 0 = 0`. -/
theorem isDifferentiableTestSolution_const_of_H_zero {H : ℝ → ℝ} {U : Set ℝ^2} (c : ℝ)
    (hU : IsOpen U) (hH0 : H 0 = 0) :
    IsDifferentiableTestSolution H U (fun _ : ℝ^2 ↦ c) :=
  (isAmbientDifferentiableTestSolution_of_classical (fun _ _ ↦ differentiableAt_const c)
    fun _ _ ↦ by simp [PDE.partialDeriv_const, hH0]).toSpatial hU

/-- Constant profiles give continuous Hamilton–Jacobi viscosity solutions on open domains
whenever `H 0 = 0`. -/
theorem isContinuousDifferentiableTestSolution_const_of_H_zero {H : ℝ → ℝ} {U : Set ℝ^2} (c : ℝ)
    (hU : IsOpen U) (hH0 : H 0 = 0) :
    IsContinuousDifferentiableTestSolution H U (fun _ : ℝ^2 ↦ c) :=
  isContinuousDifferentiableTestSolution_of_classical hU (fun _ _ ↦ differentiableAt_const c)
    fun _ _ ↦ by simp [PDE.partialDeriv_const, hH0]

/-- A regular characteristic solution satisfies the ambient-local viscosity inequalities
on its open footpoint domain. -/
theorem characteristicSolution_isAmbientDifferentiableTestSolution {H φ : ℝ → ℝ} {ξ : ℝ^2 → ℝ}
    {U : Set ℝ^2} (hH : Differentiable ℝ H) (hH' : Differentiable ℝ (deriv H))
    (hφ : Differentiable ℝ φ) (hφ' : Differentiable ℝ (deriv φ)) (hU : IsOpen U)
    (hξ : ∀ x ∈ U, DifferentiableAt ℝ ξ x) (hrel : IsFootpointOn H φ ξ U) :
    IsAmbientDifferentiableTestSolution H U (characteristicSolution H φ ξ) :=
  isAmbientDifferentiableTestSolution_of_classical
    (fun x hx ↦ differentiableAt_characteristicSolution hH hH' hφ hφ' (hξ x hx))
    (characteristicSolution_residual_on hH hH' hφ hφ' hU hξ hrel)

/-- A regular characteristic solution is a viscosity solution on its open
footpoint domain. -/
theorem characteristicSolution_isDifferentiableTestSolution {H φ : ℝ → ℝ} {ξ : ℝ^2 → ℝ}
    {U : Set ℝ^2} (hH : Differentiable ℝ H) (hH' : Differentiable ℝ (deriv H))
    (hφ : Differentiable ℝ φ) (hφ' : Differentiable ℝ (deriv φ)) (hU : IsOpen U)
    (hξ : ∀ x ∈ U, DifferentiableAt ℝ ξ x) (hrel : IsFootpointOn H φ ξ U) :
    IsDifferentiableTestSolution H U (characteristicSolution H φ ξ) :=
  (characteristicSolution_isAmbientDifferentiableTestSolution hH hH' hφ hφ' hU hξ hrel).toSpatial hU

end

end HamiltonJacobi1D
