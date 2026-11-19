/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Problem.Equation.Satisfaction
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import PDE.FDeriv.PartialDeriv
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Symmetric first-order hyperbolic systems

We formalize the setting of Evans, §7.3.1: systems

`u_t + sum_j B_j(x,t) u_{x_j} = f(x,t)`

with values in a finite-dimensional real Euclidean space.

## Main definitions

* `LinearFirstOrderSystem`, the coefficient, forcing, and domain data;
* `LinearFirstOrderSystem.principalSymbol`;
* the pointwise predicates `LinearFirstOrderSystem.IsHyperbolicAt`,
  `LinearFirstOrderSystem.IsStrictlyHyperbolicAt` and `LinearFirstOrderSystem.IsSymmetricAt`,
  and their domain-wide forms;
* `LinearFirstOrderSystem.initialValueProblem`.

## Main results

* `LinearFirstOrderSystem.IsSymmetricAt.isHyperbolicAt`: by the finite-dimensional spectral
  theorem, every symmetric system is hyperbolic in Evans's sense;
* `LinearFirstOrderSystem.local_energy_flux_identity`: the pointwise identity behind the energy
  calculation in step 2 of the proof of Theorem 2 in Evans, §7.3.2, including the
  coefficient-derivative term required for variable coefficients.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.3.1, equations (1)-(2) and the definitions of hyperbolic,
  symmetric hyperbolic and strictly hyperbolic systems; §7.3.2, proof of Theorem 2, step 2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Finset
open PDE.Common
open scoped InnerProductSpace

namespace PDE.Hyperbolic.FirstOrder

/-! ## First-order systems and their symbols -/

/-- Coefficient data for a linear first-order system on Euclidean spacetime.

The equation is imposed on `domain`; the initial slice is supplied separately
when constructing an initial-value problem. -/
structure LinearFirstOrderSystem (n m : ℕ) where
  /-- Spatial coefficient operators `B_j(x,t)`. -/
  coefficient : Fin n → SpaceTime n → ℝ^m →L[ℝ] ℝ^m
  /-- Inhomogeneous term `f(x,t)`. -/
  forcing : SpaceTime n → ℝ^m
  /-- Spacetime region on which the differential equation is imposed. -/
  domain : Set (SpaceTime n)

namespace LinearFirstOrderSystem

variable {n m : ℕ}

/-- The left-hand side `u_t + sum_j B_j u_{x_j}`. -/
def operator
    (S : LinearFirstOrderSystem n m)
    (u : SpaceTime n → ℝ^m) (p : SpaceTime n) : ℝ^m :=
  (∂[0] u) p +
    ∑ j : Fin n, S.coefficient j p ((∂[j.succ] u) p)

/-- The equation residual `u_t + sum_j B_j u_{x_j} - f`. -/
def residual
    (S : LinearFirstOrderSystem n m)
    (u : SpaceTime n → ℝ^m) (p : SpaceTime n) : ℝ^m :=
  S.operator u p - S.forcing p

/-- Evans's principal symbol `B(x,t; xi) = sum_j xi_j B_j(x,t)`. -/
def principalSymbol
    (S : LinearFirstOrderSystem n m)
    (p : SpaceTime n) (xi : ℝ^n) : ℝ^m →L[ℝ] ℝ^m :=
  ∑ j : Fin n, (xi j) • S.coefficient j p

/-- The principal symbol vanishes at the zero covector. -/
@[simp]
theorem principalSymbol_zero (S : LinearFirstOrderSystem n m) (p : SpaceTime n) :
    S.principalSymbol p 0 = 0 := by
  ext v
  simp [principalSymbol]

/-- The principal symbol is additive in its covector argument. -/
@[simp]
theorem principalSymbol_add (S : LinearFirstOrderSystem n m) (p : SpaceTime n) (xi eta : ℝ^n) :
    S.principalSymbol p (xi + eta) = S.principalSymbol p xi + S.principalSymbol p eta := by
  ext v
  simp [principalSymbol, add_smul, Finset.sum_add_distrib]

/-- The principal symbol is homogeneous in its covector argument. -/
@[simp]
theorem principalSymbol_smul (S : LinearFirstOrderSystem n m) (p : SpaceTime n) (c : ℝ) (xi : ℝ^n) :
    S.principalSymbol p (c • xi) = c • S.principalSymbol p xi := by
  ext v
  simp [principalSymbol, Finset.smul_sum, smul_smul]

/-- A system is hyperbolic at `p` when every principal symbol at `p` has a real eigenbasis.

This is the basis-valued form of Evans, §7.3.1: the principal symbol is
diagonalizable over `ℝ`. -/
def IsHyperbolicAt
    (S : LinearFirstOrderSystem n m) (p : SpaceTime n) : Prop :=
  ∀ xi, ∃ b : Module.Basis (Fin m) ℝ (ℝ^m), ∃ speed : Fin m → ℝ,
    ∀ k, Module.End.HasEigenvector
      (S.principalSymbol p xi).toLinearMap (speed k) (b k)

/-- A system is hyperbolic when it is hyperbolic at every point of its PDE domain. -/
def IsHyperbolic (S : LinearFirstOrderSystem n m) : Prop :=
  ∀ p ∈ S.domain, S.IsHyperbolicAt p

/-- Strict hyperbolicity at `p` requires distinct characteristic speeds away
from the zero covector. -/
def IsStrictlyHyperbolicAt
    (S : LinearFirstOrderSystem n m) (p : SpaceTime n) : Prop :=
  ∀ xi, xi ≠ 0 →
    ∃ b : Module.Basis (Fin m) ℝ (ℝ^m), ∃ speed : Fin m → ℝ,
      Function.Injective speed ∧
        ∀ k, Module.End.HasEigenvector
          (S.principalSymbol p xi).toLinearMap (speed k) (b k)

/-- A system is strictly hyperbolic when it is strictly hyperbolic throughout its PDE domain. -/
def IsStrictlyHyperbolic (S : LinearFirstOrderSystem n m) : Prop :=
  ∀ p ∈ S.domain, S.IsStrictlyHyperbolicAt p

namespace IsStrictlyHyperbolicAt

variable {S : LinearFirstOrderSystem n m} {p : SpaceTime n}

/-- Strict hyperbolicity at a point implies hyperbolicity there. -/
theorem isHyperbolicAt (hS : S.IsStrictlyHyperbolicAt p) :
    S.IsHyperbolicAt p := by
  intro xi
  by_cases hxi : xi = 0
  · subst xi
    refine ⟨(EuclideanSpace.basisFun (Fin m) ℝ).toBasis, fun _ ↦ 0, fun k ↦ ?_⟩
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    exact ⟨by simp, (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.ne_zero k⟩
  · rcases hS xi hxi with ⟨b, speed, _, heigen⟩
    exact ⟨b, speed, heigen⟩

end IsStrictlyHyperbolicAt

namespace IsStrictlyHyperbolic

variable {S : LinearFirstOrderSystem n m}

/-- Strict hyperbolicity throughout the PDE domain implies hyperbolicity there. -/
theorem isHyperbolic (hS : S.IsStrictlyHyperbolic) :
    S.IsHyperbolic :=
  fun p hp ↦ (hS p hp).isHyperbolicAt

end IsStrictlyHyperbolic

/-- A system is symmetric at `p` when every spatial coefficient there is self-adjoint. -/
def IsSymmetricAt
    (S : LinearFirstOrderSystem n m) (p : SpaceTime n) : Prop :=
  ∀ j, (S.coefficient j p : ℝ^m →ₗ[ℝ] ℝ^m).IsSymmetric

/-- A symmetric first-order system is symmetric at every point of its PDE domain. -/
def IsSymmetric (S : LinearFirstOrderSystem n m) : Prop :=
  ∀ p ∈ S.domain, S.IsSymmetricAt p

namespace IsSymmetricAt

variable {S : LinearFirstOrderSystem n m} {p : SpaceTime n}

/-- Every principal symbol of a system symmetric at `p` is symmetric. -/
theorem principalSymbol_isSymmetric (hS : S.IsSymmetricAt p) (xi : ℝ^n) :
    (S.principalSymbol p xi : ℝ^m →ₗ[ℝ] ℝ^m).IsSymmetric := by
  have heq : (S.principalSymbol p xi : ℝ^m →ₗ[ℝ] ℝ^m) = ∑ j : Fin n, (xi j) •
          (S.coefficient j p : ℝ^m →ₗ[ℝ] ℝ^m) := by
    ext x
    simp [principalSymbol]
  rw [heq]
  exact LinearMap.isSymmetric_sum Finset.univ fun j _ ↦ (hS j).smul (by simp)

/-- Every principal symbol of a system symmetric at `p` is self-adjoint. -/
theorem principalSymbol_isSelfAdjoint (hS : S.IsSymmetricAt p) (xi : ℝ^n) :
    IsSelfAdjoint (S.principalSymbol p xi) :=
  (hS.principalSymbol_isSymmetric xi).isSelfAdjoint

/-- A symmetric system is hyperbolic at the same point by the real spectral theorem. -/
theorem isHyperbolicAt (hS : S.IsSymmetricAt p) :
    S.IsHyperbolicAt p := by
  intro xi
  have hA := hS.principalSymbol_isSymmetric xi
  have hrank : Module.finrank ℝ (ℝ^m) = m := by
    simp
  exact ⟨(hA.eigenvectorBasis hrank).toBasis, hA.eigenvalues hrank,
      hA.hasEigenvector_eigenvectorBasis hrank⟩

end IsSymmetricAt

namespace IsSymmetric

variable {S : LinearFirstOrderSystem n m}

/-- A symmetric system has symmetric principal symbols throughout its domain. -/
theorem principalSymbol_isSymmetric
    (hS : S.IsSymmetric) (p : SpaceTime n) (hp : p ∈ S.domain) (xi : ℝ^n) :
    (S.principalSymbol p xi : ℝ^m →ₗ[ℝ] ℝ^m).IsSymmetric :=
  (hS p hp).principalSymbol_isSymmetric xi

/-- A symmetric system has self-adjoint principal symbols throughout its domain. -/
theorem principalSymbol_isSelfAdjoint
    (hS : S.IsSymmetric) (p : SpaceTime n) (hp : p ∈ S.domain) (xi : ℝ^n) :
    IsSelfAdjoint (S.principalSymbol p xi) :=
  (hS p hp).principalSymbol_isSelfAdjoint xi

/-- Symmetric systems are hyperbolic by the real finite-dimensional spectral theorem. -/
theorem isHyperbolic (hS : S.IsSymmetric) :
    S.IsHyperbolic :=
  fun p hp ↦ (hS p hp).isHyperbolicAt

end IsSymmetric

/-! ## Bundled initial-value problem -/

/-- The initial time slice `t = 0`. -/
def initialSlice (n : ℕ) : Set (SpaceTime n) :=
  {p | p 0 = 0}

/-- The pointwise initial-value problem associated with a first-order system. -/
def initialValueProblem
    (S : LinearFirstOrderSystem n m) (g : ℝ^n → ℝ^m) :
    PDEProblem (SpaceTime n) (ℝ^m) where
  eqns := [{
    Output := ℝ^m
    operator := S.operator
    rhs := S.forcing
    domain := S.domain
  }]
  sideConditions := [{
    Output := ℝ^m
    operator := fun u p ↦ u p
    rhs := g ∘ spatialPartCLM n
    domain := initialSlice n
  }]

/-- A solution of the bundled initial-value problem satisfies the PDE on `S.domain`. -/
theorem initialValueProblem.operator_eq {S : LinearFirstOrderSystem n m} {g : ℝ^n → ℝ^m}
    {u : SpaceTime n → ℝ^m} (hu : SatisfiesPDEProblem (S.initialValueProblem g) u) {p : SpaceTime n}
    (hp : p ∈ S.domain) :
    S.operator u p = S.forcing p := by
  let eqn : PDEEquation (SpaceTime n) (ℝ^m) :=
    { Output := ℝ^m
      operator := S.operator
      rhs := S.forcing
      domain := S.domain }
  have heqn : eqn ∈ (S.initialValueProblem g).eqns := by
    simp [eqn, initialValueProblem]
  exact hu.eqn heqn hp

/-- A solution of the bundled initial-value problem satisfies the assigned initial value. -/
theorem initialValueProblem.initial_eq {S : LinearFirstOrderSystem n m} {g : ℝ^n → ℝ^m}
    {u : SpaceTime n → ℝ^m} (hu : SatisfiesPDEProblem (S.initialValueProblem g) u) {p : SpaceTime n}
    (hp : p ∈ initialSlice n) :
    u p = g (spatialPartCLM n p) := by
  let eqn : PDEEquation (SpaceTime n) (ℝ^m) :=
    { Output := ℝ^m
      operator := fun v q ↦ v q
      rhs := g ∘ spatialPartCLM n
      domain := initialSlice n }
  have heqn : eqn ∈ (S.initialValueProblem g).sideConditions := by
    simp [eqn, initialValueProblem]
  simpa [eqn, Function.comp_apply] using hu.side_condition heqn hp

/-- Construct a bundled initial-value solution from its PDE and assigned initial-value identity. -/
theorem initialValueProblem.of_operator_initial {S : LinearFirstOrderSystem n m} {g : ℝ^n → ℝ^m}
    {u : SpaceTime n → ℝ^m} (hop : ∀ p ∈ S.domain, S.operator u p = S.forcing p)
    (hinit : ∀ p ∈ initialSlice n, u p = g (spatialPartCLM n p)) :
    SatisfiesPDEProblem (S.initialValueProblem g) u := by
  refine SatisfiesPDEProblem.mk ?_ ?_
  · intro eqn heqn p hp
    simp only [initialValueProblem, List.mem_singleton] at heqn
    subst eqn
    exact hop p hp
  · intro eqn heqn p hp
    simp only [initialValueProblem, List.mem_singleton] at heqn
    subst eqn
    simpa [Function.comp_apply] using hinit p hp

/-- Characterization of the bundled initial-value problem by its two pointwise conditions. -/
theorem initialValueProblem_iff {S : LinearFirstOrderSystem n m} {g : ℝ^n → ℝ^m}
    {u : SpaceTime n → ℝ^m} :
    SatisfiesPDEProblem (S.initialValueProblem g) u ↔ (∀ p ∈ S.domain, S.operator u p =
      S.forcing p) ∧ ∀ p ∈ initialSlice n, u p = g (spatialPartCLM n p) := by
  constructor
  · intro hu
    exact ⟨fun p hp ↦ initialValueProblem.operator_eq hu hp,
        fun p hp ↦ initialValueProblem.initial_eq hu hp⟩
  · rintro ⟨hop, hinit⟩
    exact initialValueProblem.of_operator_initial hop hinit

/-! ## Pointwise energy identity -/

/-- Quadratic energy density `|u|^2 / 2`. -/
def energyDensity (u : ℝ^m) : ℝ :=
  (1 / 2 : ℝ) * ‖u‖ ^ 2

/-- Energy flux associated with one coefficient operator. -/
def energyFlux (B : ℝ^m →L[ℝ] ℝ^m) (u : ℝ^m) : ℝ :=
  (1 / 2 : ℝ) * ⟪B u, u⟫_ℝ

/-- The spacetime energy density of a field. -/
def energyField (u : SpaceTime n → ℝ^m) (p : SpaceTime n) : ℝ :=
  energyDensity (u p)

/-- The `j`th spacetime energy flux of a field. -/
def energyFluxField
    (S : LinearFirstOrderSystem n m) (j : Fin n)
    (u : SpaceTime n → ℝ^m) (p : SpaceTime n) : ℝ :=
  energyFlux (S.coefficient j p) (u p)

/-- A coordinate derivative of quadratic energy is the inner product with
the corresponding coordinate derivative of the field. -/
theorem partialDeriv_energyDensity {u : SpaceTime n → ℝ^m} {p : SpaceTime n} (i : Fin (n + 1))
    (hu : DifferentiableAt ℝ u p) :
    (∂[i] (energyDensity ∘ u)) p = ⟪(∂[i] u) p, u p⟫_ℝ := by
  have hnorm : DifferentiableAt ℝ (fun q ↦ ‖u q‖ ^ 2) p := hu.norm_sq ℝ
  unfold energyDensity Function.comp partialDeriv
  rw [fderiv_const_mul hnorm (1 / 2 : ℝ)]
  rw [hu.hasFDerivAt.norm_sq.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_eq_mul]
  rw [real_inner_comm]
  ring

/-- Product rule for one coordinate derivative of the energy flux.

Symmetry combines the two derivatives falling on `u`; differentiating `B`
produces the variable-coefficient correction. -/
theorem partialDeriv_energyFlux {B : SpaceTime n → ℝ^m →L[ℝ] ℝ^m} {u : SpaceTime n → ℝ^m}
    {p : SpaceTime n} (i : Fin (n + 1)) (hB : DifferentiableAt ℝ B p) (hu : DifferentiableAt ℝ u p)
    (hsymm : (B p : ℝ^m →ₗ[ℝ] ℝ^m).IsSymmetric) :
    (∂[i] (fun q ↦ energyFlux (B q) (u q))) p = ⟪B p ((∂[i] u) p),
      u p⟫_ℝ + (1 / 2 : ℝ) * ⟪((∂[i] B) p) (u p), u p⟫_ℝ := by
  have hBu : DifferentiableAt ℝ (fun q ↦ B q (u q)) p := hB.clm_apply hu
  have hinner : DifferentiableAt ℝ (fun q ↦ ⟪B q (u q), u q⟫_ℝ) p := hBu.inner ℝ hu
  unfold energyFlux partialDeriv
  rw [fderiv_const_mul hinner (1 / 2 : ℝ)]
  simp only [smul_apply, smul_eq_mul]
  rw [fderiv_inner_apply (𝕜 := ℝ) hBu hu]
  rw [fderiv_clm_apply hB hu]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, inner_add_left]
  have hsymm' : ⟪B p (u p), fderiv ℝ u p (EuclideanSpace.single i (1 : ℝ))⟫_ℝ = ⟪u p,
          B p (fderiv ℝ u p (EuclideanSpace.single i (1 : ℝ)))⟫_ℝ :=
    hsymm (u p) (fderiv ℝ u p (EuclideanSpace.single i (1 : ℝ)))
  rw [hsymm']
  rw [real_inner_comm (B p (fderiv ℝ u p (EuclideanSpace.single i (1 : ℝ)))) (u p)]
  ring

/-- The pointwise energy-flux identity for a differentiable solution of a
first-order system whose coefficients are symmetric at the point.

This is the local identity underlying Evans's integration-by-parts energy
calculation. For variable coefficients, differentiating the flux contributes
`(1/2) sum_j <(partial_j B_j)u,u>`; the term disappears for constant
coefficients. -/
theorem local_energy_flux_identity_at {S : LinearFirstOrderSystem n m} {u : SpaceTime n → ℝ^m}
    {p : SpaceTime n} (hS : S.IsSymmetricAt p) (hu : DifferentiableAt ℝ u p)
    (hB : ∀ j, DifferentiableAt ℝ (S.coefficient j) p) (hop : S.operator u p = S.forcing p) :
    (∂[0] (energyField u)) p + ∑ j : Fin n, (∂[j.succ] (S.energyFluxField j u)) p = ⟪S.forcing p,
      u p⟫_ℝ + (1 / 2 : ℝ) * ∑ j : Fin n, ⟪((∂[j.succ] (S.coefficient j)) p) (u p), u p⟫_ℝ := by
  have henergy : (∂[0] (energyField u)) p = ⟪(∂[0] u) p, u p⟫_ℝ := partialDeriv_energyDensity 0 hu
  have hflux : ∀ j : Fin n, (∂[j.succ] (S.energyFluxField j u)) p =
          ⟪S.coefficient j p ((∂[j.succ] u) p), u p⟫_ℝ + (1 / 2 : ℝ) *
              ⟪((∂[j.succ] (S.coefficient j)) p) (u p), u p⟫_ℝ :=
    fun j ↦ partialDeriv_energyFlux j.succ (hB j) hu (hS j)
  have heq : ⟪(∂[0] u) p, u p⟫_ℝ + ∑ j : Fin n, ⟪S.coefficient j p ((∂[j.succ] u) p), u p⟫_ℝ =
        ⟪S.forcing p, u p⟫_ℝ := by
    have h := congrArg (fun z : ℝ^m ↦ ⟪z, u p⟫_ℝ) hop
    simpa [operator, inner_add_left, sum_inner] using h
  rw [henergy]
  simp_rw [hflux]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [← add_assoc, heq]

/-- The local energy-flux identity for a differentiable solution of a
symmetric first-order system on its PDE domain. -/
theorem local_energy_flux_identity {S : LinearFirstOrderSystem n m} {u : SpaceTime n → ℝ^m}
    {p : SpaceTime n} (hS : S.IsSymmetric) (hp : p ∈ S.domain) (hu : DifferentiableAt ℝ u p)
    (hB : ∀ j, DifferentiableAt ℝ (S.coefficient j) p) (hop : S.operator u p = S.forcing p) :
    (∂[0] (energyField u)) p + ∑ j : Fin n, (∂[j.succ] (S.energyFluxField j u)) p = ⟪S.forcing p,
      u p⟫_ℝ + (1 / 2 : ℝ) * ∑ j : Fin n, ⟪((∂[j.succ] (S.coefficient j)) p) (u p), u p⟫_ℝ :=
  local_energy_flux_identity_at (hS p hp) hu hB hop

end LinearFirstOrderSystem

end PDE.Hyperbolic.FirstOrder
