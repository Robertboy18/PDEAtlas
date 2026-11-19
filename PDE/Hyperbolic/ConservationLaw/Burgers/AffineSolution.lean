/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv
public import PDE.Problem.Equation.Satisfaction
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# Affine solutions of the inviscid Burgers equation

We formalize the 1D inviscid Burgers equation

`u_t + u * u_x = 0`

as a `PDEProblem` on spacetime `ℝ^2` with coordinates
`x 0 = t` and `x 1 = x`.

We prove that the solution of Burgers's equation with affine initial data
`u(0,x) = a*x + c` is

`u(t,x) = (a*x + c) / (1 + a*t)`,

and that, on the natural domain where the denominator is nonzero, it satisfies the
pointwise Burgers residual and initial condition.

The formula is the implicit formula (61) of Evans, §3.2.5, Example 5, for Burgers' equation:
`u = a (x - t u) + c`. In §3.4.1, Example 1, the middle region `(1 - x)/(1 - t)` is the case
`a = -1`, `c = 1`, and the method breaks down for `t ≥ 1` because the projected characteristics
cross.

The general implicit characteristic construction is in
`PDE.Hyperbolic.ConservationLaw.Scalar.Characteristics`.
For affine data the partial derivatives and the residual identity are checked by the SymLean
`cas` tactic.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.2.5, Example 5, equation (61); §3.4.1(a), Example 1,
  equations (13)-(14).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (PDEProblem SatisfiesPDEProblem)

namespace BurgersEquation

noncomputable section

open PDE.Common

/-- Numerator `a*x + c`. -/
noncomputable def burgersNumer (a c : ℝ) : ℝ^2 → ℝ := fun x ↦ a * x 1 + c

/-- Denominator `1 + a*t`. -/
noncomputable def burgersDenom (a : ℝ) : ℝ^2 → ℝ := fun x ↦ 1 + a * x 0

/-- Inverse denominator `(1 + a*t)⁻¹`. -/
noncomputable def burgersInvDenom (a : ℝ) : ℝ^2 → ℝ := fun x ↦ (burgersDenom a x)⁻¹

/-- Affine-data candidate `u(t,x) = (a*x + c)/(1 + a*t)`. -/
noncomputable def burgersAffineSolution (a c : ℝ) : ℝ^2 → ℝ :=
  fun x ↦ burgersNumer a c x * burgersInvDenom a x

/-- Domain where we impose the PDE: forward time and non-vanishing denominator. -/
def affineSolutionDomain (a : ℝ) : Set ℝ^2 :=
  {x | 0 ≤ x 0 ∧ burgersDenom a x ≠ 0}

/-- Burgers residual problem with affine initial data `u(0,x)=a*x+c`. -/
noncomputable def burgersAffineIVP (a c : ℝ) : PDEProblem ℝ^2 ℝ :=
  { eqns := [
      { Output := ℝ
        operator := fun u x ↦ (∂[(0 : Fin 2)] u) x + (u x) * (∂[(1 : Fin 2)] u) x
        rhs := fun _ ↦ 0
        domain := affineSolutionDomain a }
    ]
    sideConditions := [
      { Output := ℝ
        operator := id
        rhs := fun x ↦ a * x 1 + c
        domain := initialTimeSlice }
    ] }

private theorem partialDeriv_burgersAffineSolution_time (a c : ℝ) (x : ℝ^2)
    (hden : burgersDenom a x ≠ 0) :
    (∂[(0 : Fin 2)] (burgersAffineSolution a c)) x =
      -a * burgersNumer a c x * (burgersDenom a x)⁻¹ * (burgersDenom a x)⁻¹ := by
  cas

private theorem partialDeriv_burgersAffineSolution_space (a c : ℝ) (x : ℝ^2)
    (hden : burgersDenom a x ≠ 0) :
    (∂[(1 : Fin 2)] (burgersAffineSolution a c)) x = a * (burgersDenom a x)⁻¹ := by
  cas

private theorem burgersAffineSolution_satisfies_pde (a c : ℝ) (x : ℝ^2)
    (hden : burgersDenom a x ≠ 0) :
    (∂[(0 : Fin 2)] (burgersAffineSolution a c)) x + burgersAffineSolution a c x *
      (∂[(1 : Fin 2)] (burgersAffineSolution a c)) x = 0 := by
  rw [partialDeriv_burgersAffineSolution_time a c x hden,
    partialDeriv_burgersAffineSolution_space a c x hden]
  unfold burgersAffineSolution burgersInvDenom
  cas

private theorem burgersAffineSolution_satisfies_initial (a c : ℝ) (x : ℝ^2) (hx : x 0 = 0) :
    burgersAffineSolution a c x = a * x 1 + c := by
  unfold burgersAffineSolution burgersNumer burgersInvDenom burgersDenom
  simp [hx]

/-- The affine characteristic formula solves Burgers' initial-value problem
on its natural domain. -/
theorem burgersAffineSolution_satisfiesPDEProblem (a c : ℝ) :
    SatisfiesPDEProblem (burgersAffineIVP a c) (burgersAffineSolution a c) := by
  intro eqn heqn x hx
  rcases List.mem_append.mp heqn with heqn | heqn
  · -- PDE equation
    have heq : eqn =
          { Output := ℝ
            operator := fun u x ↦ (∂[(0 : Fin 2)] u) x + u x * (∂[(1 : Fin 2)] u) x
            rhs := fun _ ↦ 0
            domain := affineSolutionDomain a } := by
      simpa [burgersAffineIVP] using heqn
    subst heq
    rcases hx with ⟨_ht, hden⟩
    simpa using burgersAffineSolution_satisfies_pde (a := a) (c := c) x hden
  · -- initial condition
    have heq : eqn =
          { Output := ℝ
            operator := id
            rhs := fun x ↦ a * x 1 + c
            domain := initialTimeSlice } := by
      simpa [burgersAffineIVP] using heqn
    subst heq
    simpa using burgersAffineSolution_satisfies_initial (a := a) (c := c) x hx

end

end BurgersEquation
