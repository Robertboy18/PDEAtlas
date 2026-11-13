/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Problem.Equation.Satisfaction
public import PDE.FDeriv.PartialDeriv

/-!
# Scalar conservation-law equations

We define the residual form of a scalar conservation law

`u_t + divₓ (flux (u)) = 0`

on a spacetime domain.
-/

@[expose] public section

namespace PDE.Hyperbolic.ConservationLaw

open Finset

variable {n : ℕ}

/-- Scalar conservation law in divergence form: `u_t + divₓ (flux (u)) = 0`. -/
noncomputable def conservationLawEquation
    (flux : ℝ → ℝ^n)
    (U : Set (ℝ^(n + 1))) :
    PDEProblem (ℝ^(n + 1)) ℝ :=
  { eqns := [
      { Output := ℝ
        operator := fun u xt ↦
          (∂[0] u) xt +
            ∑ i : Fin n, (∂[i.succ] (fun z ↦ flux (u z) i)) xt
        rhs := fun _ ↦ 0
        domain := U }
    ]
    sideConditions := [] }

/-- The bundled conservation law is equivalent to its pointwise flux-divergence equation. -/
theorem conservationLawEquation_iff {flux : ℝ → ℝ^n} {U : Set (ℝ^(n + 1))} {u : ℝ^(n + 1) → ℝ} :
    SatisfiesPDEProblem (conservationLawEquation flux U) u ↔ ∀ x ∈ U, (∂[0] u) x + ∑ i : Fin n,
      (∂[i.succ] (fun z ↦ flux (u z) i)) x = 0 := by
  constructor
  · intro hu x hx
    let eqn : PDEEquation (ℝ^(n + 1)) ℝ :=
      { Output := ℝ
        operator := fun v y ↦ (∂[0] v) y + ∑ i : Fin n, (∂[i.succ] (fun z ↦ flux (v z) i)) y
        rhs := fun _ ↦ 0
        domain := U }
    exact SatisfiesPDEProblem.eqn hu
      (eqn := eqn) (by simp [eqn, conservationLawEquation]) hx
  · intro hu
    refine SatisfiesPDEProblem.mk ?_ ?_
    · intro eqn heqn x hx
      simp only [conservationLawEquation, List.mem_singleton] at heqn
      subst heqn
      exact hu x hx
    · intro eqn heqn
      simp [conservationLawEquation] at heqn

end PDE.Hyperbolic.ConservationLaw
