/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Transport
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# Right-moving sine transport solution

The problem is `u_t + u_x = 0` with `u(0, x) = sin x`. By the formula `u(x, t) = g(x - tb)` of
Evans, §2.1.1, (3), the solution is the initial profile transported to the right at unit
speed, `u(t, x) = sin(x - t)`, written here as a function on spacetime `ℝ^2` with coordinate
`0` as time. It solves the transport initial-value problem `transportIVP`
(`rightMovingSine_satisfiesPDEProblem`). The same profile as a symbolic expression is in
`PDE.Examples.Hyperbolic.Symbolic.Transport.RightMovingSine`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.1.1, (2)-(3), p. 18.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv SatisfiesPDEProblem)

namespace TransportEquation

noncomputable section

namespace Space1

/-- Unit velocity field for the one-dimensional transport equation. -/
def unitVelocity1D : ℝ^1 :=
  WithLp.toLp 2 fun _ ↦ 1

/-- Initial trace of `sin(x - t)` on the slice `t = 0`. -/
def rightMovingSineInitial1D (x : ℝ^1) : ℝ :=
  Real.sin (x 0)

/-- Right-moving sine profile `u(t, x) = sin(x - t)`. -/
def rightMovingSine (p : ℝ^2) : ℝ :=
  Real.sin (p 1 - p 0)

/-- The right-moving sine profile satisfies `∂ₜ u + ∂ₓ u = 0` at every point of spacetime. -/
theorem rightMovingSine_transport_residual (p : ℝ^2) :
    (∂[(0 : Fin 2)] rightMovingSine) p +
      (∂[(1 : Fin 2)] rightMovingSine) p = 0 := by
  have ht : (∂[(0 : Fin 2)] rightMovingSine) p = -Real.cos (p 1 - p 0) := by
    cas
  have hx : (∂[(1 : Fin 2)] rightMovingSine) p = Real.cos (p 1 - p 0) := by
    cas
  rw [ht, hx]
  ring

/-- The right-moving sine profile satisfies the unit-transport IVP. -/
theorem rightMovingSine_satisfiesPDEProblem :
    SatisfiesPDEProblem
      (transportIVP (n := 1) unitVelocity1D (fun _ : ℝ^2 ↦ 0) rightMovingSineInitial1D)
      rightMovingSine := by
  refine transportIVP.of_residual_initial ?_ ?_
  · intro p _hp
    rw [transportOperator_eq_timeDeriv_add_dot_spatialGradient, Fintype.sum_unique]
    simpa [unitVelocity1D, PDE.spatialGradient_apply, PiLp.toLp_apply, partialDeriv] using
      rightMovingSine_transport_residual p
  · intro p hp
    have hp0 : p (0 : Fin 2) = 0 := by
      simpa [initialDomain] using hp
    change Real.sin (p (1 : Fin 2) - p (0 : Fin 2)) = Real.sin (p (1 : Fin 2))
    simp [hp0]

end Space1

end

end TransportEquation
