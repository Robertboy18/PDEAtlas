/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.SpaceTime.Gradient.Basic
public import PDE.Problem.Equation.Basic

/-!
# Hamilton–Jacobi equations

We define the residual form of the nonautonomous Hamilton–Jacobi equation

`u_t + H(Dₓu, t, x) = 0`

on a spacetime domain. Time is the coordinate `0` of `ℝ^(n + 1)`. Evans writes the equation
with a Hamiltonian `H(p, x)` independent of time, as (62) in Example 6 of §3.2.5(c).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.2.5(c), Example 6, equation (62).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (PDEProblem spatialGradient)

namespace NonlinearFirstOrder

open PDE.Common

variable {n : ℕ}

/-- Hamilton–Jacobi equation on spacetime: `u_t + H(Dₓu, t, x) = 0`. -/
noncomputable def hamiltonJacobiEquation
    (H : ℝ^n → ℝ → ℝ^n → ℝ)
    (U : Set (ℝ^(n + 1))) :
    PDEProblem (ℝ^(n + 1)) ℝ :=
  let : Fact (0 < n + 1) := ⟨Nat.succ_pos n⟩
  { eqns := [
      { Output := ℝ
        operator := fun u xt ↦
          (∂[0] u) xt +
            H (spatialGradient (n := n) u xt) (xt 0) (spatialPartCLM n xt)
        rhs := fun _ ↦ 0
        domain := U }
    ]
    sideConditions := [] }

end NonlinearFirstOrder
