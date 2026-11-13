/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Symbolic.Heat.Equations
public import PDE.Symbolic.ClosedForm.Tactic.Residual
public import CAS.ExactTactic

/-!
# A separated heat mode

SymLean's `cas` tactic proves that `u(t,x) = exp(-t) sin(x)` has zero symbolic heat residual
(`separatedHeatMode1D_closed_residual_eq_zero`). The derivative-domain conditions hold everywhere,
so the identity transfers to ordinary Euclidean derivatives at every point
(`separatedHeatMode1D_analytic_residual_eq_zero`).

The mode has the product form (2) of Evans's §4.1.1, Example 1, with `v(t) = e^{-t}` and
`w(x) = sin x`, which satisfy (4) and (5) with `μ = -1`. On `U = (0, π)` it is the solution (6) for
the first Dirichlet eigenvalue `λ = 1`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.1.1, Example 1, (2)-(6), pp. 168-169.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HeatEquation.Symbolic.Space1

open CAS
open CAS.Euclid2

noncomputable section

/--
The elementary separated heat mode `u(t,x)=exp(-t) sin(x)`.
Symbolic `x` is time and symbolic `y` is space, matching
`HeatEquation.Symbolic.Space1.heat1DEquation`.
-/
def separatedHeatMode1DAnsatz : Verified.Expr (Fin 2) :=
  .exp (-(x : Verified.Expr (Fin 2))) *
    .sin (y : Verified.Expr (Fin 2))

/-- The symbolic heat residual of the separated mode. -/
def separatedHeatMode1DResidual : Verified.Expr (Fin 2) :=
  Scalar.residual
    HeatEquation.Symbolic.Space1.heat1DEquation
    separatedHeatMode1DAnsatz

/-- The checked closed-form heat residual is identically zero. -/
theorem separatedHeatMode1D_closed_residual_eq_zero :
    Set.EqOn (Exact.exprFn separatedHeatMode1DResidual)
      Exact.zeroFn Set.univ := by
  cas

/-- Analytic derivative-domain side conditions for the separated heat mode. -/
private theorem separatedHeatMode1D_analytic_side_condition
    (p : ℝ^2) (_hp : p ∈ Set.univ) :
    DiffExpr.AnalyticSideCondition
      (Scalar.ansatz separatedHeatMode1DAnsatz)
      p
      HeatEquation.Symbolic.Space1.heat1DEquation.residual := by
  symbolic_residual

/-- Analytic Euclidean residual version of the separated heat check. -/
theorem separatedHeatMode1D_analytic_residual_eq_zero :
    ∀ p, p ∈ Set.univ →
      DiffExpr.Equation.analyticResidual
        (Scalar.ansatz separatedHeatMode1DAnsatz)
        p
        HeatEquation.Symbolic.Space1.heat1DEquation = 0 := by
  intro p hp
  have hclosed :
      (Scalar.residual
        HeatEquation.Symbolic.Space1.heat1DEquation
        separatedHeatMode1DAnsatz).eval p = 0 := by
    simpa [separatedHeatMode1DResidual, Exact.exprFn, Exact.zeroFn] using
      separatedHeatMode1D_closed_residual_eq_zero hp
  exact DiffExpr.Equation.analyticResidual_eq_zero_of_closedResidualVanishesAt
    hclosed (separatedHeatMode1D_analytic_side_condition p hp)

end

end HeatEquation.Symbolic.Space1
