/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Symbolic.ClosedForm.Tactic.Residual
public import CAS.ExactTactic

/-!
# Symbolic Helmholtz solutions

The one-dimensional Helmholtz equation `u_xx + u = 0` has the eigenmode `u = sin x`. We
check that fact through the symbolic pipeline. The equation is a `DiffExpr.Equation` in two
coordinates, of which only the first is differentiated (the second is an inert parameter); the
ansatz `sin x` is a `Verified.Expr`; the compiled residual is closed by the `cas` tactic; and the
analytic residual theorem transports the symbolic identity to a statement about Euclidean
coordinate derivatives.

## Main results

* `helmholtzSine_satisfies_helmholtz`: the compiled symbolic residual of `sin x` vanishes.
* `helmholtzSine_analytic_residual_zero`: the analytic residual vanishes at every point.
* `helmholtzSine_secondPartial_plus_self_zero`: `∂₀∂₀ u + u = 0` for `u(p) = sin (p 0)`, stated
  with `partialDeriv`.
-/

@[expose] public section

namespace LaplacianEquation.Symbolic

open CAS
open CAS.Euclid2
open scoped CAS

noncomputable section

/-! ## One-dimensional Helmholtz eigenmode -/

/-- The one-dimensional symbolic Helmholtz equation `u_xx + u = 0`. -/
def helmholtzSineEquation : DiffExpr.Equation 2 Scalar.Unknown :=
  Scalar.helmholtz1D x (1 : Verified.Expr (Fin 2)) 0

/-- The elementary Helmholtz eigenmode `u(x,y)=sin(x)`.

Only the first coordinate is used as the one-dimensional spatial variable; the second coordinate is
an inert parameter. -/
def helmholtzSineAnsatz : Verified.Expr (Fin 2) :=
  .sin x

/-- The symbolic residual of `sin(x)` for the equation `u_xx + u = 0`. -/
def helmholtzSineResidual : Verified.Expr (Fin 2) :=
  Scalar.residual helmholtzSineEquation helmholtzSineAnsatz

/-- The sine mode satisfies the one-dimensional Helmholtz equation. -/
theorem helmholtzSine_satisfies_helmholtz :
    Set.EqOn (Exact.exprFn helmholtzSineResidual) Exact.zeroFn Set.univ := by
  cas

private theorem helmholtzSine_analytic_side_condition
    (p : ℝ^2) (_hp : p ∈ Set.univ) :
    DiffExpr.AnalyticSideCondition
      (Scalar.ansatz helmholtzSineAnsatz) p helmholtzSineEquation.residual := by
  symbolic_residual

/-- The analytic Helmholtz residual of the sine mode vanishes. -/
theorem helmholtzSine_analytic_residual_zero :
    ∀ p, p ∈ Set.univ →
      DiffExpr.Equation.analyticResidual
        (Scalar.ansatz helmholtzSineAnsatz) p helmholtzSineEquation = 0 := by
  intro p hp
  exact DiffExpr.Equation.analyticResidual_eq_zero_of_closedResidualVanishesAt
    (by
      change helmholtzSineResidual.eval p = 0
      exact helmholtzSine_satisfies_helmholtz hp)
    (helmholtzSine_analytic_side_condition p hp)

/--
Euclidean second-derivative form of the Helmholtz sine check:
`u(x,y)=sin(x)` satisfies `u_xx + u = 0`.
-/
theorem helmholtzSine_secondPartial_plus_self_zero
    (p : ℝ^2) :
    (∂[(0 : Fin 2)]
        (fun y : ℝ^2 ↦
          (∂[(0 : Fin 2)]
            (fun q : ℝ^2 ↦ helmholtzSineAnsatz.eval q)) y))
        p +
      helmholtzSineAnsatz.eval p = 0 := by
  have h := helmholtzSine_analytic_residual_zero p trivial
  have hxx :
      (∂[(0 : Fin 2)]
          (fun y : ℝ^2 ↦
            (∂[(0 : Fin 2)]
              (fun q : ℝ^2 ↦ helmholtzSineAnsatz.eval q)) y))
          p =
        (∂[(0 : Fin 2)]
          (fun y : ℝ^2 ↦ (helmholtzSineAnsatz.diff 0).eval y))
          p :=
    Verified.Expr.secondPartial_eval_eq_partialDeriv_diff
      helmholtzSineAnsatz p (0 : Fin 2) (by symbolic_assumptions)
  rw [hxx]
  simpa [helmholtzSineEquation, Scalar.helmholtz1D, Scalar.helmholtzSpatial,
    Scalar.spatialLaplacian_cons, Scalar.spatialLaplacian_nil,
    DiffExpr.Equation.analyticResidual, DiffExpr.analyticEval, DiffExpr.Equation.residual,
    Scalar.ansatz, Scalar.u, DiffExpr.D2, DiffExpr.D, DiffExpr.lower,
    Verified.Expr.eval] using h
end

end LaplacianEquation.Symbolic
