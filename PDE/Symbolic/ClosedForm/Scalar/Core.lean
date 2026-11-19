/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Symbolic.ClosedForm.Differential.Equation
public import CAS.ClosedForm.Scalar.Expression

/-!
# Scalar symbolic residuals

The analytic reading of the scalar zero test of `CAS.ClosedForm.Scalar.Expression`.
There the unknown type is `Unknown := PUnit`, so an equation `DiffExpr.Equation n Unknown` has a
single field `u`, an ansatz is a single closed form, and `Scalar.check eqn candidate` is the
executable zero test of the residual `lhs - rhs` after substituting the candidate and
differentiating symbolically.

## Main results

* `CheckedResidual.analyticResidual_eq_zero_of_normalized_eq_zero`: if the normalized residual is
  literally `0`, the analytic residual (computed with the library's Euclidean `partialDeriv` and
  `laplacian`) vanishes wherever both the normalizer's denominator conditions and the
  differential side conditions hold.
* `CheckedResidual.analyticResidual_eq_zero_of_normalized_eq_zero_of_nonzero_eq_nil`: the same
  with the denominator hypothesis replaced by `nonzero = []`.
* `Scalar.semanticResidual`: the residual of a scalar equation under an arbitrary function
  `ℝ^n → ℝ`.

## Implementation notes

Two independent families of side conditions appear. `Verified.Expr.Alg.SideHolds` records the
denominators the rational normalizer cancelled, and `DiffExpr.AnalyticSideCondition` records
the points at which the symbolic derivative is known to equal the Euclidean one. A closed-form
candidate is a solution at a point only when both hold there.
-/

@[expose] public section

namespace CAS

open scoped BigOperators

namespace Scalar

namespace CheckedResidual

/-- A zero normalized residual gives a zero analytic residual under its domain conditions. -/
theorem analyticResidual_eq_zero_of_normalized_eq_zero
    {n : Nat} [Fact (0 < n)]
    (eqn : DiffExpr.Equation n Unknown) (candidate : Verified.Expr (Fin n))
    (x : ℝ^n)
    (hsideNorm :
      Verified.Expr.Alg.SideHolds x (check eqn candidate).nonzero)
    (hanalytic : DiffExpr.AnalyticSideCondition (ansatz candidate) x eqn.residual)
    (hzero : (check eqn candidate).expr = 0) :
    DiffExpr.Equation.analyticResidual (ansatz candidate) x eqn = 0 := by
  rw [DiffExpr.Equation.analyticResidual_eq_closedResidual_eval (ansatz candidate) x eqn hanalytic]
  change (residual eqn candidate).eval x = 0
  exact residual_eval_eq_zero_of_normalized_eq_zero
    (eqn := eqn) (candidate := candidate) (x := x) hsideNorm hzero

/-- Pointwise analytic theorem helper when the stronger normalizer emits no denominator
side conditions. -/
theorem analyticResidual_eq_zero_of_normalized_eq_zero_of_nonzero_eq_nil
    {n : Nat} [Fact (0 < n)]
    (eqn : DiffExpr.Equation n Unknown) (candidate : Verified.Expr (Fin n))
    (x : ℝ^n)
    (hsideNil : (check eqn candidate).nonzero = [])
    (hanalytic : DiffExpr.AnalyticSideCondition (ansatz candidate) x eqn.residual)
    (hzero : (check eqn candidate).expr = 0) :
    DiffExpr.Equation.analyticResidual (ansatz candidate) x eqn = 0 :=
  analyticResidual_eq_zero_of_normalized_eq_zero
    (eqn := eqn) (candidate := candidate) (x := x)
    (Verified.Expr.Alg.ZeroCheck.sideHolds_of_nonzero_eq_nil
      (check eqn candidate) (fun i : Fin n ↦ x i) hsideNil)
    hanalytic hzero

end CheckedResidual

/-- Semantic residual of a scalar equation under an arbitrary Lean-function candidate. -/
noncomputable def semanticResidual {n : Nat} [Fact (0 < n)]
    (eqn : DiffExpr.Equation n Unknown) (candidate : ℝ^n → ℝ)
    (x : ℝ^n) : ℝ :=
  DiffExpr.Equation.semanticResidual (semanticAnsatz candidate) x eqn


end Scalar

end CAS
