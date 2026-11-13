/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.ClosedForm.Differential.EquationExpression
public import PDE.Symbolic.ClosedForm.Differential.Semantics

/-!
# Scalar symbolic differential equations

An equation is represented by its two differential expressions. Subtracting the right-hand side
gives a residual that can either be interpreted analytically (`analyticResidual`, or
`semanticResidual` for arbitrary functions) or lowered to a closed-form symbolic expression. The
bridge theorems `analyticResidual_eq_closedResidual_eval` and
`analyticResidual_eq_zero_of_closedResidualVanishesAt` turn a verified symbolic zero into a
theorem about the analytic residual, provided the natural domain requirements hold.
-/

@[expose] public section

namespace CAS

namespace DiffExpr

namespace Equation

/-- Interpret the residual using Lean's Euclidean derivative operators. -/
noncomputable def analyticResidual {n : Nat} {σ : Type} [Fact (0 < n)]
    (ansatz : σ → Verified.Expr (Fin n)) (x : ℝ^n) (eqn : Equation n σ) : ℝ :=
  analyticEval ansatz x eqn.residual

/-- Interpret the residual for arbitrary Lean-function ansatzes. -/
noncomputable def semanticResidual {n : Nat} {σ : Type} [Fact (0 < n)]
    (ansatz : σ → ℝ^n → ℝ) (x : ℝ^n) (eqn : Equation n σ) : ℝ :=
  semanticEval ansatz x eqn.residual

/-- The analytic residual equals the lowered residual wherever symbolic differentiation is valid. -/
theorem analyticResidual_eq_closedResidual_eval {n : Nat} {σ : Type} [Fact (0 < n)]
    (ansatz : σ → Verified.Expr (Fin n)) (x : ℝ^n) (eqn : Equation n σ)
    (h : AnalyticSideCondition ansatz x eqn.residual) :
    analyticResidual ansatz x eqn = (closedResidual ansatz eqn).eval x :=
  analyticEval_eq_lower_eval ansatz x eqn.residual h

/-- A vanishing lowered residual gives a vanishing analytic residual at every valid point. -/
theorem analyticResidual_eq_zero_of_closedResidualVanishesAt {n : Nat} {σ : Type}
    [Fact (0 < n)] {ansatz : σ → Verified.Expr (Fin n)} {eqn : Equation n σ} {x : ℝ^n}
    (hclosed : ClosedResidualVanishesAt ansatz eqn x)
    (hside : AnalyticSideCondition ansatz x eqn.residual) :
    analyticResidual ansatz x eqn = 0 := by
  rw [analyticResidual_eq_closedResidual_eval ansatz x eqn hside]
  exact hclosed

end Equation

end DiffExpr

end CAS
