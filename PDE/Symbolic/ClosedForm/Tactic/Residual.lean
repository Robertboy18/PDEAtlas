/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.ClosedForm.Tactic.Algebra
public import CAS.ClosedForm.Tactic.Reduction
public import PDE.Symbolic.ClosedForm.Differential.Equation

/-!
# Symbolic residual automation

The internal residual solver used by the PDE bridge files for analytic residuals and exact
closed-form goals. Analytic residual goals are rewritten to the closed symbolic residual, whose
zero test runs through `symbolic_alg_zero_side`; every analytic domain obligation is discharged by
`symbolic_assumptions`. `symbolic_laplacian_zero` first rewrites analytic Laplacian goals to the
symbolic closed Laplacian with `closedLaplacian_eval_eq_laplacian`, whose `ValidAt` hypotheses
become ordinary side goals.
-/

public meta section

namespace CAS

open scoped BigOperators
open Lean Elab Tactic

/-- Prove analytic Euclidean-Laplacian goals for functions denoted by symbolic expressions.

This tactic targets goals of the shape `laplacian (fun x => expr.eval x) p = 0`. It rewrites the
analytic Laplacian to the verified symbolic closed Laplacian, then calls the symbolic zero tactic.
The `ValidAt` derivative side conditions are solved from the local context by
`symbolic_assumptions`. -/
syntax (name := symbolicLaplacianZero) "symbolic_laplacian_zero" : tactic

macro_rules
  | `(tactic| symbolic_laplacian_zero) =>
      `(tactic|
        rw [← Verified.Expr.closedLaplacian_eval_eq_laplacian] <;>
          first
            | symbolic_alg_zero_side
            | symbolic_assumptions)

/-- Combine the internal residual, equality, and side-condition solvers.

Ordinary theorem proofs should invoke the public `cas` tactic. -/
syntax (name := symbolicResidual) "symbolic_residual" : tactic

macro_rules
  | `(tactic| symbolic_residual) =>
      `(tactic|
        first
          | rw [DiffExpr.Equation.analyticResidual_eq_closedResidual_eval] <;>
              first
                | symbolic_alg_zero_side
                | symbolic_assumptions
          | symbolic_laplacian_zero
          | symbolic_assumptions
          | symbolic_eq
          | symbolic_alg_zero_side
          | symbolic_simp)

end CAS
