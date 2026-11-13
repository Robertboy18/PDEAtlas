/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Symbolic.Calculus.Operators
public meta import PDE.Symbolic.Calculus.Operators
public import PDE.Symbolic.Tactic.DerivativeRewrite.PDE
public meta import PDE.Symbolic.Tactic.DerivativeRewrite.PDE
public meta import CAS.Tactic.ProofCarrier

/-!
# Explicit registration of checked PDE differentiation

Importing this module together with `CAS.ExactTactic` registers the derivative
backend `backend` for `cas`. It proves goals about coordinate derivatives, repeated
derivatives, Laplacians, and `fderiv` applied to a direction, rewrites such derivatives
inside residual identities, and closes reflected goals by rewriting with the bridges
`Verified.Expr.partialDeriv_eval_eq`, `mixedSecondPartial_eval_eq_partialDeriv_diff`,
`deriv_eval_add_smul_single_eq_diff_eval`, and `fderiv_eval_apply_eq_sum_closedPartial`.
Either import order works. Importing the operator definitions alone registers no backend.
The differentiated functions are maps `ℝ^n → ℝ` with a literal dimension `n`. Bare `cas`
reaches the same backend for these goals.

The computer algebra system itself (`cas`, `cas_nf`, the `#cas` commands, and the `cega`
certificates) is the separate package SymLean, library `CAS`. The modules under `PDE.Symbolic` add
LeanPDE's PDE routes to it, and importing `CAS` alone registers none of them.

## Implementation notes

The declarations of the modules under `PDE.Symbolic` live in the `CAS` namespaces of SymLean
that they extend (`CAS.Verified.Expr`, `CAS.Tactic`, `CAS.Command`, ...), not under `PDE`, so
dot notation on the SymLean types reaches them.
-/

public meta section

namespace CAS.Tactic.PDEDerivatives

open Lean Elab Tactic Meta
open CAS

private def closeReflected
    (valid? : Option (TSyntax `term)) : TacticM Unit := do
  discard <| ProofCarrier.runClosingMainGoal
      "checked symbolic differentiation" do
    let solveValidity : TSyntax `tactic ←
      `(tactic| symbolic_assumptions)
    let rewriteTactic ←
      match valid? with
      | none =>
          `(tactic|
            first
              | rw [Verified.Expr.deriv_eval_add_smul_single_eq_diff_eval
                  (h := by $solveValidity:tactic)]
              | rw [Verified.Expr.fderiv_eval_apply_eq_sum_closedPartial
                  (h := by $solveValidity:tactic)]
              | repeat
                  conv_lhs =>
                    pattern (partialDeriv _ (fun y =>
                      partialDeriv _
                        (fun z => Verified.Expr.eval _ z) y) _)
                    rw [Verified.Expr.mixedSecondPartial_eval_eq_partialDeriv_diff
                      (hvalid := by $solveValidity:tactic)]
                rw [Verified.Expr.partialDeriv_eval_eq
                  (h := by $solveValidity:tactic)]
                repeat first
                  | rw [Verified.Expr.partialDeriv_eval_eq
                      (h := by $solveValidity:tactic)])
      | some valid =>
          -- `valid` states validity at the point or at every point; the mixed-partial bridge
          -- uses it at the point. Validity of the symbolic first derivative is discharged
          -- separately.
          `(tactic|
            first
              | repeat
                  conv_lhs =>
                    pattern (partialDeriv _ (fun y =>
                      partialDeriv _
                        (fun z => Verified.Expr.eval _ z) y) _)
                    rw [Verified.Expr.mixedSecondPartial_eval_eq_partialDeriv_diff
                      (hvalid := by first | exact $valid | exact $valid _)]
                rw [Verified.Expr.partialDeriv_eval_eq
                  (h := by $solveValidity:tactic)]
                repeat first
                  | rw [Verified.Expr.partialDeriv_eval_eq
                      (h := by $solveValidity:tactic)]
              | rw [Verified.Expr.partialDeriv_eval_eq
                  (h := $valid)]
                repeat first
                  | rw [Verified.Expr.partialDeriv_eval_eq
                      (h := $valid)]
              | rw [Verified.Expr.deriv_eval_add_smul_single_eq_diff_eval
                  (h := $valid)]
              | rw [Verified.Expr.fderiv_eval_apply_eq_sum_closedPartial
                  (h := $valid)])
    evalTactic rewriteTactic
    evalTactic (← `(tactic|
      dsimp [Verified.Expr.diff, Verified.Expr.eval, Verified.Expr.closedPartial,
        Verified.Expr.simplify, EuclideanSpace.single]))
    evalTactic (← `(tactic|
      simp [EuclideanSpace.single, PiLp.single_apply] <;> ring))

/-- Register recognition and checked proof production for the PDE derivative frontend. -/
@[cas_derivative_backend]
def backend : DerivativeRegistry.Backend
  | .isGoal target => return .matches (← PartialDeriv.isEuclideanDerivativeGoal target)
  | .isTerm term => return .matches (← PartialDeriv.operator? term).isSome
  | .close evidence? => do
      PartialDeriv.close evidence?
      return .closed
  | .equation term evidence? => do
      let some operator ← PartialDeriv.operator? term
        | throwError "unrecognized PDE derivative subterm{indentExpr term}"
      return .equation (← DerivativeRewrite.euclideanEquation term operator evidence?)
  | .reflected evidence? => do
      closeReflected evidence?
      return .closed

end CAS.Tactic.PDEDerivatives
