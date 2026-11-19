/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.Tactic.DerivativeRewrite
public meta import CAS.Tactic.DerivativeRewrite
public import PDE.Symbolic.Tactic.PartialDeriv
public meta import PDE.Symbolic.Tactic.PartialDeriv

/-!
# Checked PDE derivative equations for residual rewriting

`euclideanEquation` proves `partialDeriv i f p = D`, `partialDeriv i (partialDeriv j f) p = D`
or `laplacian f p = D` for a subterm of an ordinary residual identity, where `f : ℝ^n → ℝ` is
explicit and `D` is its checked closed form. The equation is the one `cas` proves
for the same subterm (`PDE.Symbolic.Tactic.DerivativeBridge.PDE`). The rewriter of
`CAS.Tactic.DerivativeRewrite` collects scalar and Euclidean subterms and rewrites
them together, or not at all.
-/

public meta section

namespace CAS.Tactic.DerivativeRewrite

open Lean Elab Tactic Meta
open DerivativeBridge

/-- Run `continuation` on the body of an ordinary function `ℝ^dimension → ℝ`. -/
private def withEuclideanBody {α : Type} (dimension : Nat) (function : Expr)
    (continuation : Expr → Expr → MetaM α) : MetaM α := do
  let domain := euclideanSpace dimension
  let real := mkConst ``Real
  unless ← Elaboration.RealExpression.hasType function (← mkArrow domain real) do
    let functionType ← inferType function
    throwError
      "{operation} rewrites derivatives of real-valued functions on ℝ^{dimension}; the \
       differentiated function has type{indentExpr functionType}"
  withLocalDeclD `q domain fun binder ↦ do
    let body ← withTransparency .reducible <| whnf (mkApp function binder)
    unless ← Elaboration.RealExpression.hasType body real do
      let codomain ← inferType body
      throwError
        "{operation} rewrites real-valued derivatives; the function codomain is\
         {indentExpr codomain}"
    continuation binder body

/-- The equation `operator = closedForm` for an ordinary Euclidean derivative operator. -/
def euclideanEquation
    (term : Expr) (operator : PartialDeriv.Operator) (evidence? : Option (TSyntax `term)) :
    TacticM Expr := do
  let dimension := operator.dimension
  let (derivative, function, predicate) ←
    match operator with
    | .coordinate _ index function point => do
        let function ← withTransparency .reducible <| whnf function
        let derivative ← withEuclideanBody dimension function fun binder body ↦
          partialDerivative operation binder point dimension index body evidence?
        pure (derivative, function, fun (g : Expr) ↦ do
          mkEq (← mkAppM ``PDE.partialDeriv #[index, g, point]) derivative.value)
    | .second _ outer inner outerFunction innerFunction point => do
        let innerFunction ← withTransparency .reducible <| whnf innerFunction
        let derivative ← withEuclideanBody dimension innerFunction fun binder body ↦
          secondPartialDerivative operation binder point dimension outer inner body evidence?
        pure (derivative, outerFunction, fun (g : Expr) ↦ do
          mkEq (← mkAppM ``PDE.partialDeriv #[outer, g, point]) derivative.value)
    | .laplace _ function point => do
        let function ← withTransparency .reducible <| whnf function
        let derivative ← withEuclideanBody dimension function fun binder body ↦
          laplacianDerivative operation binder point dimension body evidence?
        pure (derivative, function, fun (g : Expr) ↦ do
          mkEq (← mkAppM ``PDE.laplacian #[g, point]) derivative.value)
  let (equation, functionGoal?) ← transportToFunction derivative function predicate
  closeFunctionGoal functionGoal?
  finishEquation term equation

end CAS.Tactic.DerivativeRewrite
