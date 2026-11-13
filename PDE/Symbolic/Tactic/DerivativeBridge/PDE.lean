/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Symbolic.Calculus.ParameterEmbeddingOperators
public meta import PDE.Symbolic.Calculus.ParameterEmbeddingOperators
public import CAS.Tactic.DerivativeBridge
public meta import CAS.Tactic.DerivativeBridge

/-!
# Proof-producing PDE derivative bridges

For the body of an ordinary function `ℝ^n → ℝ`, reflected with the coordinates first and the
binder-independent parameters after them, these functions prove the value of a coordinate
derivative from the bridge theorems of `PDE.Symbolic.Calculus.ParameterEmbeddingOperators`:

* `partialDerivative`: `partialDeriv i f p = D`, by `Verified.Expr.partialDeriv_eval_paramEmbed_eq`;
* `secondPartialDerivative`: `partialDeriv i (partialDeriv j f) p = D`, by
  `Verified.Expr.partialDeriv_partialDeriv_eval_paramEmbed_eq`;
* `laplacianDerivative`: `laplacian f p = D`, by `Verified.Expr.laplacian_eval_paramEmbed_eq`.

The validity hypotheses of each theorem are discharged by `closeValidity`
(`symbolic_assumptions`, or the `using` evidence when it is supplied). Scalar differentiation
imports only the shared bridge, not this module.
-/

public meta section

namespace CAS.Tactic.DerivativeBridge

open Lean Elab Tactic Meta

private def embeddedIndex
    (dimension parameterCount : Nat) (index : Expr) : MetaM (Expr × Expr) := do
  let embedded ←
    mkAppOptM ``Fin.castAdd
      #[some (toExpr dimension), some (toExpr parameterCount), some index]
  let valueProof ← mkEqRefl (← mkAppM ``Fin.val #[index])
  return (embedded, valueProof)

private def euclideanDerivative
    (operation : String) (binder point : Expr) (dimension : Nat) (body : Expr)
    (build : RealExpression.EmbeddedReflection → MetaM Expr) : MetaM Derivative := do
  let coordinates ← coordinateTerms binder dimension
  let pointCoordinates ← coordinateTerms point dimension
  let reflection ← RealExpression.reflectEmbedded operation #[binder] coordinates body
  let proof ← build reflection
  let proofType ← instantiateMVars (← inferType proof)
  let some (_, lhs, value) := proofType.eq?
    | throwError "{operation} internal error: the derivative theorem is not an equality"
  let function :=
    match lhs.getAppFn.constName? with
    | some ``PDE.partialDeriv =>
        let arguments := lhs.getAppArgs
        arguments[5]!
    | _ =>
        let arguments := lhs.getAppArgs
        arguments[arguments.size - 2]!
  return {
    proof
    function
    value
    pointCoordinates
    parameters := reflection.coordinates.extract dimension reflection.coordinates.size
  }

/--
Prove `partialDeriv i (fun q => expr.eval (paramEmbed c q)) p = D` for the body of an
ordinary function `ℝ^n → ℝ` given by `body` in terms of the Euclidean `binder`.
-/
def partialDerivative
    (operation : String) (binder point : Expr) (dimension : Nat) (index body : Expr)
    (evidence? : Option (TSyntax `term)) : MetaM Derivative :=
  euclideanDerivative operation binder point dimension body
    fun reflection ↦ do
      let k := reflection.parameterCount
      let (embeddedIndex, indexValue) ← embeddedIndex dimension k index
      applyBridge operation ``Verified.Expr.partialDeriv_eval_paramEmbed_eq
        #[some (toExpr dimension), some (toExpr k), some reflection.expression,
          some reflection.parameters, some point, some index, some embeddedIndex,
          some indexValue] 1 evidence?

/--
Prove `partialDeriv i (fun q => partialDeriv j (fun r => expr.eval (paramEmbed c r)) q) p = D`
for the body of an ordinary function `ℝ^n → ℝ`.
-/
def secondPartialDerivative
    (operation : String) (binder point : Expr) (dimension : Nat)
    (outerIndex innerIndex body : Expr)
    (evidence? : Option (TSyntax `term)) : MetaM Derivative :=
  euclideanDerivative operation binder point dimension body
    fun reflection ↦ do
      let k := reflection.parameterCount
      let (outerEmbedded, outerValue) ← embeddedIndex dimension k outerIndex
      let (innerEmbedded, innerValue) ← embeddedIndex dimension k innerIndex
      applyBridge operation ``Verified.Expr.partialDeriv_partialDeriv_eval_paramEmbed_eq
        #[some (toExpr dimension), some (toExpr k), some reflection.expression,
          some reflection.parameters, some point, some outerIndex, some innerIndex,
          some outerEmbedded, some innerEmbedded, some outerValue, some innerValue]
        2 evidence?

/-- Prove `laplacian (fun q => expr.eval (paramEmbed c q)) p = D` for the body of an ordinary
function `ℝ^n → ℝ`. -/
def laplacianDerivative
    (operation : String) (binder point : Expr) (dimension : Nat) (body : Expr)
    (evidence? : Option (TSyntax `term)) : MetaM Derivative :=
  euclideanDerivative operation binder point dimension body
    fun reflection ↦ do
      let k := reflection.parameterCount
      applyBridge operation ``Verified.Expr.laplacian_eval_paramEmbed_eq
        #[some (toExpr dimension), some (toExpr k), some reflection.expression,
          some reflection.parameters, some point] 2 evidence?

end CAS.Tactic.DerivativeBridge
