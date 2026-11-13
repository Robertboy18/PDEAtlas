/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.Tactic.ConditionalRewrites
public import PDE.Symbolic.Tactic.DerivativeBridge.PDE
public meta import PDE.Symbolic.Tactic.DerivativeBridge.PDE
/-!
# Reflection of ordinary Euclidean derivative goals

A theorem-facing bridge from ordinary Mathlib syntax about
coordinate derivatives of functions `ℝ^n → ℝ` (with a literal dimension `n`)
to the checked symbolic derivative language. It accepts equalities whose one
side is

* `partialDeriv i (fun q : ℝ^n => body) p`,
* `partialDeriv i (fun q => partialDeriv j (fun r : ℝ^n => body) q) p`,
* `laplacian (fun q : ℝ^n => body) p`, or
* `fderiv ℝ (fun q : ℝ^n => body) p (EuclideanSpace.single i 1)`,

where the body is written with the coordinate projections `q 0, …, q (n - 1)`
and any binder-independent real parameters. The function may also be a named
function `ℝ^n → ℝ` after `show`, `unfold`, or `simp only`.

The body is reflected with the coordinates as the first `n` variables and the
parameters as the remaining variables of `Verified.Expr (Fin (n + k))`. The
bridge theorems of `PDE.Symbolic.Calculus.ParameterEmbeddingOperators` then compute the
analytic derivative from the executable symbolic derivative; only validity at
the evaluation point is required, also for repeated derivatives and the
Laplacian, because validity persists near a valid point. The computed value is
identified with the stated one by
`CAS.Tactic.DerivativeBridge.closeMatchingGoals`.

Users never see `Verified.Expr`: the reflected function is definitionally the
user's function, so no rewriting of the goal is needed before the theorem is
applied.
-/

public meta section

namespace CAS.Tactic.PartialDeriv

open Lean Elab Tactic Meta
open DerivativeBridge

/-- A recognised Euclidean derivative operator application. -/
inductive Operator where
  /-- `partialDeriv index function point` on `ℝ^dimension`. -/
  | coordinate (dimension : Nat) (index function point : Expr)
  /-- `partialDeriv outer (fun q => partialDeriv inner innerFunction q) point`. -/
  | second (dimension : Nat) (outer inner outerFunction innerFunction point : Expr)
  /-- `laplacian function point` on `ℝ^dimension`. -/
  | laplace (dimension : Nat) (function point : Expr)

namespace Operator

/-- The outermost differentiated function. -/
def function : Operator → Expr
  | .coordinate _ _ f _ | .second _ _ _ f _ _ | .laplace _ f _ => f

/-- The dimension of the Euclidean domain. -/
def dimension : Operator → Nat
  | .coordinate n _ _ _ | .second n _ _ _ _ _ | .laplace n _ _ => n

end Operator

/-- A recognised goal: an equality between an operator application and a stated value. -/
structure Shape where
  /-- The derivative operator application. -/
  operator : Operator
  /-- The stated value on the other side of the equality. -/
  stated : Expr
  /-- Whether the operator application is the right-hand side of the equality. -/
  reverse : Bool

private def innerPartial? (function : Expr) : Option (Expr × Expr) :=
  match function.consumeMData with
  | .lam _ _ body _ =>
      let body := body.consumeMData
      if body.isAppOfArity ``PDE.partialDeriv 7 then
        let arguments := body.getAppArgs
        if arguments[6]! == .bvar 0 && !arguments[4]!.hasLooseBVars &&
            !arguments[5]!.hasLooseBVars then
          some (arguments[4]!, arguments[5]!)
        else
          none
      else
        none
  | _ => none

/-- Recognise an ordinary Euclidean derivative operator application. -/
def operator? (expression : Expr) : MetaM (Option Operator) := do
  let expression := expression.consumeMData
  if expression.isAppOfArity ``PDE.partialDeriv 7 then
    let arguments := expression.getAppArgs
    let some dimension ← literalDimension? arguments[0]!
      | return none
    let index := arguments[4]!
    let function := arguments[5]!
    let point := arguments[6]!
    match innerPartial? function with
    | some (inner, innerFunction) =>
        return some (.second dimension index inner function innerFunction point)
    | none =>
        return some (.coordinate dimension index function point)
  if expression.isAppOfArity ``PDE.laplacian 6 then
    let arguments := expression.getAppArgs
    let some dimension ← literalDimension? arguments[0]!
      | return none
    -- The operator permits normed codomains, while this reflective backend is scalar.
    unless ← isDefEqGuarded arguments[1]! (mkConst ``Real) do
      return none
    return some (.laplace dimension arguments[4]! arguments[5]!)
  if expression.isAppOfArity ``DFunLike.coe 6 then
    let arguments := expression.getAppArgs
    let map := arguments[4]!.consumeMData
    let direction := arguments[5]!.consumeMData
    unless map.getAppFn.consumeMData.isConstOf ``fderiv do
      return none
    let mapArguments := map.getAppArgs
    unless 4 ≤ mapArguments.size && mapArguments[0]!.isConstOf ``Real do
      return none
    let some dimension := (← euclideanDimension? mapArguments[2]!).join
      | return none
    unless direction.getAppFn.consumeMData.isConstOf ``EuclideanSpace.single do
      return none
    let directionArguments := direction.getAppArgs
    unless 2 ≤ directionArguments.size do
      return none
    let one ← mkAppOptM ``OfNat.ofNat #[some (mkConst ``Real), some (mkRawNatLit 1), none]
    unless ← isDefEqGuarded directionArguments[directionArguments.size - 1]! one do
      return none
    return some
      (.coordinate dimension directionArguments[directionArguments.size - 2]!
        mapArguments[mapArguments.size - 2]! mapArguments[mapArguments.size - 1]!)
  return none

/-- Recognise the Euclidean derivative shape of a proposition, if any. -/
def shape? (target : Expr) : MetaM (Option Shape) := do
  let target := target.consumeMData
  unless target.isAppOfArity ``Eq 3 do
    return none
  let arguments := target.getAppArgs
  match ← operator? arguments[1]! with
  | some operator => return some { operator, stated := arguments[2]!, reverse := false }
  | none =>
      match ← operator? arguments[2]! with
      | some operator => return some { operator, stated := arguments[1]!, reverse := true }
      | none => return none

/-- Whether a proposition has one of the Euclidean derivative shapes. -/
def isEuclideanDerivativeGoal (target : Expr) : MetaM Bool :=
  Option.isSome <$> shape? target

/--
Expose local definitions that depend on the Euclidean argument of the differentiated
functions, together with real-valued local definitions used in the stated value, so the
goal and the reflected body share one definitional presentation.
-/
private def unfoldDependentLocalDefinitions : TacticM Unit :=
  unfoldLocalDefinitionsWhile do
    let target ← instantiateMVars (← getMainTarget)
    let some shape ← shape? target
      | return #[]
    let domain := euclideanSpace shape.operator.dimension
    let functions : Array Expr :=
      match shape.operator with
      | .second _ _ _ outer inner _ => #[outer, inner]
      | operator => #[operator.function]
    let mut definitions ← statedLocalDefinitions shape.stated
    for function in functions do
      if ← Elaboration.RealExpression.hasType function (← mkArrow domain (mkConst ``Real)) then
        definitions := definitions ++ (← dependentLocalDefinitions domain function)
    return definitions

private def ensureEuclideanFunction (dimension : Nat) (function : Expr) : MetaM Expr := do
  let function ← withTransparency .reducible <| whnf function
  let expected ← mkArrow (euclideanSpace dimension) (mkConst ``Real)
  unless ← Elaboration.RealExpression.hasType function expected do
    let functionType ← inferType function
    throwError
      "{operation} supports real-valued functions on ℝ^{dimension}; the differentiated \
       function has type{indentExpr functionType}"
  return function

private def withBody {α : Type} (dimension : Nat) (function : Expr)
    (continuation : Expr → Expr → MetaM α) : MetaM α :=
  withLocalDeclD `q (euclideanSpace dimension) fun binder ↦ do
    let body ← withTransparency .reducible <| whnf (mkApp function binder)
    unless ← Elaboration.RealExpression.hasType body (mkConst ``Real) do
      let codomain ← inferType body
      throwError
        "{operation} supports real-valued scalar functions; \
         the function codomain is{indentExpr codomain}"
    continuation binder body

/-- Assign the main goal with `proof` and close the derivative conversion goals. -/
private def finish
    (proof : Expr) (derivative : Derivative) (functionGoal? : Option MVarId)
    (valueGoal : MVarId) (evidence? : Option (TSyntax `term)) : TacticM Unit := do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let proofType ← instantiateMVars (← inferType proof)
  unless ← isDefEq proofType target do
    throwError
      "{operation} constructed a proof of{indentExpr proofType}\n\
       but the goal is{indentExpr target}"
  closeMatchingGoals operation functionGoal? (some valueGoal) derivative evidence?
  goal.assign (← instantiateMVars proof)
  replaceMainGoal []

/--
Restate the Laplacian value `∑ i, ((expr.diff i).diff i).eval ρ` as the evaluation of the single
checked expression `addList (List.ofFn fun i => (expr.diff i).diff i)`
(`Verified.Expr.eval_addList_ofFn`), so that the checked side-conditioned normalizer can
identify it with the stated value. Returns the restated derivative and the equality
`laplacian f p = folded value`, or `none` when the value does not have the expected shape.
-/
private def foldLaplacianSum (derivative : Derivative) (equality : Expr) :
    MetaM (Option (Derivative × Expr)) := do
  let value := (← instantiateMVars derivative.value).consumeMData
  unless value.isAppOfArity ``Finset.sum 5 do
    return none
  let .lam name type body info := value.appArg!.consumeMData
    | return none
  let body := body.consumeMData
  unless body.isAppOfArity ``Verified.Expr.eval 3 do
    return none
  let arguments := body.getAppArgs
  let environment := arguments[1]!
  if environment.hasLooseBVars then
    return none
  let symbolicFunction := Expr.lam name type arguments[2]! info
  let list ← mkAppM ``List.ofFn #[symbolicFunction]
  let folded ←
    mkAppM ``Verified.Expr.eval #[environment, ← mkAppM ``Verified.Expr.addList #[list]]
  let sumEquality ← mkAppM ``Verified.Expr.eval_addList_ofFn #[environment, symbolicFunction]
  let foldedEquality ← mkEqTrans equality (← mkEqSymm sumEquality)
  return some ({ derivative with value := folded }, foldedEquality)

/-- Close a conversion goal left by the Mathlib script with the square-root identities available
from the context (`ConditionalRewrites.addSquareRootFacts`) and linear arithmetic. -/
private def closeWithSquareRootFacts (goal : MVarId) : TacticM Unit := do
  let goals ← getGoals
  setGoals [goal]
  ConditionalRewrites.addSquareRootFacts
  evalTactic (← `(tactic| first | linarith | nlinarith))
  unless (← getGoals).isEmpty do
    throwError "{operation} could not close the conversion goal with the square-root identities"
  setGoals goals

/--
Assemble the proof of the operator equality as `finish` does, but identify the computed value
with the stated one by the Mathlib script followed by the square-root identities of the
context: a Laplacian of a radial function leaves a residual such as `3u - 3(√u)² = 0`, which
`(√u)² = u` under `0 < u` closes at once.
-/
private def assembleWithSquareRootFacts
    (shape : Shape) (derivative : Derivative) (equality : Expr)
    (functionGoal? : Option MVarId) : TacticM Unit := do
  let valueGoal ← mkFreshExprSyntheticOpaqueMVar (← mkEq derivative.value shape.stated)
  let proof ← mkEqTrans equality valueGoal
  let proof ← if shape.reverse then mkEqSymm proof else pure proof
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  unless ← isDefEq (← inferType proof) target do
    throwError "{operation} constructed a proof of a different statement"
  let remaining ←
    mathlibCleanup (← unfoldEvaluation (functionGoal?.toList ++ [valueGoal.mvarId!]))
  for remainingGoal in remaining do
    closeWithSquareRootFacts remainingGoal
  let proof ← instantiateMVars proof
  if proof.hasMVar ∨ proof.hasSorry then
    throwError "{operation} produced incomplete derivative identification evidence"
  goal.assign proof
  replaceMainGoal []

private def closeShape (shape : Shape) (evidence? : Option (TSyntax `term)) : TacticM Unit := do
  let dimension := shape.operator.dimension
  let (derivative, function, predicate) ←
    match shape.operator with
    | .coordinate _ index function point => do
        let function ← ensureEuclideanFunction dimension function
        let derivative ← withBody dimension function fun binder body ↦
          partialDerivative operation binder point dimension index body evidence?
        pure (derivative, function, fun (g : Expr) ↦ do
          mkEq (← mkAppM ``PDE.partialDeriv #[index, g, point]) derivative.value)
    | .second _ outer inner outerFunction innerFunction point => do
        let innerFunction ← ensureEuclideanFunction dimension innerFunction
        let derivative ← withBody dimension innerFunction fun binder body ↦
          secondPartialDerivative operation binder point dimension outer inner body evidence?
        pure (derivative, outerFunction, fun (g : Expr) ↦ do
          mkEq (← mkAppM ``PDE.partialDeriv #[outer, g, point]) derivative.value)
    | .laplace _ function point => do
        let function ← ensureEuclideanFunction dimension function
        let derivative ← withBody dimension function fun binder body ↦
          laplacianDerivative operation binder point dimension body evidence?
        pure (derivative, function, fun (g : Expr) ↦ do
          mkEq (← mkAppM ``PDE.laplacian #[g, point]) derivative.value)
  let (equality, functionGoal?) ← transportToFunction derivative function predicate
  let assemble (derivative : Derivative) (equality : Expr) : TacticM Unit := do
    let valueGoal ← mkFreshExprSyntheticOpaqueMVar (← mkEq derivative.value shape.stated)
    let proof ← mkEqTrans equality valueGoal
    let proof ← if shape.reverse then mkEqSymm proof else pure proof
    finish proof derivative functionGoal? valueGoal.mvarId! evidence?
  match shape.operator with
  | .laplace .. =>
      -- The Laplacian value is a finite sum of evaluations. When the Mathlib script does not
      -- identify it with the stated value, the residual is retried with the square-root
      -- identities the context provides (`(√u)² = u` under `0 < u`), and finally the sum is
      -- folded into the evaluation of one checked expression for the checked normalizer.
      let saved ← saveState
      try
        assemble derivative equality
      catch error =>
        saved.restore
        try
          assembleWithSquareRootFacts shape derivative equality functionGoal?
        catch _ =>
          saved.restore
          let some (folded, foldedEquality) ← foldLaplacianSum derivative equality
            | throw error
          assemble folded foldedEquality
  | _ => assemble derivative equality

/--
Close an equality whose one side is a coordinate derivative operator applied to an
ordinary function `ℝ^n → ℝ` with literal `n`: `partialDeriv`, a repeated
`partialDeriv`, `laplacian`, or `fderiv ℝ f p (EuclideanSpace.single i 1)`.
-/
def close (evidence? : Option (TSyntax `term) := none) : TacticM Unit := do
  unfoldDependentLocalDefinitions
  exposeCheckedExpressions operation
  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let some shape ← shape? target
      | throwError
          "{operation} expected an equality with an ordinary `partialDeriv`, `laplacian`, or \
           `fderiv ℝ f p (EuclideanSpace.single i 1)` application on ℝ^n with a literal \
           dimension"
    closeShape shape evidence?

end CAS.Tactic.PartialDeriv
