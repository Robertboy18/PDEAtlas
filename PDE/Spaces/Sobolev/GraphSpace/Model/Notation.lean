/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Model.Definitions

/-!
# Notation for scalar Sobolev spaces

With `open scoped Sobolev`, write `W^{k,p}(Ω)` for the scalar weak-derivative
graph space. The domain determines the spatial dimension. The exponent is an
extended nonnegative real, so the same notation includes `p = ∞`.
On the whole space, write `W^{k,p}(ℝ^n)`.

The notation only abbreviates the space. Its usual Sobolev interpretation
requires an open domain, and its Banach-space structure requires `1 ≤ p`.
-/

@[expose] public section

/-- Scalar Sobolev space, with its dimension inferred from the domain. -/
scoped[Sobolev] notation "W^{" k "," p "}(" Ω ")" =>
  SobolevSpace.GraphSpace.WkpSpaceOn _ k p Ω

/-- Scalar Sobolev space on a bundled domain, using its underlying set. -/
scoped[Sobolev] notation "W^{" k "," p "}(" Ω ")" =>
  SobolevSpace.GraphSpace.WkpSpaceOn _ k p (SetLike.coe Ω)

/-- Scalar Sobolev space on the whole Euclidean space. -/
scoped[Sobolev] notation "W^{" k "," p "}(" "ℝ^" n ")" =>
  SobolevSpace.GraphSpace.WkpSpace n k p

public meta section

namespace Sobolev

open Lean PrettyPrinter.Delaborator SubExpr

/-- Retain the qualified space application when its notation would lose information. -/
def delabSpaceApp : Delab := do
  delabAppCore (← getExpr).getAppNumArgs (fun explicit ↦ do
    let head ← withOptionAtCurrPos `pp.fullNames true delabConst
    if explicit && !head.raw.isOfKind ``Lean.Parser.Term.explicit then
      `(@$head)
    else
      pure head) (unexpand := false)

/-- Respect explicit arguments requested by the pretty-printer's type analysis. -/
def guardSpaceNotation (arity : Nat) : DelabM Unit := do
  guard <| (← getExpr).getAppNumArgs == arity
  guard <| ← getPPOption getPPNotation
  guard <| !(← getPPOption getPPExplicit) && !(← getPPOption getPPUniverses)
  guard <| !(← withBoundedAppFn arity <|
    withMDatasOptions <| getPPOption getPPAnalysisBlockImplicit)
  for i in [:arity] do
    guard <| !(← withNaryArg i <| getPPOption getPPAnalysisNamedArg)

/-- The fractional scope uses the same text for a different Sobolev model. -/
def guardIntegerSobolevScope : DelabM Unit := do
  let state :: _ := (delabAttribute.ext.ext.getState (← getEnv)).stateStack | failure
  guard <| state.activeScopes.contains `Sobolev
  guard <| !state.activeScopes.contains `FractionalSobolev

/-- Omit an underlying-set coercion, retaining the dimension of anonymous domains. -/
def delabSpaceDomain : Delab := do
  let domain : Delab := do
    let stx ← delab
    if (← getExpr).isFVar then return stx
    let type ← withType delab
    `(($stx : $type))
  if (← getExpr).isAppOfArity ``SetLike.coe 4 then
    withAppArg domain
  else
    domain

/-- Select one formatting branch of overlapping notations with the same printed text.
The formatter cannot retain their `choice` node inside a binder. -/
def selectSpaceNotation (stx : Term) : Term :=
  ⟨if stx.raw.isOfKind choiceKind then stx.raw[0] else stx.raw⟩

/-- Display the scalar graph without changing to the Banach-valued model. -/
@[scoped app_delab SobolevSpace.GraphSpace.WkpSpaceOn]
def delabScalarWkpSpaceOn : Delab := (do
  guardSpaceNotation 4
  guardIntegerSobolevScope
  let k ← withNaryArg 1 delab
  let p ← withNaryArg 2 delab
  let Ω ← withNaryArg 3 delabSpaceDomain
  return selectSpaceNotation (← `(W^{$k,$p}($Ω)))) <|> delabSpaceApp

/-- Keep the spatial dimension explicit in whole-space scalar notation. -/
@[scoped app_delab SobolevSpace.GraphSpace.WkpSpace]
def delabScalarWkpSpace : Delab := (do
  guardSpaceNotation 3
  guardIntegerSobolevScope
  let n ← withNaryArg 0 delab
  let k ← withNaryArg 1 delab
  let p ← withNaryArg 2 delab
  return selectSpaceNotation (← `(W^{$k,$p}(ℝ^$n)))) <|> delabSpaceApp

end Sobolev

end
