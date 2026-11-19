/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Model.Notation
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Model

/-!
# Notation for Banach-valued Sobolev spaces

With `open scoped Sobolev`, write `W^{k,p}(Ω; F)` for functions on the open
domain `Ω` with weak derivatives through order `k` in `Lᵖ(Ω; F)`. Here `Ω`
is a bundled open set and `F` is any complete normed real vector space.
For the whole domain, write `W^{k,p}(ℝ^n; F)`.

The semicolon keeps the codomain visible. In particular, `W^{k,p}(Ω; ℝ)`
uses the Banach-valued graph; the scalar space `W^{k,p}(Ω)` is related to it
by the isometry in `GraphSpace.VectorValued.Scalar`.
-/

@[expose] public section

/-- Banach-valued Sobolev space on a bundled open domain. -/
scoped[Sobolev] notation "W^{" k "," p "}(" Ω "; " F ")" =>
  SobolevSpace.VectorValued.WkpSpaceOn _ k p Ω F

/-- Banach-valued Sobolev space on the whole Euclidean space. -/
scoped[Sobolev] notation "W^{" k "," p "}(" "ℝ^" n "; " F ")" =>
  SobolevSpace.VectorValued.WkpSpaceOn n k p
    (⊤ : TopologicalSpace.Opens ℝ^n) F

public meta section

namespace Sobolev

open Lean PrettyPrinter.Delaborator SubExpr

/-- The graph keeps its codomain visible, including when that codomain is real. -/
@[scoped app_delab SobolevSpace.VectorValued.WkpSpaceOn]
def delabNativeWkpSpaceOn : Delab := (do
  guardSpaceNotation 8
  guardIntegerSobolevScope
  let k ← withNaryArg 1 delab
  let p ← withNaryArg 2 delab
  let F ← withNaryArg 4 delab
  let Ω ← withNaryArg 3 delab
  match Ω with
  | `(⊤) =>
    let n ← withNaryArg 0 delab
    return selectSpaceNotation (← `(W^{$k,$p}(ℝ^$n; $F)))
  | _ =>
    let Ω ← withNaryArg 3 delabSpaceDomain
    return selectSpaceNotation (← `(W^{$k,$p}($Ω; $F)))) <|> delabSpaceApp

/-- In a type position the submodule notation already supplies its carrier coercion. -/
@[scoped app_delab Subtype]
def delabNativeWkpSpaceOnSort : Delab := do
  guardSpaceNotation 2
  guardIntegerSobolevScope
  let #[_, .lam n _ body _] := (← getExpr).getAppArgs | failure
  guard <| body.isAppOf ``Membership.mem
  let #[_, _, inst, space, .bvar 0] := body.getAppArgs | failure
  guard <| inst.isAppOfArity ``SetLike.instMembership 3
  guard <| (inst.getArg! 2).isAppOfArity ``Submodule.setLike 5
  guard <| space.isAppOfArity ``SobolevSpace.VectorValued.WkpSpaceOn 8
  withAppArg <| withBindingBody n <| withNaryArg 3 do
    guardSpaceNotation 8
    delabNativeWkpSpaceOn

end Sobolev

end
