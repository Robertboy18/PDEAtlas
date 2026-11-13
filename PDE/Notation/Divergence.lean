/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public meta import Lean.Elab.SyntheticMVars
public import Lean.Exception

/-!
# Divergence notation

The input to `∇· u` determines the divergence operator and its result type.
For an ordinary vector field the result is a function; for a Sobolev vector
field it is a weak divergence in the corresponding Sobolev or `Lᵖ` space.
The notation is global, as is `∂[i] u`.

For an ordinary vector field, `∇· u x` means `(∇· u) x`. This module supplies only the
syntax; each operator comes with the module that defines it.

* Vector fields `ℝ^n → ℝ^n`: the coordinate divergence `PDE.divergence`, from
  `PDE.FDeriv.Operators`.
* Sobolev vector fields in `W^{k+1,p}(Ω; ℝ^n)`: the weak divergence in `W^{k,p}(Ω)`, from
  `PDE.Spaces.Sobolev.GraphSpace.VectorValued.Divergence`.
* Zero-boundary Hilbert vector fields in `H¹₀(Ω; ℝ^n)`: the weak divergence as an `L²` class,
  from `PDE.Spaces.Sobolev.Calculus.Divergence.ZeroBoundary`.

When a proof needs the continuous linear map itself, use the named operator, such as
`SobolevSpace.VectorValued.divergenceCLM`.
-/

@[expose] public section

namespace PDE

universe u v

/-- Divergence notation with a result type determined by the vector field.
The analytical properties belong to each concrete operator. -/
class Divergence (X : Type u) (Y : outParam (Type v)) where
  /-- Take the divergence of a vector field. -/
  divergence : X → Y

public meta section

open Lean Meta Elab Term

/-- Divergence, selected by the input type. -/
syntax:max (name := divergenceNotation) "∇· " term:arg : term

/-- Resolve divergence to its underlying operator before applying it.

This preserves the continuous linear map used by weak divergence. Abstract
instances retain their class projection. -/
@[term_elab divergenceNotation]
def elabDivergence : TermElab := fun stx expectedType? ↦ do
  let `(∇· $u) := stx | throwUnsupportedSyntax
  let e ← elabTerm (← `(PDE.Divergence.divergence $u)) expectedType?
  synthesizeSyntheticMVars
  let e ← instantiateMVars e
  let .app operator u := e | throwError "unexpected divergence application"
  let operator ← withTransparency .instances <| whnf operator
  if operator.isAppOf ``PDE.Divergence.divergence && operator.hasExprMVar then
    tryPostpone
  return (mkApp operator u).headBeta

end

end PDE
