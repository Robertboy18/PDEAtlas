/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Data.Nat.Notation

/-!
# Partial-derivative notation

The input to `∂[i] u` determines its derivative operator and result type.
For ordinary functions this is a classical coordinate derivative. For Sobolev
functions it is a weak derivative, with one less order of Sobolev regularity.
Application and repeated differentiation need no extra parentheses:
`∂[i] u x` and `∂[i] ∂[j] u x`.
Here `i : Fin n`, `∂[i] u x` means `(∂[i] u) x`, and `∂[i] ∂[j] u` differentiates first in
`j`, then in `i`.

The notation is global and needs no scope. This module supplies only the syntax; each operator
comes with the module that defines it.

* Functions `ℝ^n → E`: the classical coordinate derivative `PDE.partialDeriv`, from
  `PDE.FDeriv.PartialDeriv`.
* Scalar Sobolev functions in `W^{k+1,p}(Ω)` or `W₀^{k+1,p}(Ω)`: the weak derivative in
  `W^{k,p}(Ω)`, from `PDE.Spaces.Sobolev.GraphSpace.Operators.PartialDerivatives`. A
  zero-boundary input gives an element of the ambient space, since the derivative need not
  have zero boundary values.
* Banach-valued Sobolev functions in `W^{m+1,p}(Ω; F)`: the weak derivative in
  `W^{m,p}(Ω; F)`, from `PDE.Spaces.Sobolev.GraphSpace.VectorValued.Derivatives`.
* Schwartz functions in `𝓢(ℝ^n, F)`: from `PDE.DistributionTheory.Schwartz.PartialDerivative`.
* Distributions in `𝓓'(Ω, F)` on an open set of `ℝ^n`: a distribution on the same domain, from
  `PDE.DistributionTheory.Distribution.Operator.Notation`, which also gives `Δ T`.
* Formal power series indexed by `Fin n`: Mathlib's `MvPowerSeries.pderiv`, from
  `PDE.Notation.PowerSeries`.

The notation asserts no regularity and no derivative identity; those are hypotheses and
theorems about the chosen operator. When a proof needs the continuous linear map itself, use
the named operator, such as `SobolevSpace.GraphSpace.partialDerivCLM`.

The spaces have their own scopes: `open scoped Sobolev` for Sobolev spaces, `SchwartzMap` for
`𝓢(E, F)`, and `Distributions` for `𝓓'(Ω, F)`. Classical `∇` and `Δ`, including the
distributional Laplacian, are Mathlib's notation in the `Gradient` and `Laplacian` scopes. The
weak gradient `∇ u` of a scalar Sobolev function is notation in the `Sobolev` scope, from
`PDE.Spaces.Sobolev.GraphSpace.Operators.Gradient`.

`PDE.Examples.Notation.PartialDerivative` checks application, repeated derivatives, and the
dispatch on ordinary, Schwartz, and Sobolev functions and on distributions.
-/

@[expose] public section

namespace PDE

/-- A coordinate derivative operator whose result type is determined by its input.

This class supplies notation; differentiability and weak-derivative identities
are proved separately for the chosen operator. -/
class PartialDerivative (n : outParam ℕ) (X : Type*) (Y : outParam Type*) where
  /-- Differentiate in the specified coordinate direction. -/
  partialDeriv : Fin n → X → Y

end PDE

namespace PDE

public meta section

open Lean Meta Elab Term

/-- Coordinate partial derivatives, selected by the input type. -/
syntax:max (name := partialDerivativeNotation) "∂[" term "] " term:max : term

/-- Resolve a coordinate derivative to its underlying operator.

Elaborating the input first settles postponed instances, including numeric
coordinate indices in component functions, before derivative dispatch.
Unresolved projections may still wait for the surrounding expression to
determine their domain.
Reducing the operator before application preserves continuous-map coercions.
Beta-reducing its arguments keeps component codomains such as `(fun _ ↦ ℝ) j`
from appearing in the result type without unfolding function coercions.
Known abstract instances retain their class projection. -/
@[term_elab partialDerivativeNotation]
def elabPartialDerivative : TermElab := fun stx expectedType? ↦ do
  let `(∂[$i] $u) := stx | throwUnsupportedSyntax
  let u ← withSynthesize (postpone := .yes) <| elabTerm u none
  let u ← exprToSyntax (← instantiateMVars u)
  let e ← elabTerm (← `(PDE.PartialDerivative.partialDeriv $i $u)) expectedType?
  synthesizeSyntheticMVars
  let e ← instantiateMVars e
  let .app (.app operator i) u := e |
    throwError "unexpected coordinate derivative application"
  let operator ← withTransparency .instances <| whnf operator
  if operator.isAppOf ``PDE.PartialDerivative.partialDeriv && operator.hasExprMVar then
    tryPostpone
  let operator := mkAppN operator.getAppFn (operator.getAppArgs.map Expr.headBeta)
  return (mkApp2 operator i u).headBeta

end

end PDE
