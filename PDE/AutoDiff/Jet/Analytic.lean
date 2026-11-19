/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.AutoDiff.Jet.Basic
public import PDE.FDeriv.PartialDeriv

/-!
# First-order calculus semantics for formal jets

`Jet` is a formal multivariate power series. `RepresentsFirstOrderAt` says that its constant
and linear coefficients are the value and the partial derivatives of a real function at a point.
The proposition includes differentiability on a neighborhood, rather than deriving regularity
from the formal coefficients. Coefficients of degree two and higher are unconstrained, and
no convergence of the series is asserted.
-/

@[expose] public section

namespace PDE.AutoDiff.Jet

open scoped Topology

/--
A formal jet represents the value and coordinate derivatives of `f` at `x` to first order.

The function and point are indices of the proposition rather than duplicated fields. Neighborhood
differentiability provides the regularity needed to interpret `partialDeriv` classically; the
remaining fields identify the formal constant and linear coefficients with the function value
and coordinate derivatives.
-/
structure RepresentsFirstOrderAt {n order : ℕ}
    (jet : Jet (Fin n) ℝ order) (f : ℝ^n → ℝ) (x : ℝ^n) : Prop where
  /-- The represented function is differentiable at every point in some neighborhood of `x`. -/
  differentiableEventually :
    ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y
  /-- The formal constant coefficient is the function value at `x`. -/
  value_eq :
    value jet = f x
  /-- Every formal linear coordinate coefficient is the corresponding partial derivative. -/
  firstCoefficient_eq_partialDeriv :
    ∀ i, firstCoefficient i jet = (∂[i] f) x

end PDE.AutoDiff.Jet
