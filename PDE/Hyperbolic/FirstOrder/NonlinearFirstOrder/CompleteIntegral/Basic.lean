/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.Characteristics.Equation
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Complete integrals of nonlinear first-order equations

A complete integral has as many parameters as spatial variables. Its
parameter derivative in the first jet `(u, Du)` has full column rank. We
express this rank condition by injectivity of the corresponding linear map,
without choosing coordinates in the augmented jet space. This is condition (ii) of the
definition of a complete integral in Evans, §3.1.1: the `n × (n+1)` matrix
`(D_a u, D²_{xa} u)` of (2) has rank `n`.

This condition is distinct from the invertible parameter Hessian used to
construct a particular stationary envelope. The Clairaut family has full
jet rank even when that Hessian is singular.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.1.1, definition of a complete integral, equation (2).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Gradient

namespace NonlinearFirstOrder

variable {n : ℕ} [Fact (0 < n)]

/-- A C² complete integral on open spatial and parameter domains. The
injectivity field is the full rank `n` condition on the `(n+1) × n`
parameter derivative of `(u, Du)`. -/
structure IsCompleteIntegral (pde : Equation n) (A : Set (ℝ^n))
    (u : ℝ^n → ℝ^n → ℝ) : Prop where
  /-- The spatial domain of the equation is open. -/
  isOpen_domain : IsOpen pde.domain
  /-- The allowed parameters form an open set. -/
  isOpen_parameter : IsOpen A
  /-- The family is jointly C² in the spatial and parameter variables. -/
  contDiffOn : ContDiffOn ℝ 2 (fun q : ℝ^n × ℝ^n ↦ u q.1 q.2) (pde.domain ×ˢ A)
  /-- Each allowed parameter gives a classical solution on the spatial domain. -/
  classical : ∀ a ∈ A, IsClassicalSolution pde (fun x ↦ u x a)
  /-- At each spatial point, the derivative of the value-gradient jet with respect to
  the parameters has full column rank. -/
  parameter_rank : ∀ x ∈ pde.domain, ∀ a ∈ A,
    Function.Injective (fderiv ℝ (fun b ↦ (u x b, ∇ (fun y ↦ u y b) x)) a)

end NonlinearFirstOrder
