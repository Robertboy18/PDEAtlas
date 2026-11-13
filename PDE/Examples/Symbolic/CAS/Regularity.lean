/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives
/-!
# Checked regularity goal shapes and derivative identities

These examples record the ordinary Mathlib regularity statements that
`cas` (and bare `cas`) prove through the checked symbolic language, and
the identities with several derivative terms that bare `cas` closes by rewriting
every derivative subterm to its checked closed form before the arithmetic route.

* Regularity shapes: `DifferentiableAt ℝ f x`, `Differentiable ℝ f`,
  `ContDiffAt ℝ n f x`, `ContDiffOn ℝ n f s`, and `ContDiff ℝ n f`, for explicit
  elementary `f : ℝ → ℝ` and `f : ℝ^k → ℝ` with a literal `k`. The smoothness order
  may be a natural literal, `(⊤ : ℕ∞)`, a variable of type `ℕ∞`, or the analytic
  order, because the bridge theorems of `CAS.Calculus.Smoothness` hold for
  every order. The analytic domain conditions are exactly those of the derivative
  rules (nonzero denominators and logarithm arguments, positive square-root and
  real-power bases); for `ContDiffOn`, `ContDiff`, and `Differentiable` they must
  hold on the set or everywhere.
* Derivative identities: residual identities such as
  `deriv (deriv f) t - deriv (deriv g) x = 0` and differences of repeated
  `partialDeriv`s of explicit functions, which are not a single derivative
  statement and therefore go through bare `cas`.

Every shape is shown with a positive instance and, where a hypothesis is
essential, a negative instance that must fail without changing the proof state.
-/

@[expose] public section

namespace PDE.Examples.CASRegularity

/-! ## Regularity on `ℝ^k` -/

/-- Products and exponentials of coordinates are differentiable everywhere. -/
example (x : ℝ^2) : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y 0 * Real.exp (y 1)) x := by
  cas

/-- A polynomial in the coordinates is smooth of every finite order. -/
example : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ^3 ↦ x 0 ^ 2 + x 1 ^ 2) := by
  cas

/-- A quotient of coordinates is differentiable where the denominator does not vanish; the
condition is read from the local context. -/
example (p : ℝ^2) (hp : p 0 ≠ 0) : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y 1 / y 0) p := by
  cas

/-- Smoothness on an open set: the condition must hold at every point of the set, and the
membership hypothesis is unfolded automatically. -/
example : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ^2 ↦ Real.log (q 0 * q 1)) {q | 0 < q 0 ∧ 0 < q 1} := by
  cas

/-- Bare `cas` dispatches regularity goals to the same route. -/
example (x : ℝ^2) : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y 0 * Real.exp (y 1)) x := by
  cas

/-! ## Regularity on `ℝ` -/

/-- A finite smoothness order. -/
example (a : ℝ) : ContDiff ℝ 2 (fun t : ℝ ↦ Real.sin (a * t)) := by
  cas

/-- A logarithm whose argument is positive everywhere. -/
example (x : ℝ) : ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ Real.log (1 + t ^ 2)) x := by
  cas

/-- Smoothness on a half-line: the denominator is nonzero at every point of the set. -/
example : ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ 1 / t) (Set.Ioi 0) := by
  cas

/-- Global differentiability of a Gaussian. -/
example : Differentiable ℝ (fun t : ℝ ↦ Real.exp (-t ^ 2)) := by
  cas

/-- The smoothness order may be a variable. -/
example (n : ℕ∞) (x : ℝ) : ContDiffAt ℝ n (fun t : ℝ ↦ Real.exp (2 * t)) x := by
  cas

/-- The analytic order is certified as well, since Mathlib's lemmas for the elementary
functions hold for every order. -/
example : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun t : ℝ ↦ Real.cos t * t) := by
  cas

/-- A square root and a real power need a positive base at the point. -/
example (x : ℝ) (hx : 0 < x) :
    ContDiffAt ℝ 3 (fun t : ℝ ↦ Real.sqrt t + t ^ (1 / 2 : ℝ)) x := by
  cas

/-- Current-module definitions depending on the variable are unfolded automatically. -/
noncomputable def heatMode (k t x : ℝ) : ℝ :=
  Real.exp (-(k ^ 2) * t) * Real.sin (k * x)

example (k x : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ heatMode k t x) := by
  cas

/-! ## Identities with several derivative terms

Bare `cas` rewrites every maximal derivative subterm of an ordinary identity to its checked
closed form before the arithmetic route, so the residual identities of separated-variable
solutions close in one step. -/

/-- The mixed second derivatives of `sin x * sin s` in either variable agree. -/
example (t x : ℝ) :
    deriv (deriv (fun s : ℝ ↦ Real.sin x * Real.sin s)) t -
        deriv (deriv (fun y : ℝ ↦ Real.sin y * Real.sin t)) x = 0 := by
  cas

/-- The one-dimensional wave equation for `sin (y - x)`, as a difference of repeated partial
derivatives. -/
example (p : ℝ^2) :
    (∂[0] (fun q : ℝ^2 ↦ (∂[0] (fun r : ℝ^2 ↦ Real.sin (r 1 - r 0))) q)) p -
      (∂[1] (fun q : ℝ^2 ↦ (∂[1] (fun r : ℝ^2 ↦ Real.sin (r 1 - r 0))) q)) p =
        0 := by
  cas

/-- The heat-equation residual of the interval mode `exp (-k² t) sin (k x)`, stated through
the current-module definition, which is unfolded first. -/
example (k t x : ℝ) :
    deriv (fun s ↦ heatMode k s x) t - deriv (deriv (fun y ↦ heatMode k t y)) x = 0 := by
  cas

/-- The domain condition of a derivative subterm is read from the context. -/
example (x : ℝ) (hx : x ≠ 0) : deriv (fun t : ℝ ↦ Real.log (2 * t)) x - 1 / x = 0 := by
  cas

/-- Without it the derivative subterm is left in place and the identity is refused. -/
example (x : ℝ) : x = x := by
  fail_if_success have : deriv (fun t : ℝ ↦ Real.log (2 * t)) x - 1 / x = 0 := by cas
  rfl

/-! ## Negative instances -/

/-- A reciprocal is not smooth on the whole line: the condition `t ≠ 0` fails at `0`. -/
example (x : ℝ) : x = x := by
  fail_if_success have : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ 1 / t) := by cas
  fail_if_success have : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ 1 / t) := by cas
  rfl

/-- Without the nonvanishing hypothesis the quotient of coordinates is refused. -/
example (p : ℝ^2) : p = p := by
  fail_if_success have : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y 1 / y 0) p := by cas
  rfl

/-- A symbolic dimension is refused; the error asks for a literal dimension. -/
example (n : ℕ) (i : Fin n) (y : ℝ^n) : y i = y i := by
  fail_if_success have : DifferentiableAt ℝ (fun y : ℝ^n ↦ y i) y := by cas
  rfl

end PDE.Examples.CASRegularity
