/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.ExactTactic
public import PDE.Symbolic.PDEDerivatives
public import CAS.IntegrationTactic
/-!
# Symbolic derivatives in PDE calculations

These calculations cover scalar derivatives: elementary shapes, symbolic natural exponents and
composite expressions with frozen parameters. Positivity hypotheses specify where square roots
and real powers are differentiable. Coordinate derivatives, radial Laplacians and the derivatives
of library functions are in `DerivativesEuclidean.lean`.
-/

@[expose] public section

namespace PDE.Examples.CASDerivatives

/-! ## Scalar shapes -/

/-- `HasDerivAt` for a polynomial: the inner derivative of the smooth absolute value. -/
example (ε x : ℝ) : HasDerivAt (fun y : ℝ ↦ y ^ 2 + ε ^ 2) (2 * x) x := by
  cas

/-- An exponential decay mode, as in the Laplace-transform module. -/
example (lambda t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ Real.exp (-lambda * s)) (-lambda * Real.exp (-lambda * t)) t := by
  cas

/-- `HasDerivWithinAt` is derived from the pointwise derivative; the nonvanishing denominator
is proved from the local hypothesis. -/
example (u₀ : ℝ) (hne : u₀ ≠ 1) :
    HasDerivWithinAt (fun u : ℝ ↦ u / (1 - u)) (1 / (1 - u₀) ^ 2) (Set.Icc 0 (1 / 2)) u₀ := by
  cas

/-- `DifferentiableAt` needs no stated derivative. -/
example (x : ℝ) (hx : x ≠ 0) : DifferentiableAt ℝ (fun t : ℝ ↦ t⁻¹ + Real.sin t) x := by
  cas

/-- A nested derivative is eliminated inner-first; the inner body must be valid everywhere. -/
example (a x : ℝ) :
    deriv (fun x ↦ deriv (fun y ↦ Real.sin (a * y)) x) x = -(a ^ 2) * Real.sin (a * x) := by
  cas

/-- The evaluation point may be a coordinate of a Euclidean vector. -/
example (n : ℕ) (x : ℝ^1) :
    HasDerivAt (fun s : ℝ ↦ ((n + 1 : ℕ) : ℝ) * s - 1) ((n + 1 : ℕ) : ℝ) (x 0) := by
  cas

/-- Bare `cas` recognises derivative shapes. -/
example (a b x : ℝ) : deriv (fun t : ℝ ↦ a * t ^ 2 + b) x = 2 * a * x := by
  cas

/-- Complex differentiation uses Mathlib's analytic and chain rules. -/
example (z : ℂ) :
    HasDerivAt (fun w : ℂ ↦ Complex.exp (w ^ 2)) (2 * z * Complex.exp (z ^ 2)) z := by
  cas

/-- A supplied derivative family lets the same chain rule work with an arbitrary function. -/
example (f f' : ℝ → ℝ) (hf : ∀ x, HasDerivAt f (f' x) x) (x : ℝ) :
    deriv (fun t ↦ f (t ^ 2) + f t) x = f' (x ^ 2) * (2 * x) + f' x := by
  cas

/-- Bare `cas` dispatches interval integrals to the integration frontend when it is imported. -/
example (a b : ℝ) : (∫ t in a..b, t ^ 2) = b ^ 3 / 3 - a ^ 3 / 3 := by
  cas

/-- Mathlib's total inverse sine is constant on the exterior interval `(1, ∞)`. -/
example : HasDerivAt Real.arcsin 0 2 := by
  cas

/-- The inverse cosine derivative also vanishes there. -/
example : HasDerivAt Real.arccos 0 2 := by
  cas

/-! ## Symbolic natural exponents

The power rule produces the exponent `2 * (k + 1) - 1`, a truncated natural subtraction that
Mathlib's normal forms do not identify with `2 * k + 1`. The checked finisher unfolds the
computed derivative and reflects both sides over atoms, reading the exponent arithmetic through
the cast of `k` with `omega` discharging the non-truncation bound. -/

/-- The odd-power potential of `PDE.Analysis.Scalar.OddPower`, stated with the exponent as
written. -/
example (linear nonlinear : ℝ) (k : ℕ) (z : ℝ) :
    HasDerivAt
      (fun t : ℝ ↦ linear * t ^ 2 / 2 + nonlinear * t ^ (2 * (k + 1)) / (2 * (k + 1)))
      (linear * z + nonlinear * z ^ (2 * k + 1)) z := by
  cas

/-- The power rule with a symbolic exponent. -/
example (x : ℝ) (n : ℕ) : deriv (fun t : ℝ ↦ t ^ (n + 1)) x = (n + 1) * x ^ n := by
  cas

/-! ## Composite frozen parameters

Binder-independent subterms are frozen as parameters of the reflected body. A parameter that
contains the numerals `0` or `1`, such as `x + 1` or `1 / 2`, is identified with its
atoms on the checked route (`Fin.reduceFinMk`, `reduceFinAppend`, `Nat.cast_one`), which is
needed when the Mathlib script cannot supply `(√u)² = u`. -/

example (x y : ℝ) (h : 0 < (x + 1) * y) (hy : y ≠ 0) :
    deriv (fun t : ℝ ↦ Real.sqrt ((x + 1) * t)) y = Real.sqrt ((x + 1) * y) / (2 * y) := by
  cas

example (y : ℝ) (hy : 0 < y) :
    deriv (fun t : ℝ ↦ (1 / 2) * Real.sqrt t) y = (1 / 2) * Real.sqrt y / (2 * y) := by
  cas

example (x : ℝ) (p : ℝ^2) (h : 0 < (x + 1) * p 0) (hp : p 0 ≠ 0) :
    (∂[0] (fun q : ℝ^2 ↦ Real.sqrt ((x + 1) * q 0))) p =
      Real.sqrt ((x + 1) * p 0) / (2 * p 0) := by
  cas

end PDE.Examples.CASDerivatives
