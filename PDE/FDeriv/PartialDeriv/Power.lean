/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.FDeriv.PartialDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# The power rule for coordinate derivatives

## Motivation

What is the coordinate derivative of a power of a real function on `ℝ^d`?

## The idea

The coordinate derivative `∂ₖ` is the Fréchet derivative applied to the `k`-th coordinate
vector, so the rule is Mathlib's `fderiv_fun_pow` evaluated at that vector.

## Main results

* `DifferentiableAt.partialDeriv_fun_pow`: `∂ₖ (fᵐ) = m f^{m-1} ∂ₖ f` at every point where `f`
  is differentiable, for all dimensions `d` and all exponents `m`.
* `DifferentiableAt.partialDeriv_fun_pow_succ`: `∂ₖ (f^{m+1}) = (m + 1) fᵐ ∂ₖ f`, the same
  rule without the truncated subtraction.

## Relations

The second result is the first at the exponent `m + 1`. `PDE.partialDeriv_sq` is the first at
the exponent `2`, and the `example` at the end of this file derives its statement from it.
`PDE.Analysis.partialDeriv_fun_pow` in `PDE.Analysis.Calculus.PowerBounds` is the first in the
plane. `PDE.Elliptic.Regularity.Analytic.frozenOperator_pow` and
`PDE.Elliptic.Regularity.Analytic.le_frozenOperator_ballWeight_pow_mul_sq` use the second.

## What stays open

Powers of functions with values in a normed algebra are not stated.
-/

@[expose] public section

namespace PDE

variable {d : ℕ} {f : ℝ^d → ℝ} {y : ℝ^d}

/-- The power rule for a coordinate derivative: `∂ₖ (fᵐ) = m f^{m-1} ∂ₖ f` at a point where `f`
is differentiable. -/
theorem _root_.DifferentiableAt.partialDeriv_fun_pow (hf : DifferentiableAt ℝ f y) (m : ℕ)
    (k : Fin d) : (∂[k] (fun y ↦ f y ^ m)) y = m * f y ^ (m - 1) * (∂[k] f) y := by
  change fderiv ℝ (fun y ↦ f y ^ m) y (EuclideanSpace.single k 1) =
    m * f y ^ (m - 1) * fderiv ℝ f y (EuclideanSpace.single k 1)
  rw [fderiv_fun_pow m hf]
  simp only [smul_apply, smul_eq_mul, nsmul_eq_mul]

/-- The power rule at the exponent `m + 1`: `∂ₖ (f^{m+1}) = (m + 1) fᵐ ∂ₖ f` at a point where
`f` is differentiable. -/
theorem _root_.DifferentiableAt.partialDeriv_fun_pow_succ (hf : DifferentiableAt ℝ f y) (m : ℕ)
    (k : Fin d) : (∂[k] (fun y ↦ f y ^ (m + 1))) y = (m + 1) * f y ^ m * (∂[k] f) y := by
  simpa using hf.partialDeriv_fun_pow (m + 1) k

/-- The statement of `PDE.partialDeriv_sq` is the power rule at the exponent `2`. -/
example (hf : DifferentiableAt ℝ f y) (k : Fin d) :
    (∂[k] (fun y ↦ f y ^ 2)) y = 2 * f y * (∂[k] f) y := by
  simpa using hf.partialDeriv_fun_pow 2 k

end PDE
