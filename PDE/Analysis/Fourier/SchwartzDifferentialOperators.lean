/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.Schwartz.Derivatives

/-!
# Fourier calculus for Schwartz differential operators

The Fourier transform turns differentiation into multiplication by a polynomial in the
frequency: with Mathlib's convention `𝓕 f ξ = ∫ exp (-2π i x ξ) f x dx`, one has
`𝓕(∂ₓ f)(ξ) = (2π i ξ) 𝓕f(ξ)` for every Schwartz function `f`, hence
`𝓕(∂ₓⁿ f) = (2π i ξ)ⁿ 𝓕f` and, for a constant-coefficient operator `P(∂ₓ) = ∑ aₙ ∂ₓⁿ`,
`𝓕(P(∂ₓ) f) = P(2π i ξ) 𝓕f`. In Evans's unitary angular-frequency convention this is
§4.3.1, Theorem 2(ii), `(D^α u)^ = (iy)^α û`, which he applies to `-Δu + u = f` in Example 1
of §4.3.1(b). We work on `𝓢(ℝ, ℂ)`, where each identity follows from Mathlib's
`Real.fourier_iteratedDeriv`. The sign in the multiplier depends on the sign convention in
the exponential; with the opposite convention `2π i ξ` becomes `-2π i ξ`.

The derivative symbol `fourierDerivativeSymbol1D ξ = 2π i ξ` and the positive elliptic
symbol `fourierEllipticSymbol1D ξ = (2π ξ)²` of `-∂ₓₓ` are given names, so that the `L²`
derivative domain of the Hilbert transform uses the same convention.

## Main results

* `fourier_constant_coeff_operator_multiplier`: for a finite set of orders with complex
  coefficients, `𝓕(∑ aₙ ∂ₓⁿ f) = (∑ aₙ (2π i ξ)ⁿ) 𝓕f`.
* `fourier_second_derivative_multiplier_elliptic_symbol`,
  `fourier_negative_second_derivative_multiplier`: `𝓕(∂ₓₓ f) = -(2π ξ)² 𝓕f`, so `-∂ₓₓ` has
  the positive symbol `(2π ξ)²`.

## Implementation notes

Iterated derivatives are written with `Function.iterate` applied to
`SchwartzMap.derivCLM ℂ ℂ`, not through a separate differential-operator type, so the
results compose with Mathlib's continuous linear maps on the Schwartz space. All results
are one-dimensional.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.3.1, Theorem 2(ii), p. 189, step 2 of its proof,
  p. 190, and Example 1, p. 191. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Analysis.Fourier

open scoped SchwartzMap
open scoped FourierTransform
open scoped BigOperators

/-- The Fourier symbol `2π i ξ` of `∂ₓ` under Mathlib's convention:
`𝓕(∂ₓ f)(ξ) = (2π i ξ) 𝓕(f)(ξ)`. -/
noncomputable def fourierDerivativeSymbol1D (ξ : ℝ) : ℂ :=
  (2 * Real.pi : ℂ) * Complex.I * (ξ : ℂ)

/-- The positive elliptic symbol for `-∂ₓₓ` under Mathlib's Fourier convention. -/
noncomputable def fourierEllipticSymbol1D (ξ : ℝ) : ℂ :=
  ((2 * Real.pi : ℂ) * (ξ : ℂ)) ^ 2

/-- Fourier algebra for an arbitrary finite constant-coefficient differential operator.

`orders` records the derivative orders that occur and `a n` is the complex coefficient of
`∂ₓⁿ`.  The conclusion says that the differential operator is replaced by evaluation of the same
finite polynomial at the Fourier symbol `2π i ξ`.  Repeated orders are not needed because
`Finset` combines the coefficient of each order before this theorem is applied. -/
theorem fourier_constant_coeff_operator_multiplier (f : 𝓢(ℝ, ℂ)) (a : ℕ → ℂ)
    (orders : Finset ℕ) (x : ℝ) :
    SchwartzMap.fourierTransformCLM ℂ
        (∑ n ∈ orders, a n •
          ((fun g : 𝓢(ℝ, ℂ) ↦ SchwartzMap.derivCLM ℂ ℂ g)^[n] f)) x =
      (∑ n ∈ orders, a n * fourierDerivativeSymbol1D x ^ n) *
        SchwartzMap.fourierTransformCLM ℂ f x := by
  calc
    SchwartzMap.fourierTransformCLM ℂ
        (∑ n ∈ orders, a n •
          ((fun g : 𝓢(ℝ, ℂ) ↦ SchwartzMap.derivCLM ℂ ℂ g)^[n] f)) x =
        ∑ n ∈ orders, a n *
          SchwartzMap.fourierTransformCLM ℂ
            ((fun g : 𝓢(ℝ, ℂ) ↦ SchwartzMap.derivCLM ℂ ℂ g)^[n] f) x := by
      simp
    _ = ∑ n ∈ orders, (a n * fourierDerivativeSymbol1D x ^ n) *
          SchwartzMap.fourierTransformCLM ℂ f x := by
      apply Finset.sum_congr rfl
      intro n hn
      have h := Real.fourier_iteratedDeriv (f.smooth ⊤)
        (fun k _ ↦ f.integrable_iteratedDeriv k)
        (n := n) le_top
      have hx := congrFun h x
      simpa only [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe,
        SchwartzMap.coe_iterate_derivCLM, fourierDerivativeSymbol1D,
        smul_eq_mul, mul_assoc] using
        congrArg (a n * ·) hx
    _ = (∑ n ∈ orders, a n * fourierDerivativeSymbol1D x ^ n) *
          SchwartzMap.fourierTransformCLM ℂ f x := by
      rw [Finset.sum_mul]

/-- The second derivative has Fourier multiplier `-(2πξ)^2`, so `-∂ₓₓ` has the positive symbol
`(2πξ)^2`. In Evans's convention, §4.3.1, Theorem 2(ii), the multiplier is `-y^2`. -/
theorem fourier_second_derivative_multiplier_elliptic_symbol (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    SchwartzMap.fourierTransformCLM ℂ
        (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f)) x =
      -fourierEllipticSymbol1D x * (SchwartzMap.fourierTransformCLM ℂ f x) := by
  have h := Real.fourier_iteratedDeriv (f.smooth ⊤)
    (fun k _ ↦ f.integrable_iteratedDeriv k)
    (n := 2) le_top
  have hsymbol : fourierDerivativeSymbol1D x ^ 2 = -fourierEllipticSymbol1D x := by
    let a : ℂ := (2 * Real.pi : ℂ) * (x : ℂ)
    have hder : fourierDerivativeSymbol1D x = a * Complex.I := by
      simp [fourierDerivativeSymbol1D, a, mul_left_comm, mul_comm]
    have hell : fourierEllipticSymbol1D x = a ^ 2 := by
      simp [fourierEllipticSymbol1D, a, mul_comm]
    rw [hder, hell]
    calc
      (a * Complex.I) ^ 2 = a ^ 2 * Complex.I ^ 2 := by ring
      _ = a ^ 2 * (-1 : ℂ) := by rw [Complex.I_sq]
      _ = -a ^ 2 := by ring
  have hx := congrFun h x
  change 𝓕 (iteratedDeriv 2 (f : ℝ → ℂ)) x =
    fourierDerivativeSymbol1D x ^ 2 * 𝓕 (f : ℝ → ℂ) x at hx
  rw [hsymbol] at hx
  simpa only [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe,
    ← SchwartzMap.coe_iterate_derivCLM ℂ, Function.iterate_succ_apply',
    Function.iterate_zero_apply] using hx

/-- The operator `-∂ₓₓ` has the positive Fourier multiplier `(2πξ)^2`. -/
theorem fourier_negative_second_derivative_multiplier (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    SchwartzMap.fourierTransformCLM ℂ
        (-(SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f))) x =
      fourierEllipticSymbol1D x * (SchwartzMap.fourierTransformCLM ℂ f x) := by
  have h := fourier_second_derivative_multiplier_elliptic_symbol f x
  calc
    SchwartzMap.fourierTransformCLM ℂ
        (-(SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f))) x =
        -SchwartzMap.fourierTransformCLM ℂ
          (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f)) x := by
          simp
    _ = -(-fourierEllipticSymbol1D x * (SchwartzMap.fourierTransformCLM ℂ f x)) := by
          rw [h]
    _ = fourierEllipticSymbol1D x * (SchwartzMap.fourierTransformCLM ℂ f x) := by
          ring

end PDE.Analysis.Fourier
