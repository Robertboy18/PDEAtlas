/-
Authors: Levent Alpöge, Tristan Buckmaster

The lemmas of this file come from modules of the Lean package of the paper
"Finite-time blow-up for the Navier–Stokes equations"
(https://github.com/tristanbuckmaster/navier-stokes, folder lean/, commit ad53419),
where six of the seven were proved in several modules and two_mul_re_mul_conj_le_young was a step
of a longer proof. They were included in BlowupZoo
(https://github.com/lean-dojo/BlowupZoo, folder AtlasCandidates/) with the permission of the
authors (20 November 2026) and moved here from there; the file NOTICE of this repository records it.
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.SimpleRing.Principal

set_option linter.style.header false

/-!
# Squared norms of complex numbers

The lemmas express `‖z‖ ^ 2` through `z * conj z` and through the real and imaginary parts, bound
`‖a ± b‖ ^ 2` by `2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2`, and complete a square. The proofs are algebra on the
real and imaginary parts (`ring`, `nlinarith`, `field_simp`).

## Main results

* `PDE.Analysis.sq_norm_eq_re_mul_conj`: for every complex `z`, `‖z‖ ^ 2` is the real part of
  `z * conj z`.
* `PDE.Analysis.sq_norm_eq_mul_conj`: for every complex `z`, the real number `‖z‖ ^ 2`, seen in `ℂ`,
  is `z * conj z`.
* `PDE.Analysis.sq_norm_eq_re_sq_add_im_sq`: for every complex `z`, `‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2`.
* `PDE.Analysis.norm_add_sq_le_two_mul`: for complex `x` and `y`,
  `‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2`.
* `PDE.Analysis.norm_sub_sq_le_two_mul`: for complex `a` and `b`,
  `‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2`.
* `PDE.Analysis.neg_norm_sq_div_le_add_re`: for real `h > 0` and complex `a`, `b`,
  `-(‖b‖ ^ 2 / h) ≤ h * ‖a‖ ^ 2 + 2 * (a * conj b).re`.
* `PDE.Analysis.two_mul_re_mul_conj_le_young`: for real `h > 0` and complex `a`, `b`,
  `2 * (a * conj b).re ≤ h * ‖a‖ ^ 2 + ‖b‖ ^ 2 / h`.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

/-- For real `h > 0` and complex `a`, `b`, `-(‖b‖ ^ 2 / h) ≤ h * ‖a‖ ^ 2 + 2 * (a * conj b).re`. By
completing the square: the difference of the two sides is `‖h * a + b‖ ^ 2 / h`. -/
theorem neg_norm_sq_div_le_add_re {h : ℝ} (hh : 0 < h) (a b : ℂ) :
    -(‖b‖ ^ 2 / h) ≤ h * ‖a‖ ^ 2 + 2 * (a * (starRingEnd ℂ) b).re := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  have key : h * (a.re * a.re + a.im * a.im) + 2 * (a.re * b.re - a.im * -b.im) +
      (b.re * b.re + b.im * b.im) / h
      = ((h * a.re + b.re) ^ 2 + (h * a.im + b.im) ^ 2) / h := by
    field_simp; ring
  have : 0 ≤ ((h * a.re + b.re) ^ 2 + (h * a.im + b.im) ^ 2) / h := by positivity
  linarith

/-- For complex `x` and `y`, `‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2`. From `‖x + y‖ ≤ ‖x‖ + ‖y‖`
and `2 * ‖x‖ * ‖y‖ ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2`. -/
theorem norm_add_sq_le_two_mul (x y : ℂ) : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h1 : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- For every complex `z`, `‖z‖ ^ 2` is the real part of `z * conj z`. -/
theorem sq_norm_eq_re_mul_conj (z : ℂ) : ‖z‖ ^ 2 = (z * (starRingEnd ℂ) z).re := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]

/-- For every complex `z`, `‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2`. -/
theorem sq_norm_eq_re_sq_add_im_sq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- For every complex `z`, the real number `‖z‖ ^ 2`, seen in `ℂ`, equals `z * conj z`. -/
theorem sq_norm_eq_mul_conj (z : ℂ) : (((‖z‖ ^ 2 : ℝ)) : ℂ) = z * (starRingEnd ℂ) z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- For complex `a` and `b`, `‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2`. This is
`norm_add_sq_le_two_mul` at `-b`. -/
theorem norm_sub_sq_le_two_mul (a b : ℂ) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_add_sq_le_two_mul a (-b)
  rwa [← sub_eq_add_neg, norm_neg] at h

end PDE.Analysis

/-! ### A Young-type bound -/

namespace PDE.Analysis

/-- Young-type bound for complex numbers: for `0 < h` and complex `a`, `b`,
`2 * (a * conj b).re ≤ h * ‖a‖ ^ 2 + ‖b‖ ^ 2 / h`. -/
theorem two_mul_re_mul_conj_le_young {h : ℝ} (hh : 0 < h) (a b : ℂ) :
    2 * (a * (starRingEnd ℂ) b).re ≤ h * ‖a‖ ^ 2 + ‖b‖ ^ 2 / h := by
  have := neg_norm_sq_div_le_add_re hh (-a) b
  rw [norm_neg, neg_mul, Complex.neg_re] at this
  linarith

end PDE.Analysis
