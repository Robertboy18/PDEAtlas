/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.TruncatedPowerCell

/-!
# Exact rational coefficients of an affine cell polynomial

The branch endpoint selects the truncated powers. Independent origin
and scale parameters express their polynomial in a local coordinate,
including a reflected or degenerate affine substitution. Exact
rational arithmetic casts to every coefficient of the real polynomial.

## Main definitions

* `rationalSplineDividedDifferenceDenominator`: the divided-difference denominator of one knot,
  computed over `ℚ`.
* `rationalTruncatedPowerCellCoefficient`: the `m`-th coefficient over `ℚ` of the cell polynomial
  after the substitution `origin + scale * X`.

## Main results

* `cast_rationalSplineDividedDifferenceDenominator`: the rational denominator casts to the real
  `splineDividedDifferenceDenominator`.
* `coeff_truncatedPowerCellPolynomial_comp_affine`: the binomial formula for the coefficients of
  the cell polynomial composed with `origin + scale * X`.
* `cast_rationalTruncatedPowerCellCoefficient`: every rational coefficient casts to the
  corresponding coefficient of the real polynomial.
* `eval_truncatedPowerCellPolynomial_affine_eq_sum`: the cell polynomial at `origin + scale * t`
  is `∑_{m ≤ n + 1} c_m t^m` with the rational coefficients `c_m`.
* `truncatedPowerBSpline_affine_eq_rational_sum`: if no knot lies in the open cell `(a, b)`, the
  B-spline at `origin + scale * t ∈ [a, b]` is that rational polynomial in `t`.
-/

@[expose] public section

namespace CAS.Splines

open _root_.Polynomial

/-- Exact rational divided-difference denominator for any spline order. -/
def rationalSplineDividedDifferenceDenominator {n : ℕ} (knots : Fin (n + 3) → ℚ)
    (j : Fin (n + 3)) : ℚ :=
  ∏ k ∈ Finset.univ.erase j, (knots j - knots k)

/-- Rational coefficient after the affine substitution `origin + scale * X`. -/
def rationalTruncatedPowerCellCoefficient (n : ℕ) (knots : Fin (n + 3) → ℚ)
    (a origin scale : ℚ) (m : ℕ) : ℚ :=
  ∑ j, if a < knots j then
    ((n + 2 : ℚ) / rationalSplineDividedDifferenceDenominator knots j) *
      ((knots j - origin) ^ (n + 1 - m) * (Nat.choose (n + 1) m : ℚ) * (-scale) ^ m)
  else 0

noncomputable section

/-- Rational denominator arithmetic commutes exactly with casting to the real spline. -/
theorem cast_rationalSplineDividedDifferenceDenominator {n : ℕ}
    (knots : Fin (n + 3) → ℚ) (j : Fin (n + 3)) :
    (rationalSplineDividedDifferenceDenominator knots j : ℝ) =
      splineDividedDifferenceDenominator (fun k ↦ (knots k : ℝ)) j := by
  simp [rationalSplineDividedDifferenceDenominator, splineDividedDifferenceDenominator]

/-- The coefficient of `X^m` in `(k + s X)^n` is `k^(n - m) C(n, m) s^m`. -/
private theorem coeff_affine_pow (k s : ℝ) (n m : ℕ) :
    ((C k + C s * X : ℝ[X]) ^ n).coeff m =
      k ^ (n - m) * (Nat.choose n m : ℝ) * s ^ m := by
  have hcomp : ((X + C k : ℝ[X]) ^ n).comp (C s * X) = (C k + C s * X) ^ n := by
    simp only [pow_comp, add_comp, X_comp, C_comp, add_comm]
  rw [← hcomp, comp_C_mul_X_coeff, coeff_X_add_C_pow]

/-- The binomial formula gives each coefficient of the real affine cell polynomial. -/
theorem coeff_truncatedPowerCellPolynomial_comp_affine (n : ℕ)
    (knots : Fin (n + 3) → ℝ) (a origin scale : ℝ) (m : ℕ) :
    ((truncatedPowerCellPolynomial n knots a).comp (C origin + C scale * X)).coeff m =
      ∑ j, if a < knots j then
        ((n + 2 : ℝ) / splineDividedDifferenceDenominator knots j) *
          ((knots j - origin) ^ (n + 1 - m) *
            (Nat.choose (n + 1) m : ℝ) * (-scale) ^ m)
      else 0 := by
  simp only [truncatedPowerCellPolynomial, sum_comp, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · simp only [mul_comp, C_comp, pow_comp, sub_comp, X_comp, coeff_C_mul]
    have hlinear : (C (knots j) - (C origin + C scale * X) : ℝ[X]) =
        C (knots j - origin) + C (-scale) * X := by
      simp only [map_sub, map_neg]
      ring
    rw [hlinear, coeff_affine_pow]
  · simp

/-- Every exact rational cell coefficient is the corresponding real polynomial coefficient. -/
theorem cast_rationalTruncatedPowerCellCoefficient (n : ℕ) (knots : Fin (n + 3) → ℚ)
    (a origin scale : ℚ) (m : ℕ) :
    (rationalTruncatedPowerCellCoefficient n knots a origin scale m : ℝ) =
      ((truncatedPowerCellPolynomial n (fun j ↦ (knots j : ℝ)) (a : ℝ)).comp
        (C (origin : ℝ) + C (scale : ℝ) * X)).coeff m := by
  rw [coeff_truncatedPowerCellPolynomial_comp_affine]
  simp only [rationalTruncatedPowerCellCoefficient, Rat.cast_sum, apply_ite,
    Rat.cast_add, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_div, Rat.cast_mul,
    Rat.cast_pow, Rat.cast_sub, Rat.cast_neg, Rat.cast_zero,
    cast_rationalSplineDividedDifferenceDenominator, Rat.cast_lt]

/-- The finite rational coefficient vector reconstructs the cell polynomial in any affine chart. -/
theorem eval_truncatedPowerCellPolynomial_affine_eq_sum (n : ℕ)
    (knots : Fin (n + 3) → ℚ) (a origin scale : ℚ) (t : ℝ) :
    (truncatedPowerCellPolynomial n (fun j ↦ (knots j : ℝ)) (a : ℝ)).eval
        ((origin : ℝ) + (scale : ℝ) * t) =
      ∑ m : Fin (n + 2),
        (rationalTruncatedPowerCellCoefficient n knots a origin scale m.val : ℝ) * t ^ m.val := by
  let p := (truncatedPowerCellPolynomial n (fun j ↦ (knots j : ℝ)) (a : ℝ)).comp
    (C (origin : ℝ) + C (scale : ℝ) * X)
  have hlinear : (C (origin : ℝ) + C (scale : ℝ) * X : ℝ[X]).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le (by simp)
    exact (natDegree_C_mul_le _ _).trans (by simp)
  have hp : p.natDegree ≤ n + 1 := by
    exact natDegree_comp_le.trans
      ((Nat.mul_le_mul (natDegree_truncatedPowerCellPolynomial_le n _ _) hlinear).trans
        (by simp))
  have heval : p.eval t = ∑ m : Fin (n + 2), p.coeff m.val * t ^ m.val := by
    rw [eval_eq_sum_range' (show p.natDegree < n + 2 by omega)]
    exact Finset.sum_range _
  simpa only [p, eval_comp, eval_add, eval_C, eval_mul, eval_X,
    ← cast_rationalTruncatedPowerCellCoefficient] using heval

/-- The rational finite sum is the actual raw spline on every admissible closed cell. -/
theorem truncatedPowerBSpline_affine_eq_rational_sum (n : ℕ)
    (knots : Fin (n + 3) → ℚ) (a b origin scale : ℚ)
    (hknots : ∀ j, knots j ≤ a ∨ b ≤ knots j) {t : ℝ}
    (ht : (origin : ℝ) + (scale : ℝ) * t ∈ Set.Icc (a : ℝ) (b : ℝ)) :
    truncatedPowerBSpline n (fun j ↦ (knots j : ℝ))
        ((origin : ℝ) + (scale : ℝ) * t) =
      ∑ m : Fin (n + 2),
        (rationalTruncatedPowerCellCoefficient n knots a origin scale m.val : ℝ) * t ^ m.val := by
  have hreal : ∀ j, (knots j : ℝ) ≤ (a : ℝ) ∨ (b : ℝ) ≤ (knots j : ℝ) := by
    intro j
    exact (hknots j).imp (Rat.cast_le.mpr) (Rat.cast_le.mpr)
  rw [← truncatedPowerCellPolynomial_eval n _ hreal ht]
  exact eval_truncatedPowerCellPolynomial_affine_eq_sum n knots a origin scale t

end

end CAS.Splines
