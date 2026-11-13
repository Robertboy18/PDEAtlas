/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.TruncatedPower
public import PDE.Analysis.Calculus.ClosedIntervalDerivatives

/-!
# Exact truncated-power polynomials on closed cells

A supporting knot outside the open cell fixes the branch of its
positive part throughout the closed cell. The resulting polynomial
also identifies every continuous derivative at the cell endpoints.
To the right of every knot, and strictly to the left of distinct knots,
the polynomial is zero.

## Main definitions

* `truncatedPowerCellPolynomial`: the polynomial branch of `truncatedPowerBSpline` selected
  immediately to the right of `a`.

## Main results

* `truncatedPowerCellPolynomial_eval`: if no knot lies in `(a, b)`, the polynomial equals the
  B-spline on `[a, b]`.
* `natDegree_truncatedPowerCellPolynomial_le`: the polynomial has degree at most `n + 1`.
* `iteratedDeriv_truncatedPowerCellPolynomial_eqOn`: on such a cell with `a < b`, the derivatives
  of order `m ≤ n` of the polynomial and of the B-spline agree on `[a, b]`.
* `truncatedPowerCellPolynomial_eq_zero_of_knots_le`: the polynomial is zero when every knot is at
  most `a`.
* `truncatedPowerCellPolynomial_eq_zero_of_lt_knots`: the polynomial is zero when the knots are
  distinct and all larger than `a`.
-/

@[expose] public noncomputable section

namespace CAS.Splines

open _root_.Polynomial

/-- The polynomial branch selected immediately to the right of `a`. -/
def truncatedPowerCellPolynomial (n : ℕ) (knots : Fin (n + 3) → ℝ) (a : ℝ) : ℝ[X] :=
  ∑ j, if a < knots j then
    C ((n + 2 : ℝ) / splineDividedDifferenceDenominator knots j) *
      (C (knots j) - X) ^ (n + 1)
  else 0

/-- No supporting knot in the open cell gives equality throughout the closed cell. -/
theorem truncatedPowerCellPolynomial_eval (n : ℕ) (knots : Fin (n + 3) → ℝ)
    {a b x : ℝ} (hknots : ∀ j, knots j ≤ a ∨ b ≤ knots j) (hx : x ∈ Set.Icc a b) :
    (truncatedPowerCellPolynomial n knots a).eval x = truncatedPowerBSpline n knots x := by
  unfold truncatedPowerCellPolynomial truncatedPowerBSpline
  rw [eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : a < knots j
  · have hright := (hknots j).resolve_left (not_le.mpr hj)
    rw [ite_eq_left hj, posPart_eq_self.mpr (sub_nonneg.mpr (hx.2.trans hright))]
    simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_X]
    exact div_mul_eq_mul_div _ _ _
  · rw [ite_eq_right hj,
      posPart_eq_zero.mpr (sub_nonpos.mpr ((le_of_not_gt hj).trans hx.1))]
    simp

/-- Each cell polynomial has at most the degree of its truncated powers. -/
theorem natDegree_truncatedPowerCellPolynomial_le (n : ℕ)
    (knots : Fin (n + 3) → ℝ) (a : ℝ) :
    (truncatedPowerCellPolynomial n knots a).natDegree ≤ n + 1 := by
  unfold truncatedPowerCellPolynomial
  apply natDegree_sum_le_of_forall_le
  intro j _
  split_ifs
  · apply (natDegree_C_mul_le _ _).trans
    have hlinear : (C (knots j) - X).natDegree ≤ 1 := by
      simpa using natDegree_sub_le (C (knots j)) (X : ℝ[X])
    simpa using (natDegree_pow_le.trans (Nat.mul_le_mul_left (n + 1) hlinear))
  · simp

/-- The polynomial represents every derivative through the spline's smoothness order,
including both endpoints of a nondegenerate cell. -/
theorem iteratedDeriv_truncatedPowerCellPolynomial_eqOn (n : ℕ)
    (knots : Fin (n + 3) → ℝ) {a b : ℝ} (hab : a < b)
    (hknots : ∀ j, knots j ≤ a ∨ b ≤ knots j) {m : ℕ} (hm : m ≤ n) :
    Set.EqOn
      (iteratedDeriv m (fun x ↦ (truncatedPowerCellPolynomial n knots a).eval x))
      (iteratedDeriv m (truncatedPowerBSpline n knots)) (Set.Icc a b) := by
  exact PDE.Analysis.iteratedDeriv_eqOn_Icc hab (PDE.Analysis.contDiff_polynomial_eval _)
    (contDiff_truncatedPowerBSpline n knots)
    (fun _ hx ↦ truncatedPowerCellPolynomial_eval n knots hknots hx) hm

/-- To the right of all supporting knots, every cell-polynomial summand is excluded. -/
theorem truncatedPowerCellPolynomial_eq_zero_of_knots_le (n : ℕ)
    (knots : Fin (n + 3) → ℝ) {a : ℝ} (hknots : ∀ j, knots j ≤ a) :
    truncatedPowerCellPolynomial n knots a = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  exact ite_eq_right (not_lt.mpr (hknots j))

/-- Strictly to the left of distinct knots, divided-difference cancellation gives zero. -/
theorem truncatedPowerCellPolynomial_eq_zero_of_lt_knots (n : ℕ)
    (knots : Fin (n + 3) → ℝ) (hinj : Function.Injective knots)
    {a : ℝ} (hknots : ∀ j, a < knots j) :
    truncatedPowerCellPolynomial n knots a = 0 := by
  apply Polynomial.funext
  intro x
  simp only [truncatedPowerCellPolynomial, ite_eq_left (hknots _), eval_finsetSum,
    eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_zero]
  simp_rw [div_mul_eq_mul_div, mul_div_assoc]
  rw [← Finset.mul_sum, sum_splineDividedDifference_pow_eq_zero n knots hinj (by omega), mul_zero]

end CAS.Splines
