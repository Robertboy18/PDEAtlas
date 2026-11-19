/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.PositivePartPower
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.Fintype.Order

/-!
# Smoothness and support of truncated-power B-splines

An order-`n + 2` B-spline is the divided-difference sum of truncated powers
`(sⱼ - x)₊^(n + 1)`. It has `n` continuous derivatives across every supporting
knot. Lagrange interpolation annihilates the polynomial sum below all knots;
above all knots, every truncated power vanishes. Distinct supporting knots
therefore give compact support without a decay or regularity hypothesis.
Differentiating the truncated powers gives the first two derivatives
explicitly, including their values at the knots.

This is the basis formula used in Chen and Hou, Part II, Appendix C, (C.3a).
The near-field order six and angular order eight correspond to `n = 4` and
`n = 6`, respectively.

## Main definitions

* `truncatedPowerBSpline`: the order-`n + 2` truncated-power formula on `n + 3` knots, with its
  normalization factor.
* `truncatedPowerBSplineDeriv`: its explicit first derivative; `truncatedPowerBSplineSecondDeriv`
  is the second derivative.

## Main results

* `contDiff_truncatedPowerBSpline`: the basis is `C^n` on all of `ℝ`, the knots included.
* `sum_splineDividedDifference_pow_eq_zero`: the untruncated divided-difference sum annihilates
  every power of degree below `n + 2`.
* `truncatedPowerBSpline_eq_zero_of_le_knots`: for distinct knots the basis vanishes below every
  knot; `truncatedPowerBSpline_eq_zero_of_knots_le` is the case above every knot.
* `hasCompactSupport_truncatedPowerBSpline`: distinct knots give compact support.
* `hasDerivAt_truncatedPowerBSpline`: for `1 ≤ n` the basis has the derivative
  `truncatedPowerBSplineDeriv` at every point.
* `hasDerivAt_truncatedPowerBSplineDeriv`: for `2 ≤ n` the first derivative has the derivative
  `truncatedPowerBSplineSecondDeriv` at every point.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Appendix C, (C.3a)
  and (C.4). <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public noncomputable section

namespace CAS.Splines

open _root_.Polynomial
open scoped ContDiff

/-- The product denominator for one term of a finite divided difference. -/
def splineDividedDifferenceDenominator {n : ℕ} (knots : Fin (n + 3) → ℝ)
    (j : Fin (n + 3)) : ℝ :=
  ∏ k ∈ Finset.univ.erase j, (knots j - knots k)

/-- The order-`n + 2` truncated-power basis formula, including its normalization factor. -/
def truncatedPowerBSpline (n : ℕ) (knots : Fin (n + 3) → ℝ) : ℝ → ℝ :=
  fun x ↦ ∑ j, (n + 2 : ℝ) * (knots j - x)⁺ ^ (n + 1) /
    splineDividedDifferenceDenominator knots j

/-- Finite smoothness of the actual truncated-power formula, including every knot. -/
theorem contDiff_truncatedPowerBSpline (n : ℕ) (knots : Fin (n + 3) → ℝ) :
    ContDiff ℝ (n : ℕ∞ω) (truncatedPowerBSpline n knots) := by
  unfold truncatedPowerBSpline
  apply ContDiff.sum
  intro j _
  exact (contDiff_const.mul
    ((PDE.Analysis.contDiff_posPart_pow_succ n).comp
      (contDiff_const.sub contDiff_id))).div_const _

/-- The untruncated divided-difference sum annihilates every power of degree below
`n + 2`. -/
theorem sum_splineDividedDifference_pow_eq_zero (n : ℕ)
    (knots : Fin (n + 3) → ℝ) (hknots : Function.Injective knots) {d : ℕ} (hd : d < n + 2)
    (x : ℝ) :
    (∑ j, (knots j - x) ^ d / splineDividedDifferenceDenominator knots j) = 0 := by
  let P : ℝ[X] := (X - C x) ^ d
  have hnatDegree : P.natDegree = d := by
    simp [P]
  have hdegree : P.degree < ((Finset.univ : Finset (Fin (n + 3))).card : ℕ) := by
    apply lt_of_le_of_lt (degree_le_natDegree)
    simp only [hnatDegree, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast (show d < n + 3 by omega)
  have hcoeff : P.coeff (n + 2) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rwa [hnatDegree]
  have h := Lagrange.coeff_eq_sum
    (s := Finset.univ) (v := knots) (P := P) (fun i _ j _ hij ↦ hknots hij) hdegree
  simpa [P, hcoeff, splineDividedDifferenceDenominator] using h.symm

/-- Below every supporting knot, interpolation cancellation makes the basis zero. -/
theorem truncatedPowerBSpline_eq_zero_of_le_knots (n : ℕ)
    (knots : Fin (n + 3) → ℝ) (hknots : Function.Injective knots) {x : ℝ}
    (hx : ∀ j, x ≤ knots j) : truncatedPowerBSpline n knots x = 0 := by
  unfold truncatedPowerBSpline
  simp_rw [posPart_eq_self.mpr (sub_nonneg.mpr (hx _)), mul_div_assoc]
  rw [← Finset.mul_sum, sum_splineDividedDifference_pow_eq_zero n knots hknots (by omega)]
  exact mul_zero _

/-- Above every supporting knot, each truncated-power term is zero. -/
theorem truncatedPowerBSpline_eq_zero_of_knots_le (n : ℕ)
    (knots : Fin (n + 3) → ℝ) {x : ℝ} (hx : ∀ j, knots j ≤ x) :
    truncatedPowerBSpline n knots x = 0 := by
  unfold truncatedPowerBSpline
  apply Finset.sum_eq_zero
  intro j _
  rw [posPart_eq_zero.mpr (sub_nonpos.mpr (hx j)), zero_pow (by omega)]
  simp

/-- Distinct supporting knots give compact support for the actual basis formula. -/
theorem hasCompactSupport_truncatedPowerBSpline (n : ℕ)
    (knots : Fin (n + 3) → ℝ) (hknots : Function.Injective knots) :
    HasCompactSupport (truncatedPowerBSpline n knots) := by
  obtain ⟨lo, hlo⟩ := Finite.bddBelow_range knots
  obtain ⟨hi, hhi⟩ := Finite.bddAbove_range knots
  apply HasCompactSupport.intro (isCompact_Icc (a := lo) (b := hi))
  intro x hx
  have hx' : x < lo ∨ hi < x := by simpa only [Set.mem_Icc, not_and_or, not_le] using hx
  rcases hx' with hleft | hright
  · exact truncatedPowerBSpline_eq_zero_of_le_knots n knots hknots
      (fun j ↦ hleft.le.trans (hlo ⟨j, rfl⟩))
  · exact truncatedPowerBSpline_eq_zero_of_knots_le n knots
      (fun j ↦ (hhi ⟨j, rfl⟩).trans hright.le)

/-- The explicit first derivative of the truncated-power formula. -/
def truncatedPowerBSplineDeriv (n : ℕ) (knots : Fin (n + 3) → ℝ) (x : ℝ) : ℝ :=
  ∑ j, -((n + 2) * (n + 1) : ℝ) * (knots j - x)⁺ ^ n /
    splineDividedDifferenceDenominator knots j

/-- The explicit second derivative of the truncated-power formula. -/
def truncatedPowerBSplineSecondDeriv (n : ℕ) (knots : Fin (n + 3) → ℝ) (x : ℝ) : ℝ :=
  ∑ j, ((n + 2) * (n + 1) * n : ℝ) * (knots j - x)⁺ ^ (n - 1) /
    splineDividedDifferenceDenominator knots j

/-- The derivative of `y ↦ (a - y)₊^(m + 2)` at `x` is `-(m + 2) (a - x)₊^(m + 1)`. -/
private theorem hasDerivAt_truncatedPower (m : ℕ) (a x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (a - y)⁺ ^ (m + 2)) (-(m + 2 : ℝ) * (a - x)⁺ ^ (m + 1)) x := by
  have h := (PDE.Analysis.hasDerivAt_posPart_pow m (a - x)).comp x
    ((hasDerivAt_id x).const_sub a)
  convert h using 1
  · rfl
  · push_cast
    ring

/-- A basis with one continuous derivative has the explicit first derivative,
also at the knots. -/
theorem hasDerivAt_truncatedPowerBSpline {n : ℕ} (hn : 1 ≤ n) (knots : Fin (n + 3) → ℝ)
    (x : ℝ) :
    HasDerivAt (truncatedPowerBSpline n knots) (truncatedPowerBSplineDeriv n knots x) x := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold truncatedPowerBSpline truncatedPowerBSplineDeriv
  apply HasDerivAt.fun_sum
  intro j _
  have h := ((hasDerivAt_truncatedPower m (knots j) x).const_mul
    ((m + 1 : ℕ) + 2 : ℝ)).div_const (splineDividedDifferenceDenominator knots j)
  convert h using 1
  push_cast
  ring

/-- A basis with two continuous derivatives has the explicit second derivative,
also at the knots. -/
theorem hasDerivAt_truncatedPowerBSplineDeriv {n : ℕ} (hn : 2 ≤ n)
    (knots : Fin (n + 3) → ℝ) (x : ℝ) :
    HasDerivAt (truncatedPowerBSplineDeriv n knots)
      (truncatedPowerBSplineSecondDeriv n knots x) x := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold truncatedPowerBSplineDeriv truncatedPowerBSplineSecondDeriv
  apply HasDerivAt.fun_sum
  intro j _
  have h := ((hasDerivAt_truncatedPower m (knots j) x).const_mul
    (-(((m + 2 : ℕ) : ℝ) + 2) * (((m + 2 : ℕ) : ℝ) + 1))).div_const
      (splineDividedDifferenceDenominator knots j)
  convert h using 1
  · funext y
    push_cast
    ring
  · simp only [show m + 2 - 1 = m + 1 by omega]
    push_cast
    ring

end CAS.Splines
