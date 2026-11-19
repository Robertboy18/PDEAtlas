/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import CAS.Continuum.Interval.Rational.RelativeHull

/-!
# Outward rounding of rationals

Certificates evaluated over the rationals keep their numbers small by rounding intermediate values
outward. Rounding up and down to fifty significant bits is the relative rounding
`RationalInterval.roundUpRel 50` and `RationalInterval.roundDownRel 50` of the rational interval
arithmetic. The upper bound `(q/s + s)/2` of `√q` holds for any positive `s`, here a relative
approximation of `√q`.

## Main definitions

* `log2Rat`: the approximate binary exponent of `q`.
* `roundUpRel`, `roundDownRel`: `q` rounded up and down to fifty significant bits.
* `mulHigh`, `mulLow`: upper and lower bounds of `c x` for `x ∈ [lo, hi]`.
* `sqrtApproxRel`: a positive rational near `√q`, to about twenty-five significant bits.
* `sqrtHigh`, `sqrtLow`: the bounds `(q/s + s)/2` and `q / sqrtHigh q` of `√q`.

## Main results

* `le_roundUpRel`: `q ≤ roundUpRel q`.
* `roundDownRel_le`: `roundDownRel q ≤ q`.
* `mul_le_mulHigh`: `c x ≤ mulHigh c lo hi` for `x ∈ [lo, hi]`.
* `mulLow_le_mul`: `mulLow c lo hi ≤ c x` for `x ∈ [lo, hi]`.
* `sqrt_le_sqrtHigh`: `√q ≤ sqrtHigh q` for `q ≥ 0`.
* `sqrtLow_le_sqrt`: `sqrtLow q ≤ √q` for `q ≥ 0`.
-/

@[expose] public section

namespace PDE.Analysis

open CAS.Continuum

/-- The integer part of `log₂ |q|`, approximately. -/
def log2Rat (q : ℚ) : ℤ := (Nat.log2 q.num.natAbs : ℤ) - (Nat.log2 q.den : ℤ)

/-- `q` rounded up to fifty significant bits, `RationalInterval.roundUpRel 50 q`. -/
def roundUpRel (q : ℚ) : ℚ := RationalInterval.roundUpRel 50 q

/-- `q` rounded down to fifty significant bits, `RationalInterval.roundDownRel 50 q`. -/
def roundDownRel (q : ℚ) : ℚ := RationalInterval.roundDownRel 50 q

/-- Rounding up does not decrease: `q ≤ roundUpRel q`. -/
theorem le_roundUpRel (q : ℚ) : q ≤ roundUpRel q :=
  RationalInterval.le_roundUpRel 50 q

/-- Rounding down does not increase: `roundDownRel q ≤ q`. -/
theorem roundDownRel_le (q : ℚ) : roundDownRel q ≤ q :=
  RationalInterval.roundDownRel_le 50 q

/-- Rounding down keeps a nonnegative rational nonnegative. -/
theorem roundDownRel_nonneg {q : ℚ} (hq : 0 ≤ q) : 0 ≤ roundDownRel q := by
  unfold roundDownRel RationalInterval.roundDownRel
  have hp : (0 : ℚ) < 2 ^ RationalInterval.relativeExponent 50 q := zpow_pos (by norm_num) _
  have : (0 : ℤ) ≤ ⌊q * 2 ^ RationalInterval.relativeExponent 50 q⌋ :=
    Int.floor_nonneg.2 (mul_nonneg hq hp.le)
  have : (0 : ℚ) ≤ (⌊q * 2 ^ RationalInterval.relativeExponent 50 q⌋ : ℚ) := by
    exact_mod_cast this
  positivity

/-- An upper bound of `c x` for `x ∈ [lo, hi]`. -/
def mulHigh (c lo hi : ℚ) : ℚ := if 0 ≤ c then c * hi else c * lo

/-- A lower bound of `c x` for `x ∈ [lo, hi]`. -/
def mulLow (c lo hi : ℚ) : ℚ := if 0 ≤ c then c * lo else c * hi

/-- For `x ∈ [lo, hi]`, `c x ≤ mulHigh c lo hi`. -/
theorem mul_le_mulHigh {c lo hi : ℚ} {x : ℝ} (h₁ : (lo : ℝ) ≤ x) (h₂ : x ≤ hi) :
    (c : ℝ) * x ≤ mulHigh c lo hi := by
  unfold mulHigh
  split_ifs with hc
  · push_cast
    exact mul_le_mul_of_nonneg_left h₂ (by exact_mod_cast hc)
  · push_cast
    exact mul_le_mul_of_nonpos_left h₁ (by exact_mod_cast (not_le.1 hc).le)

/-- For `x ∈ [lo, hi]`, `mulLow c lo hi ≤ c x`. -/
theorem mulLow_le_mul {c lo hi : ℚ} {x : ℝ} (h₁ : (lo : ℝ) ≤ x) (h₂ : x ≤ hi) :
    (mulLow c lo hi : ℝ) ≤ c * x := by
  unfold mulLow
  split_ifs with hc
  · push_cast
    exact mul_le_mul_of_nonneg_left h₁ (by exact_mod_cast hc)
  · push_cast
    exact mul_le_mul_of_nonpos_left h₂ (by exact_mod_cast (not_le.1 hc).le)

/-- A positive rational near `√q` for `q > 0`, to about twenty-five significant bits. -/
def sqrtApproxRel (q : ℚ) : ℚ :=
  let m : ℤ := 26 - log2Rat q / 2
  let s : ℚ := (Nat.sqrt ⌊q * 4 ^ m⌋.toNat : ℚ) / 2 ^ m
  if 0 < s then s else 1

/-- The approximation `sqrtApproxRel q` is positive. -/
theorem sqrtApproxRel_pos (q : ℚ) : 0 < sqrtApproxRel q := by
  unfold sqrtApproxRel
  dsimp only
  split_ifs with h
  · exact h
  · exact one_pos

/-- An upper bound `(q/s + s)/2` of `√q`, with `s = sqrtApproxRel q`. -/
def sqrtHigh (q : ℚ) : ℚ := (q / sqrtApproxRel q + sqrtApproxRel q) / 2

/-- For `q ≥ 0`, `√q ≤ sqrtHigh q`, by the inequality of arithmetic and geometric means for `q / s`
and `s`. -/
theorem sqrt_le_sqrtHigh {q : ℚ} (hq : 0 ≤ q) : Real.sqrt q ≤ sqrtHigh q := by
  have hs := sqrtApproxRel_pos q
  have hs' : (0 : ℝ) < sqrtApproxRel q := by exact_mod_cast hs
  have hq' : (0 : ℝ) ≤ q := by exact_mod_cast hq
  have h := Real.sq_sqrt hq'
  simp only [sqrtHigh]
  push_cast
  rw [le_div_iff₀ (by norm_num), div_add' _ _ _ hs'.ne', le_div_iff₀ hs']
  nlinarith [sq_nonneg (Real.sqrt q - sqrtApproxRel q)]

/-- A lower bound `q / sqrtHigh q` of `√q`. -/
def sqrtLow (q : ℚ) : ℚ := q / sqrtHigh q

/-- For `q ≥ 0` the upper bound `sqrtHigh q` is positive. -/
theorem sqrtHigh_pos {q : ℚ} (hq : 0 ≤ q) : 0 < sqrtHigh q := by
  have hs := sqrtApproxRel_pos q
  unfold sqrtHigh
  have : 0 ≤ q / sqrtApproxRel q := div_nonneg hq hs.le
  linarith

/-- For `q ≥ 0`, `sqrtLow q ≤ √q`. -/
theorem sqrtLow_le_sqrt {q : ℚ} (hq : 0 ≤ q) : (sqrtLow q : ℝ) ≤ Real.sqrt q := by
  have hh := sqrtHigh_pos hq
  have hh' : (0 : ℝ) < sqrtHigh q := by exact_mod_cast hh
  have hs := sqrt_le_sqrtHigh hq
  have hq' : (0 : ℝ) ≤ q := by exact_mod_cast hq
  have h2 := Real.mul_self_sqrt hq'
  simp only [sqrtLow]
  push_cast
  rw [div_le_iff₀ hh']
  nlinarith [Real.sqrt_nonneg (q : ℝ)]

/-- For `q > 0` the lower bound `sqrtLow q` is positive. -/
theorem sqrtLow_pos {q : ℚ} (hq : 0 < q) : 0 < sqrtLow q :=
  div_pos hq (sqrtHigh_pos hq.le)

end PDE.Analysis
