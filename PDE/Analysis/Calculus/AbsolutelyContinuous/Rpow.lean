/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Absolute continuity of real powers at the origin

For every real `a > 0` and every `b`, the power `r ↦ r^a` is absolutely continuous on the
interval between `0` and `b`. For `0 < a < 1` the power is not Lipschitz at `0`, so a bound on
the derivative does not give this. It is what the fundamental theorem of calculus needs for a
product `r^a φ(r)`, as in the proof of Bliss's inequality. On an interval inside `[0, ∞)` that
does not start at `0` the statement follows by restriction. For `b < 0` it is a statement about
Mathlib's real power of a negative base.

## Main results

* `Real.absolutelyContinuousOnInterval_rpow`: `r ↦ r^a` is absolutely continuous on the interval
  between `0` and `b`, for all `a > 0` and all real `b`.

## How it works

The power is the integral of its derivative, `r^a = ∫₀^r a s^{a-1} ds`, and `s^{a-1}` is
integrable at `0` because `a - 1 > -1` (`intervalIntegral.intervalIntegrable_rpow'`). An
indefinite integral of an integrable function is absolutely continuous
(`IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`).

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley, 1999,
  for absolutely continuous functions and the fundamental theorem of calculus for Lebesgue
  integrals.
  <https://www.wiley.com/en-us/Real+Analysis%3A+Modern+Techniques+and+Their+Applications%2C+2nd+Edition-p-9780471317166>
-/

@[expose] public noncomputable section

open MeasureTheory Set

/-- For `a > 0` the power `r ↦ r^a` is absolutely continuous on the interval between `0` and
`b`: it is the integral of `a s^{a-1}`, which is integrable at `0`. For `b < 0` the power is
Mathlib's real power of a negative base. -/
theorem Real.absolutelyContinuousOnInterval_rpow {a : ℝ} (ha : 0 < a) (b : ℝ) :
    AbsolutelyContinuousOnInterval (fun r : ℝ ↦ r ^ a) 0 b := by
  have hint : IntervalIntegrable (fun s : ℝ ↦ a * s ^ (a - 1)) volume 0 b :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul a
  refine (hint.absolutelyContinuousOnInterval_intervalIntegral (c := 0) left_mem_uIcc).congr
    fun r _ ↦ ?_
  change ∫ v in (0 : ℝ)..r, a * v ^ (a - 1) = r ^ a
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)), sub_add_cancel,
    Real.zero_rpow ha.ne', sub_zero]
  field_simp
