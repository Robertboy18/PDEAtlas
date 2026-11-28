/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Lower integrals of nonnegative real functions over intervals

Polar coordinates produce lower integrals over `(0, ∞)`, while the calculus of one variable works
with interval integrals of real functions. For an interval integrable `f` that is nonnegative on
`(a, b]`, the lower integral of `ENNReal.ofReal (f r)` over `(a, b]` is `ENNReal.ofReal` of the
interval integral of `f`, and so is the lower integral over the half line `(a, ∞)` when `f`
vanishes beyond `b`. Both are Mathlib's `MeasureTheory.ofReal_integral_eq_lintegral_ofReal` on
an interval: for `a ≤ b` the interval integral is the Bochner integral over `(a, b]`. Functions
that are nonnegative only almost everywhere on the interval are not treated.

## Main results

* `MeasureTheory.setLIntegral_Ioc_ofReal_eq_intervalIntegral`: for `a ≤ b` and `f` interval
  integrable and nonnegative on `(a, b]`,
  `∫⁻ r in (a, b], ofReal (f r) = ofReal (∫ r in a..b, f r)`.
* `MeasureTheory.setLIntegral_Ioi_ofReal_eq_intervalIntegral`: for the same `f`, if it also
  vanishes beyond `b`, `∫⁻ r in (a, ∞), ofReal (f r) = ofReal (∫ r in a..b, f r)`.
-/

@[expose] public noncomputable section

open Set

namespace MeasureTheory

variable {f : ℝ → ℝ} {a b : ℝ}

/-- For `a ≤ b` and an interval integrable `f` that is nonnegative on `(a, b]`, the lower
integral of `ENNReal.ofReal (f r)` over `(a, b]` is the interval integral of `f`. -/
theorem setLIntegral_Ioc_ofReal_eq_intervalIntegral (hab : a ≤ b) (hf0 : ∀ r ∈ Ioc a b, 0 ≤ f r)
    (hfi : IntervalIntegrable f volume a b) :
    ∫⁻ r in Ioc a b, ENNReal.ofReal (f r) = ENNReal.ofReal (∫ r in a..b, f r) := by
  rw [intervalIntegral.integral_of_le hab, ofReal_integral_eq_lintegral_ofReal hfi.1
    ((ae_restrict_mem measurableSet_Ioc).mono fun r hr ↦ hf0 r hr)]

/-- For `a ≤ b` and an interval integrable `f` that is nonnegative on `(a, b]` and zero beyond
`b`, the lower integral of `ENNReal.ofReal (f r)` over the half line `(a, ∞)` is the interval
integral of `f` from `a` to `b`. -/
theorem setLIntegral_Ioi_ofReal_eq_intervalIntegral (hab : a ≤ b) (hf0 : ∀ r ∈ Ioc a b, 0 ≤ f r)
    (hfz : ∀ r, b < r → f r = 0) (hfi : IntervalIntegrable f volume a b) :
    ∫⁻ r in Ioi a, ENNReal.ofReal (f r) = ENNReal.ofReal (∫ r in a..b, f r) := by
  have h1 : ∫⁻ r in Ioi a, ENNReal.ofReal (f r) = ∫⁻ r in Ioc a b, ENNReal.ofReal (f r) := by
    rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioc]
    refine lintegral_congr fun r ↦ ?_
    by_cases h : r ∈ Ioc a b
    · rw [indicator_of_mem h, indicator_of_mem (mem_Ioi.mpr h.1)]
    · rw [indicator_of_notMem h]
      by_cases h' : r ∈ Ioi a
      · rw [indicator_of_mem h', hfz r (by by_contra hc; exact h ⟨h', not_lt.mp hc⟩),
          ENNReal.ofReal_zero]
      · rw [indicator_of_notMem h']
  rw [h1, setLIntegral_Ioc_ofReal_eq_intervalIntegral hab hf0 hfi]

end MeasureTheory
