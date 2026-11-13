/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Periodic-cell averaging

Rescaling a one-periodic function by a positive integer preserves its average over the unit
cell. This is the one-dimensional cell identity behind integer rescaling in periodic
homogenization.
-/

@[expose] public section

namespace PDE.Analysis.Asymptotics

open scoped Interval
open MeasureTheory intervalIntegral

/-- Rescaling a one-periodic function by a positive integer preserves its average over one cell. -/
theorem periodicCellAverage_integerRescaling
    (a : ℝ → ℝ) (ha : Function.Periodic a 1)
    (ha_int : IntervalIntegrable a volume 0 1) (N : ℕ) :
    ∫ x in (0 : ℝ)..1, a ((N.succ : ℝ) * x) = ∫ x in (0 : ℝ)..1, a x := by
  let c : ℝ := N.succ
  have hc_pos : 0 < c := by
    simpa [c] using (show (0 : ℝ) < (N.succ : ℝ) by positivity)
  have hc : c ≠ 0 := ne_of_gt hc_pos
  have hscale :
      c * ∫ x in (0 : ℝ)..1, a (c * x) = ∫ x in (0 : ℝ)..c, a x := by
    simpa [smul_eq_mul, c] using
      (intervalIntegral.smul_integral_comp_mul_left
        (f := a) (a := (0 : ℝ)) (b := (1 : ℝ)) c)
  have hall : ∀ t₁ t₂, IntervalIntegrable a volume t₁ t₂ :=
    ha.intervalIntegrable₀ (by norm_num) ha_int
  have hperiod :
      ∫ x in (0 : ℝ)..c, a x = c * ∫ x in (0 : ℝ)..1, a x := by
    simpa [c, Nat.cast_succ, one_zsmul, zsmul_eq_mul, smul_eq_mul] using
      (ha.intervalIntegral_add_zsmul_eq (n := (N.succ : ℤ)) (t := (0 : ℝ)) hall)
  have hmul : c * ∫ x in (0 : ℝ)..1, a (c * x) = c * ∫ x in (0 : ℝ)..1, a x := by
    rw [hscale, hperiod]
  exact mul_left_cancel₀ hc hmul

end PDE.Analysis.Asymptotics
