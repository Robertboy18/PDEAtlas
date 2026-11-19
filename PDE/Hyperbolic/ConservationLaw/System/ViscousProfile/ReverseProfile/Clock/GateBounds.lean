/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Clock.Middle

import CAS.CEGA
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# Bounds for the middle clock on the curvature gate

On `[205, 205.1]`, the middle clock lies in `[1, 1.4]`, its first derivative
lies in `[0, 0.05025]`, and its second derivative lies in `[0, 10⁻⁶]`.

The first pulse alone contributes `41 / 40` to the clock at 205, by its unit
mass and first moment. The remaining curvature is nonnegative. Monotonicity
and the estimate at 210 give the value bounds. All four pulse terms
vanish on this gate, so only the bounded density contributes to the curvature.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PDE.Analysis.ClockDensity
open scoped Interval

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.MiddleClock

private theorem integral_weighted_qMinus_205 :
    (∫ s in (0 : ℝ)..205, (205 - s) * qMinus s / 100) = 41 / 40 := by
  have hsupp : Function.support (fun s : ℝ ↦ (205 - s) * qMinus s) ⊆
      Ioc (0 : ℝ) 205 := by
    intro s hs
    change (205 - s) * qMinus s ≠ 0 at hs
    have hq : s ∈ Function.support qMinus := (mul_ne_zero_iff.mp hs).2
    rw [support_qMinus] at hq
    exact ⟨lt_trans (by cas) hq.1, hq.2.le.trans (by cas)⟩
  rw [intervalIntegral.integral_div, intervalIntegral.integral_eq_integral_of_support_subset hsupp]
  simp_rw [sub_mul]
  rw [integral_sub (integrable_qMinus.const_mul 205) integrable_mul_qMinus,
    integral_const_mul, integral_qMinus, integral_mul_qMinus]
  cas

private theorem qMinus_div_le_curvature (y : ℝ) : qMinus y / 100 ≤ curvature y := by
  unfold curvature
  have hp := qPlus_nonneg y
  have hm := qMinus_nonneg (-y)
  have hpneg := qPlus_nonneg (-y)
  have hr := (rho0_pos (y / 100)).le
  cas

/-- The first pulse alone puts the clock strictly above one at the gate entrance. -/
theorem g_205_ge : (41 / 40 : ℝ) ≤ g 205 := by
  rw [g_eq_weighted_integral]
  calc
    (41 / 40 : ℝ) = ∫ s in (0 : ℝ)..205, (205 - s) * qMinus s / 100 :=
      integral_weighted_qMinus_205.symm
    _ ≤ ∫ s in (0 : ℝ)..205, (205 - s) * curvature s := by
      apply intervalIntegral.integral_mono_on (by cas) ((((continuous_const.sub continuous_id).mul
          contDiff_qMinus.continuous).div_const 100).intervalIntegrable 0 205)
        (((continuous_const.sub continuous_id).mul
          contDiff_curvature.continuous).intervalIntegrable 0 205)
      intro s hs
      calc
        (205 - s) * qMinus s / 100 = (205 - s) * (qMinus s / 100) := by cas
        _ ≤ (205 - s) * curvature s :=
          mul_le_mul_of_nonneg_left (qMinus_div_le_curvature s) (sub_nonneg.mpr hs.2)

/-- The clock values on the closed gate satisfy the range used in the curvature estimate. -/
theorem g_mem_Icc_gate {y : ℝ} (hy : y ∈ Icc (205 : ℝ) (2051 / 10)) :
    g y ∈ Icc (1 : ℝ) (7 / 5) := by
  have hy0 : 0 ≤ y := le_trans (by cas : (0 : ℝ) ≤ 205) hy.1
  constructor
  · calc
      (1 : ℝ) ≤ 41 / 40 := by cega
      _ ≤ g 205 := g_205_ge
      _ ≤ g y := monotoneOn_g_nonneg (by cas : (0 : ℝ) ≤ 205) hy0 hy.1
  · calc
      g y ≤ g 210 := monotoneOn_g_nonneg hy0 (by cas : (0 : ℝ) ≤ 210)
        (hy.2.trans (by cega))
      _ ≤ 27941 / 20000 := g_210_le
      _ ≤ 7 / 5 := by cega

/-- Positive curvature gives the lower slope bound; pulse masses give the upper bound. -/
theorem deriv_g_mem_Icc_gate {y : ℝ} (hy : y ∈ Icc (205 : ℝ) (2051 / 10)) :
    deriv g y ∈ Icc (0 : ℝ) (201 / 4000) := by
  constructor
  · rw [deriv_g]
    exact intervalIntegral.integral_nonneg_of_forall
      (le_trans (by cas : (0 : ℝ) ≤ 205) hy.1) fun s ↦ (curvature_pos s).le
  · exact (abs_le.mp (abs_deriv_g_le y)).2

/-- The open pulse supports end at 205, leaving only the density beyond that point. -/
theorem curvature_of_205_le {y : ℝ} (hy : 205 ≤ y) :
    curvature y = (1 / 1000000) * rho0 (y / 100) := by
  have hm : qMinus y = 0 := by
    by_contra h
    have hs : y ∈ Function.support qMinus := h
    rw [support_qMinus] at hs
    exact (not_lt_of_ge ((by cas : (105 : ℝ) ≤ 205).trans hy)) hs.2
  have hp : qPlus y = 0 := by
    by_contra h
    have hs : y ∈ Function.support qPlus := h
    rw [support_qPlus] at hs
    exact (not_lt_of_ge hy) hs.2
  have hmneg : qMinus (-y) = 0 := by
    by_contra h
    have hs : -y ∈ Function.support qMinus := h
    rw [support_qMinus] at hs
    have hneg : -y ≤ 100 := by cas using hy
    exact (not_lt_of_ge hneg) hs.1
  have hpneg : qPlus (-y) = 0 := by
    by_contra h
    have hs : -y ∈ Function.support qPlus := h
    rw [support_qPlus] at hs
    have hneg : -y ≤ 200 := by cas using hy
    exact (not_lt_of_ge hneg) hs.1
  simp only [curvature, hm, hp, hmneg, hpneg, mul_zero, add_zero, zero_div, zero_add]

/-- The second derivative is the scaled density, which lies between zero and `10⁻⁶`. -/
theorem deriv_deriv_g_mem_Icc_gate {y : ℝ} (hy : y ∈ Icc (205 : ℝ) (2051 / 10)) :
    deriv (deriv g) y ∈ Icc (0 : ℝ) (1 / 1000000) := by
  rw [deriv_deriv_g, curvature_of_205_le hy.1]
  have hr : rho0 (y / 100) ∈ Icc (0 : ℝ) 1 := ⟨(rho0_pos (y / 100)).le, rho0_le_one (y / 100)⟩
  generalize rho0 (y / 100) = r at hr ⊢
  cega [enclose r in [0, 1] ] ((1 / 1000000 : ℝ) * r)

end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.MiddleClock
