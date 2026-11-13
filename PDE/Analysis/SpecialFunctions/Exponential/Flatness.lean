/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import CAS.ExactTactic

/-!
# Real powers multiplying a flat exponential

Multiplication by any real power preserves the smoothness of `expNegInvGlue`.
The exponential dominates the power at zero, and each derivative is a linear
combination of two functions of the same form. Real exponents allow this lemma
to apply to Gaussian kernels in odd as well as even dimensions.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace expNegInvGlue

/-- The flat exponential dominates every real power at zero. -/
theorem tendsto_rpow_mul_zero (a : ℝ) :
    Tendsto (fun x : ℝ ↦ x ^ a * expNegInvGlue x) (𝓝 0) (𝓝 0) := by
  simp only [expNegInvGlue, mul_ite, mul_zero]
  refine tendsto_const_nhds.if ?_
  simp only [not_le]
  change Tendsto (fun x : ℝ ↦ x ^ a * Real.exp (-x⁻¹)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-a) 1 zero_lt_one).comp
    tendsto_inv_nhdsGT_zero
  simpa only [Function.comp_def, ← Real.rpow_neg_eq_inv_rpow, neg_neg, neg_one_mul] using h

/-- Differentiation of a real power times the flat exponential, including its
zero junction. -/
theorem hasDerivAt_rpow_mul (a x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ y ^ a * expNegInvGlue y)
      (a * x ^ (a - 1) * expNegInvGlue x + x ^ (a - 2) * expNegInvGlue x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · simp only [zero_of_nonpos hx.le, mul_zero, add_zero]
    refine (hasDerivAt_const x 0).congr_of_eventuallyEq ?_
    filter_upwards [gt_mem_nhds hx] with y hy
    simp [zero_of_nonpos hy.le]
  · simp only [expNegInvGlue.zero, mul_zero, add_zero]
    rw [hasDerivAt_iff_tendsto_slope]
    refine ((tendsto_rpow_mul_zero (a - 1)).mono_left inf_le_left).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : y ≠ 0 := hy
    simp only [slope_def_field, expNegInvGlue.zero, mul_zero, sub_zero]
    rw [Real.rpow_sub_one hy0]
    exact div_mul_eq_mul_div _ _ _
  · have hbranch : (fun y : ℝ ↦ y ^ a * expNegInvGlue y) =ᶠ[𝓝 x]
        fun y ↦ y ^ a * Real.exp (-y⁻¹) := by
      filter_upwards [lt_mem_nhds hx] with y hy
      simp [expNegInvGlue, hy.not_ge]
    rw [expNegInvGlue, ite_eq_right hx.not_ge]
    apply HasDerivAt.congr_of_eventuallyEq _ hbranch
    cas using hx

/-- Arbitrary real powers preserve the infinite smoothness of the flat exponential. -/
theorem contDiff_rpow_mul {m : ℕ∞} (a : ℝ) :
    ContDiff ℝ m (fun x : ℝ ↦ x ^ a * expNegInvGlue x) := by
  apply contDiff_all_iff_nat.2 (fun k ↦ ?_) m
  induction k generalizing a with
  | zero =>
    exact contDiff_zero.2 (continuous_iff_continuousAt.2
      fun x ↦ (hasDerivAt_rpow_mul a x).continuousAt)
  | succ k ih =>
    rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = k + 1 from rfl]
    refine contDiff_succ_iff_deriv.2
      ⟨fun x ↦ (hasDerivAt_rpow_mul a x).differentiableAt, by simp, ?_⟩
    have hderiv : deriv (fun x : ℝ ↦ x ^ a * expNegInvGlue x) =
        fun x ↦ a * (x ^ (a - 1) * expNegInvGlue x) +
          x ^ (a - 2) * expNegInvGlue x := by
      funext x
      rw [(hasDerivAt_rpow_mul a x).deriv, mul_assoc]
    rw [hderiv]
    exact (contDiff_const.mul (ih (a - 1))).add (ih (a - 2))

end expNegInvGlue
