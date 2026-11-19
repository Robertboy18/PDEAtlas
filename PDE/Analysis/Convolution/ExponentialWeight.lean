/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Differentiation of a weighted translate with exponential decay

Let `B` be of class `C¹` on the line with `|B (x)|, |B' (x)| ≤ C exp (-a |x|)`, and let `w` be a
weight with `w (t) exp (-b |t|)` integrable, where `0 ≤ b ≤ a`. Then `x ↦ ∫ w (t) B (x + t) dt`
is differentiable, with the derivative `∫ w (t) B' (x + t) dt` under the integral sign
(`PDE.Analysis.hasDerivAt_integral_mul_comp_add`). The theorem holds for all such `w`, `B`, `a`,
`b` and `C`. The weight need not be bounded or continuous, and neither function has compact
support. The derivatives of convolutions in `PDE.Analysis.Convolution.DirectionalDerivative` and
`PDE.Analysis.Convolution.ParameterDerivative` ask compact support instead. The result is
standard and follows no particular source.

## How it works

The triangle inequality `|t| ≤ |x + t| + |x|` gives
`exp (-a |x + t|) ≤ exp (b |x|) exp (-b |t|)`. For `x` in a ball around `x₀` the integrand and
its derivative in `x` are therefore bounded by a constant times `|w (t)| exp (-b |t|)`, which
is integrable, and Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le` applies.
-/

@[expose] public section

open MeasureTheory Set Filter Real Topology

namespace PDE.Analysis

private theorem exp_neg_mul_abs_add_le {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) (y t : ℝ) :
    exp (-a * |y + t|) ≤ exp (b * |y|) * exp (-b * |t|) := by
  rw [← exp_add, exp_le_exp]
  have h : |t| ≤ |y + t| + |y| := by
    have h := abs_sub (y + t) y
    rwa [add_sub_cancel_left] at h
  linarith [mul_le_mul_of_nonneg_left h hb,
    mul_le_mul_of_nonneg_right hba (abs_nonneg (y + t))]

/-- **Differentiation under the integral of a weighted translate.** Let `0 ≤ b ≤ a`, let `w` be
a weight with `w (t) exp (-b |t|)` integrable, and let `B` be of class `C¹` with
`|B (x)|, |B' (x)| ≤ C exp (-a |x|)`. Then `x ↦ ∫ w (t) B (x + t) dt` has the derivative
`∫ w (t) B' (x + t) dt` at every point. -/
theorem hasDerivAt_integral_mul_comp_add {w B : ℝ → ℝ} {a b C : ℝ} (hb : 0 ≤ b) (hba : b ≤ a)
    (hw : Integrable fun t ↦ w t * exp (-b * |t|)) (hB : ContDiff ℝ 1 B)
    (hBC : ∀ x, |B x| ≤ C * exp (-a * |x|)) (hB' : ∀ x, |deriv B x| ≤ C * exp (-a * |x|))
    (x : ℝ) :
    HasDerivAt (fun x ↦ ∫ t, w t * B (x + t)) (∫ t, w t * deriv B (x + t)) x := by
  have hC : 0 ≤ C := by simpa using (abs_nonneg (B 0)).trans (hBC 0)
  have hwm : AEStronglyMeasurable w volume := by
    have h := hw.aestronglyMeasurable.mul
      (by fun_prop : Continuous fun t : ℝ ↦ exp (b * |t|)).aestronglyMeasurable
    refine h.congr (Eventually.of_forall fun t ↦ ?_)
    change w t * exp (-b * |t|) * exp (b * |t|) = w t
    rw [mul_assoc, ← exp_add, neg_mul, neg_add_cancel, exp_zero, mul_one]
  have key : ∀ g : ℝ → ℝ, (∀ y, |g y| ≤ C * exp (-a * |y|)) → ∀ y t : ℝ,
      ‖w t * g (y + t)‖ ≤ C * exp (b * |y|) * ‖w t * exp (-b * |t|)‖ := by
    intro g hg y t
    rw [norm_mul, norm_mul, Real.norm_eq_abs (g (y + t)), Real.norm_of_nonneg (exp_pos _).le]
    calc ‖w t‖ * |g (y + t)| ≤ ‖w t‖ * (C * (exp (b * |y|) * exp (-b * |t|))) :=
          mul_le_mul_of_nonneg_left ((hg _).trans
            (mul_le_mul_of_nonneg_left (exp_neg_mul_abs_add_le hb hba y t) hC)) (norm_nonneg _)
      _ = C * exp (b * |y|) * (‖w t‖ * exp (-b * |t|)) := by ring
  have hBm : ∀ y, AEStronglyMeasurable (fun t ↦ w t * B (y + t)) volume := fun y ↦
    hwm.mul (hB.continuous.comp (continuous_const_add y)).aestronglyMeasurable
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y t ↦ w t * B (y + t)) (F' := fun y t ↦ w t * deriv B (y + t))
    (bound := fun t ↦ C * exp (b * (|x| + 1)) * ‖w t * exp (-b * |t|)‖)
    (Metric.ball_mem_nhds x one_pos) (Eventually.of_forall hBm) ?_ ?_ ?_ ?_ ?_).2
  · exact (hw.norm.const_mul _).mono' (hBm x) (Eventually.of_forall fun t ↦ key B hBC x t)
  · exact hwm.mul (hB.continuous_deriv_one.comp (continuous_const_add x)).aestronglyMeasurable
  · refine Eventually.of_forall fun t y hy ↦ (key _ hB' y t).trans ?_
    rw [Metric.mem_ball, Real.dist_eq] at hy
    have hy' : |y| ≤ |x| + 1 := by linarith [abs_sub_abs_le_abs_sub y x]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hy' hb)) hC)
      (norm_nonneg _)
  · exact hw.norm.const_mul _
  · exact Eventually.of_forall fun t y _ ↦
      ((hB.differentiable_one (y + t)).hasDerivAt.comp_add_const y t).const_mul (w t)

end PDE.Analysis
