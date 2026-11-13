/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

/-!
# Endpoint remainders from power bounds on the derivative

Integrating a derivative difference bounded by `C xᵖ` gives the factor
`1 / (p + 1)`. Keeping that factor matters when an endpoint cancellation is
used inside an energy estimate. The derivative need not extend continuously
to the endpoint: continuity of the original function and `p > -1` suffice.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PDE.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A power bound on the difference from a fixed slope controls the remainder
at the left endpoint. The exponent may be negative if the bound is integrable. -/
theorem norm_sub_sub_smul_le_of_deriv_power_bound
    {u u' : ℝ → F} {m : F} {x C p : ℝ} (hx : 0 ≤ x) (hp : -1 < p)
    (hu : ContinuousOn u (Icc 0 x))
    (hderiv : ∀ y ∈ Ioo 0 x, HasDerivAt u (u' y) y)
    (hbound : ∀ y ∈ Ioo 0 x, ‖u' y - m‖ ≤ C * y ^ p) :
    ‖u x - u 0 - x • m‖ ≤ C / (p + 1) * x ^ (p + 1) := by
  let v := fun y ↦ u y - y • m
  have hvc : ContinuousOn v (Icc 0 x) := hu.sub (by fun_prop)
  have hvd (y : ℝ) (hy : y ∈ Ioo 0 x) : HasDerivAt v (u' y - m) y := by
    simpa only [v, one_smul, Pi.sub_def, id_eq] using
      (hderiv y hy).sub ((hasDerivAt_id y).smul_const m)
  have h := norm_sub_le_integral_of_norm_deriv_le_of_le hx hvc
    (fun y hy ↦ (hvd y hy).differentiableAt.differentiableWithinAt)
    (Filter.Eventually.of_forall fun y hy ↦ by rw [(hvd y hy).deriv]; exact hbound y hy)
    ((intervalIntegral.intervalIntegrable_rpow' hp).const_mul C)
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hp),
    Real.zero_rpow (by linarith : p + 1 ≠ 0), sub_zero] at h
  have heq : v x - v 0 = u x - u 0 - x • m := by
    simp only [v, zero_smul, sub_zero]
    abel
  rw [heq] at h
  exact h.trans_eq (by ring)

/-- Reflection gives the same remainder estimate at a right endpoint. This
retains the exact integration factor for the distance `L - x`. -/
theorem norm_sub_sub_smul_le_of_deriv_power_bound_right
    {u u' : ℝ → F} {m : F} {x L C p : ℝ} (hx : x ≤ L) (hp : -1 < p)
    (hu : ContinuousOn u (Icc x L))
    (hderiv : ∀ y ∈ Ioo x L, HasDerivAt u (u' y) y)
    (hbound : ∀ y ∈ Ioo x L, ‖u' y - m‖ ≤ C * (L - y) ^ p) :
    ‖u x - u L - (x - L) • m‖ ≤ C / (p + 1) * (L - x) ^ (p + 1) := by
  let v := fun y ↦ u (L - y)
  have hvc : ContinuousOn v (Icc 0 (L - x)) := by
    apply hu.comp (by fun_prop)
    intro y hy
    constructor <;> linarith [hy.1, hy.2]
  have hvd (y : ℝ) (hy : y ∈ Ioo 0 (L - x)) :
      HasDerivAt v (-u' (L - y)) y := by
    have hy' : L - y ∈ Ioo x L := by constructor <;> linarith [hy.1, hy.2]
    simpa only [v, Function.comp_def, neg_smul, one_smul] using
      (hderiv (L - y) hy').scomp y ((hasDerivAt_id y).const_sub L)
  have hb (y : ℝ) (hy : y ∈ Ioo 0 (L - x)) :
      ‖-u' (L - y) - -m‖ ≤ C * y ^ p := by
    have hy' : L - y ∈ Ioo x L := by constructor <;> linarith [hy.1, hy.2]
    simpa only [neg_sub_neg, norm_sub_rev, sub_sub_cancel] using hbound (L - y) hy'
  have h := norm_sub_sub_smul_le_of_deriv_power_bound (m := -m)
    (sub_nonneg.mpr hx) hp hvc hvd hb
  simpa only [v, sub_sub_cancel, sub_zero, smul_neg,
    sub_neg_eq_add, sub_smul, neg_sub] using h

end PDE.Analysis
