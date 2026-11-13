/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.InitialValue
import PDE.Parabolic.Heat.Kernel.Integrability
import PDE.Parabolic.Heat.Kernel.Scaling
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Parabolic rescaling of the heat convolution

Dilating space by `r` replaces time `r²s` by `s`. The kernel's factor `r⁻ⁿ`
cancels the volume Jacobian. Translation then centers the rescaled datum at zero.
The identities need no integrability hypothesis: the change of variables preserves
integrability, and a Bochner integral of a non-integrable function is zero.
-/

@[expose] public section

namespace HeatEquation

open MeasureTheory

variable {n : ℕ}

/-- The positive-time heat convolution commutes with a positive spatial dilation
and translation. No integrability hypothesis is needed for this integral identity. -/
theorem initialValueSolution_parabolic_rescale (g : ℝ^n → ℝ) (x : ℝ^n)
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    initialValueSolution g x (r ^ 2 * s) =
      initialValueSolution (fun y ↦ g (x + r • y)) 0 s := by
  have htime : 0 < r ^ 2 * s := mul_pos (sq_pos_of_pos hr) hs
  let f : ℝ^n → ℝ := fun y ↦ fundamentalSolutionHeat (x - y) (r ^ 2 * s) * g y
  have htranslate : (∫ y, f (x + y)) = ∫ y, f y := by
    simpa only [add_comm] using integral_add_right_eq_self f x
  have hdilate := Measure.integral_comp_smul_of_nonneg
    (μ := (volume : Measure (ℝ^n))) (fun y ↦ f (x + y)) r (hR := hr.le)
  have hpow : r ^ (-(n : ℝ)) = (r ^ n)⁻¹ := by
    rw [Real.rpow_neg hr.le, Real.rpow_natCast]
  have hpoint (y : ℝ^n) :
      f (x + r • y) = (r ^ n)⁻¹ *
        (fundamentalSolutionHeat (0 - y) s * g (x + r • y)) := by
    have hspace : x - (x + r • y) = r • (0 - y) := by
      simp only [zero_sub, smul_neg, sub_add_eq_sub_sub, sub_self]
    dsimp only [f]
    rw [hspace, fundamentalSolutionHeat_scaling _ s r hs hr, hpow]
    exact mul_assoc _ _ _
  have heq : (r ^ n)⁻¹ * (∫ y, fundamentalSolutionHeat (0 - y) s *
        g (x + r • y)) = (r ^ n)⁻¹ * ∫ y, f y := by
    simpa only [hpoint, integral_const_mul, htranslate, smul_eq_mul,
      finrank_euclideanSpace_fin] using hdilate
  have hcancel := (mul_left_cancel₀ (inv_ne_zero (pow_ne_zero _ hr.ne')) heq).symm
  simpa only [initialValueSolution, ite_eq_right (not_le.mpr htime),
    ite_eq_right (not_le.mpr hs), f] using hcancel

/-- A fixed Gaussian represents the heat evolution at every time, including
the convention that nonpositive times return the initial datum.

All dependence on time is in the translated and rescaled datum. This form is useful
at time zero: the Gaussian stays integrable as `√t` tends to zero. -/
theorem initialValueSolution_eq_fixed_gaussian (g : ℝ^n → ℝ) (x : ℝ^n) (t : ℝ) :
    initialValueSolution g x t =
      ∫ y : ℝ^n, fundamentalSolutionHeat (0 - y) 1 * g (x + Real.sqrt t • y) := by
  by_cases ht : t ≤ 0
  · simp only [Real.sqrt_eq_zero_of_nonpos ht, zero_smul, add_zero]
    rw [initialValueSolution_of_t_le_zero g x ht, integral_mul_const]
    have hmass : (∫ y : ℝ^n, fundamentalSolutionHeat (0 - y) 1) = 1 := by
      exact
        (integral_sub_left_eq_self (μ := volume)
          (fun y : ℝ^n ↦ fundamentalSolutionHeat y 1) 0).trans
          (fundamentalSolutionHeat_integral 1 zero_lt_one)
    rw [hmass, one_mul]
  · have hpos := lt_of_not_ge ht
    have hscale := initialValueSolution_parabolic_rescale g x
      (s := 1) (r := Real.sqrt t) zero_lt_one (Real.sqrt_pos.2 hpos)
    simpa only [Real.sq_sqrt hpos.le, mul_one, initialValueSolution,
      ite_eq_right (not_le.mpr zero_lt_one)] using hscale

end HeatEquation
