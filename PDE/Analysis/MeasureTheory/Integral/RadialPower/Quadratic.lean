/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Integral.RadialPower

/-!
# Quadratic estimates with the inverse-radius weight

In three dimensions, Hölder with exponents `3` and `3/2` controls the integral
of `w²/r` by the L⁶ norm of `w`. Haar scaling produces one factor of the ball
radius. No regularity at the singular centre is needed.
-/

@[expose] public noncomputable section

open MeasureTheory Metric
open scoped ENNReal

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- L⁶ control suffices for the inverse-radius term, even when the function has
no value or regularity prescribed at the centre. The constant is independent of
the centre and radius. -/
theorem integral_sq_div_norm_sub_le_of_memLp_six
    (hd : Module.finrank ℝ E = 3) {w : E → ℝ} (c : E) {r : ℝ} (hr : 0 < r)
    (hw : MemLp w 6 (μ.restrict (ball c r))) :
    (∫ x in ball c r, (w x) ^ 2 / ‖x - c‖ ∂μ) ≤
      (∫ x in ball c r, |w x| ^ 6 ∂μ) ^ (1 / 3 : ℝ) *
        ((∫ x in ball (0 : E) 1, ‖x‖ ^ (-(3 / 2) : ℝ) ∂μ) ^ (2 / 3 : ℝ) * r) := by
  have hsq : MemLp (fun x ↦ (w x) ^ 2) (ENNReal.ofReal 3)
      (μ.restrict (ball c r)) := by
    have hdiv : (6 : ℝ≥0∞) / 2 = 3 := by
      calc
        _ = (3 * 2 : ℝ≥0∞) / 2 := by norm_num
        _ = 3 := ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
    simpa [hdiv] using hw.norm_rpow_div 2
  have hpq : (3 : ℝ).HolderConjugate (3 / 2) := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := integral_norm_mul_norm_sub_rpow_le hpq
    (a := -1) (by norm_num [hd]) hr c hsq
  have hexp (x : E) : |(w x) ^ 2| ^ (3 : ℝ) = |w x| ^ 6 := by
    rw [abs_pow, Real.rpow_ofNat, ← pow_mul]
  have hweight (x : E) : |(w x) ^ 2| * ‖x - c‖ ^ (-1 : ℝ) =
      (w x) ^ 2 / ‖x - c‖ := by
    rw [abs_of_nonneg (sq_nonneg _), Real.rpow_neg_one, div_eq_mul_inv]
  simp_rw [hexp, hweight] at h
  norm_num [hd] at h
  exact h

end MeasureTheory
