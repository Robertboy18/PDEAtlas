/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import PDE.Analysis.Integration.BumpMoments.NormalizedPulse.Transition

/-!
# A smooth clock density with rational tails

The normalized pulse primitive switches the denominator from one to `1 + s²`.
The resulting density is even, strictly positive, and at most one. Its flat
central region supports the quadratic clock, while its rational tails make the
clock curvature integrable. On the positive half-line, the central contribution
is at most two and comparison with `s⁻²` bounds the remaining integral by one half.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff Interval

namespace PDE.Analysis.ClockDensity

/-- The clock density, using the primitive of the normalized pulse. -/
def rho0 (s : ℝ) : ℝ :=
  (1 + s ^ 2 * NormalizedPulse.transition ((s ^ 2 - 1) / 3))⁻¹

private theorem one_le_denominator (s : ℝ) :
    1 ≤ 1 + s ^ 2 * NormalizedPulse.transition ((s ^ 2 - 1) / 3) :=
  le_add_of_nonneg_right (mul_nonneg (sq_nonneg s) (NormalizedPulse.transition_nonneg _))

/-- The clock density is infinitely differentiable on the whole real line. -/
theorem contDiff_rho0 : ContDiff ℝ ∞ rho0 := by
  have harg : ContDiff ℝ ∞ (fun s : ℝ ↦ (s ^ 2 - 1) / 3) :=
    ((contDiff_id.pow 2).sub contDiff_const).div_const 3
  have hden : ContDiff ℝ ∞ (fun s : ℝ ↦ 1 + s ^ 2 * NormalizedPulse.transition ((s ^ 2 - 1) / 3)) :=
    contDiff_const.add ((contDiff_id.pow 2).mul (NormalizedPulse.contDiff_transition.comp harg))
  exact hden.inv (fun s ↦ (zero_lt_one.trans_le (one_le_denominator s)).ne')

/-- The clock curvature never vanishes, including outside the transition region. -/
theorem rho0_pos (s : ℝ) : 0 < rho0 s :=
  inv_pos.mpr (zero_lt_one.trans_le (one_le_denominator s))

/-- The clock density is bounded above by one everywhere. -/
theorem rho0_le_one (s : ℝ) : rho0 s ≤ 1 :=
  inv_le_one_of_one_le₀ (one_le_denominator s)

/-- The density is exactly one throughout the closed central interval. -/
theorem rho0_eq_one_of_abs_le_one {s : ℝ} (hs : |s| ≤ 1) : rho0 s = 1 := by
  have harg : (s ^ 2 - 1) / 3 ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr ((sq_le_one_iff_abs_le_one s).2 hs)) (by norm_num)
  simp only [rho0, NormalizedPulse.transition_of_nonpos harg, mul_zero, add_zero, inv_one]

/-- Outside the transition interval, the density is the prescribed rational tail. -/
theorem rho0_eq_inv_one_add_sq_of_two_le_abs {s : ℝ} (hs : 2 ≤ |s|) :
    rho0 s = (1 + s ^ 2)⁻¹ := by
  have hsq : (2 : ℝ) ^ 2 ≤ s ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg s)).2 hs
  have harg : 1 ≤ (s ^ 2 - 1) / 3 := by linarith
  simp only [rho0, NormalizedPulse.transition_of_one_le harg, mul_one]

/-- Reflection leaves the clock density unchanged. -/
theorem rho0_neg (s : ℝ) : rho0 (-s) = rho0 s := by
  simp only [rho0, neg_sq]

private theorem rho0_le_cauchy_majorant (s : ℝ) :
    rho0 s ≤ 5 * (1 + s ^ 2)⁻¹ := by
  have hpos : 0 < 1 + s ^ 2 := by nlinarith [sq_nonneg s]
  by_cases hs : |s| ≤ 2
  · have hsq : s ^ 2 ≤ (2 : ℝ) ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg s) (by norm_num : (0 : ℝ) ≤ 2)).2 hs
    have hmajor : (1 : ℝ) ≤ 5 / (1 + s ^ 2) := by
      apply (le_div_iff₀ hpos).2
      nlinarith
    exact (rho0_le_one s).trans (by simpa only [div_eq_mul_inv] using hmajor)
  · rw [rho0_eq_inv_one_add_sq_of_two_le_abs (le_of_not_ge hs)]
    nlinarith [inv_pos.mpr hpos]

/-- The rational tails give an integrable density on the entire real line. -/
theorem integrable_rho0 : Integrable rho0 := by
  refine (integrable_inv_one_add_sq.const_mul (5 : ℝ)).mono'
    contDiff_rho0.continuous.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun s ↦ by
    simpa only [Real.norm_eq_abs, abs_of_pos (rho0_pos s)] using rho0_le_cauchy_majorant s

private theorem integral_zero_two_rho0_le :
    (∫ s in (0 : ℝ)..2, rho0 s) ≤ 2 := by
  calc
    (∫ s in (0 : ℝ)..2, rho0 s) ≤ ∫ s in (0 : ℝ)..2, (1 : ℝ) :=
      intervalIntegral.integral_mono_on (by norm_num)
        (contDiff_rho0.continuous.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _) (fun s _ ↦ rho0_le_one s)
    _ = 2 := by norm_num

/-- The positive rational tail contributes at most one half to the total mass. -/
theorem integral_Ioi_two_rho0_le :
    (∫ s : ℝ in Ioi (2 : ℝ), rho0 s) ≤ 1 / 2 := by
  have hpow : IntegrableOn (fun s : ℝ ↦ s ^ (-2 : ℝ)) (Ioi (2 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  calc
    (∫ s : ℝ in Ioi (2 : ℝ), rho0 s) ≤ ∫ s : ℝ in Ioi (2 : ℝ), s ^ (-2 : ℝ) := by
      refine setIntegral_mono_on integrable_rho0.integrableOn hpow measurableSet_Ioi fun s hs ↦ ?_
      have hspos : 0 < s := lt_trans (by norm_num : (0 : ℝ) < 2) hs
      have habs : 2 ≤ |s| := by
        rw [abs_of_pos hspos]
        exact hs.le
      rw [rho0_eq_inv_one_add_sq_of_two_le_abs habs, Real.rpow_neg hspos.le, Real.rpow_two]
      exact inv_anti₀ (pow_pos hspos 2) (by linarith)
    _ = -(2 : ℝ) ^ ((-2 : ℝ) + 1) / ((-2 : ℝ) + 1) :=
      integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)
    _ = 1 / 2 := by norm_num [Real.rpow_neg_one]

/-- The positive half-line has mass at most `5 / 2`, with no extra density assumptions. -/
theorem integral_Ioi_zero_rho0_le :
    (∫ s : ℝ in Ioi (0 : ℝ), rho0 s) ≤ 5 / 2 := by
  calc
    (∫ s : ℝ in Ioi (0 : ℝ), rho0 s) =
        (∫ s in (0 : ℝ)..2, rho0 s) + (∫ s : ℝ in Ioi (2 : ℝ), rho0 s) :=
      (intervalIntegral.integral_interval_add_Ioi
        integrable_rho0.integrableOn integrable_rho0.integrableOn).symm
    _ ≤ 2 + 1 / 2 := add_le_add integral_zero_two_rho0_le integral_Ioi_two_rho0_le
    _ = 5 / 2 := by norm_num

end PDE.Analysis.ClockDensity
