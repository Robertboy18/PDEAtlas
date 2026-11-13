/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Convex truncations of a Dirichlet weight

The primitive of a smooth increasing transition vanishes below `ε`, has slope
between zero and one, and approximates the identity on the nonnegative half-line
with error at most `2ε`. Applied to a positive Dirichlet eigenfunction, these
truncations give tests supported strictly inside the domain.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace HeatEquation.Nonlinear

/-- A smooth convex approximation to the positive part, with a flat interval
extending to the positive threshold `ε`. -/
def convexTruncation (ε s : ℝ) : ℝ :=
  ∫ r in 0..s, Real.smoothTransition ((r - ε) / ε)

private theorem contDiff_transition (ε : ℝ) :
    ContDiff ℝ 1 (fun r ↦ Real.smoothTransition ((r - ε) / ε)) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const ε)

/-- The derivative of the truncation is the smooth transition. -/
theorem hasDerivAt_convexTruncation (ε s : ℝ) :
    HasDerivAt (convexTruncation ε) (Real.smoothTransition ((s - ε) / ε)) s := by
  have hc := (contDiff_transition ε).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 s)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- The truncation is twice continuously differentiable. -/
theorem contDiff_convexTruncation (ε : ℝ) : ContDiff ℝ 2 (convexTruncation ε) := by
  apply (contDiff_succ_iff_deriv (n := 1)).mpr
  refine ⟨fun s ↦ (hasDerivAt_convexTruncation ε s).differentiableAt, by simp, ?_⟩
  have heq : deriv (convexTruncation ε) =
      fun r ↦ Real.smoothTransition ((r - ε) / ε) :=
    funext fun r ↦ (hasDerivAt_convexTruncation ε r).deriv
  rw [heq]
  exact contDiff_transition ε

/-- The truncation vanishes below its positive threshold. -/
theorem convexTruncation_eq_zero {ε s : ℝ} (hε : 0 < ε) (hs : s ≤ ε) :
    convexTruncation ε s = 0 := by
  apply intervalIntegral.integral_zero_ae
  filter_upwards with r hr
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg _ hε.le
  have hrle : r ≤ max 0 s := hr.2
  exact sub_nonpos.mpr (hrle.trans (max_le hε.le hs))

/-- The truncation lies between zero and the identity on the nonnegative half-line. -/
theorem convexTruncation_bounds {ε s : ℝ} (hs : 0 ≤ s) :
    0 ≤ convexTruncation ε s ∧ convexTruncation ε s ≤ s := by
  refine ⟨intervalIntegral.integral_nonneg_of_forall hs
    (fun r ↦ Real.smoothTransition.nonneg _), ?_⟩
  have h := intervalIntegral.integral_mono_on (μ := volume) hs
    ((contDiff_transition ε).continuous.intervalIntegrable 0 s)
    (intervalIntegrable_const (c := (1 : ℝ)))
    (fun r _ ↦ Real.smoothTransition.le_one ((r - ε) / ε))
  simpa only [convexTruncation, intervalIntegral.integral_const, sub_zero,
    smul_eq_mul, mul_one] using h

/-- The uniform error of the convex truncation is at most twice its threshold. -/
theorem sub_two_mul_le_convexTruncation {ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) :
    s - 2 * ε ≤ convexTruncation ε s := by
  by_cases h : s ≤ 2 * ε
  · exact (sub_nonpos.mpr h).trans (convexTruncation_bounds hs).1
  have hle : 2 * ε ≤ s := (lt_of_not_ge h).le
  have hc := (contDiff_transition ε).continuous
  have heq : (∫ r in 2 * ε..s, Real.smoothTransition ((r - ε) / ε)) = s - 2 * ε := by
    calc
      _ = ∫ _r in 2 * ε..s, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro r hr
        rw [uIcc_of_le hle] at hr
        apply Real.smoothTransition.one_of_one_le
        exact (one_le_div hε).mpr (by linarith [hr.1])
      _ = _ := by simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 (2 * ε)) (hc.intervalIntegrable (2 * ε) s)
  rw [heq] at hadd
  have hn := (convexTruncation_bounds (ε := ε) (show 0 ≤ 2 * ε by positivity)).1
  change convexTruncation ε (2 * ε) + (s - 2 * ε) = convexTruncation ε s at hadd
  linarith

/-- Convexity of the transition primitive gives a nonnegative second derivative. -/
theorem deriv_deriv_convexTruncation_nonneg {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    0 ≤ deriv (deriv (convexTruncation ε)) s := by
  have heq : deriv (convexTruncation ε) =
      fun r ↦ Real.smoothTransition ((r - ε) / ε) :=
    funext fun r ↦ (hasDerivAt_convexTruncation ε r).deriv
  rw [heq]
  apply Monotone.deriv_nonneg
  intro x y hxy
  exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right
    (sub_le_sub_right hxy ε) hε.le)

end HeatEquation.Nonlinear
