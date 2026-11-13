/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.EuclideanBall
import Mathlib.Analysis.Convolution

/-!
# Integrating local ball bounds

We average a local ball estimate over the centers that can meet a compact set.
Mathlib's convolution integral formula then gives a bound for the integral on
that set. The radius and the measure of the set of centers remain explicit.
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Common
open scoped Convolution

namespace PDE.Analysis

/-- A uniform bound on ball integrals controls the integral over a compact set.
The set of centers contains its open `r`-neighborhood. -/
theorem measure_ball_mul_integral_le_of_local_ball_bound
    {n : ℕ} {r : ℝ} {A B : Set (ℝ^n)} (hA : IsCompact A) (hB : IsCompact B)
    {K : ℝ^n → ℝ} (hK : Continuous K) (hKnonneg : ∀ x, 0 ≤ K x) {C : ℝ}
    (hnear : ∀ x ∈ A, ∀ y, dist x y < r → y ∈ B)
    (hbound : ∀ y ∈ B, (∫ x in Metric.ball y r, K x) ≤ C) :
    volume.real (Metric.ball (0 : ℝ^n) r) * (∫ x in A, K x) ≤ volume.real B * C := by
  classical
  let f : ℝ^n → ℝ := A.indicator K
  let g : ℝ^n → ℝ := (Metric.ball 0 r).indicator (fun _ ↦ 1)
  let F : ℝ^n → ℝ := f ⋆ g
  have hf : Integrable f := (integrable_indicator_iff hA.measurableSet).mpr
    (hK.continuousOn.integrableOn_compact hA)
  have hg : Integrable g := (integrable_indicator_iff measurableSet_ball).mpr
    (integrableOn_const (measure_ball_lt_top.ne))
  have hF : Integrable F := hf.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hg
  have hball (y : ℝ^n) : F y = ∫ x in Metric.ball y r, f x := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards with x
    change f x * g (y - x) = (Metric.ball y r).indicator f x
    have he : y - x ∈ Metric.ball (0 : ℝ^n) r ↔ x ∈ Metric.ball y r := by
      simp only [Metric.mem_ball, dist_eq_norm, sub_zero, norm_sub_rev]
    by_cases hx : x ∈ Metric.ball y r
    · simp only [g, indicator_of_mem (he.mpr hx), indicator_of_mem hx, mul_one]
    · simp only [g, indicator_of_notMem (mt he.mp hx), indicator_of_notMem hx, mul_zero]
  have hpoint (y : ℝ^n) : F y ≤ B.indicator (fun _ ↦ C) y := by
    rw [hball]
    by_cases hy : y ∈ B
    · rw [indicator_of_mem hy]
      apply le_trans ?_ (hbound y hy)
      apply setIntegral_mono_on hf.integrableOn
        ((hK.continuousOn.integrableOn_compact (isCompact_closedBall y r)).mono_set
          Metric.ball_subset_closedBall) measurableSet_ball
      intro x _
      exact indicator_le_self' (fun z _ ↦ hKnonneg z) x
    · rw [indicator_of_notMem hy]
      have hz : (∫ x in Metric.ball y r, f x) = 0 := by
        apply setIntegral_eq_zero_of_forall_eq_zero
        intro x hx
        apply indicator_of_notMem
        intro hxA
        exact hy (hnear x hxA y (Metric.mem_ball.mp hx))
      exact hz.le
  have hi := integral_mono hF
    ((integrable_indicator_iff hB.measurableSet).mpr
      (integrableOn_const hB.measure_ne_top)) hpoint
  have htotal : (∫ y, F y) = (∫ x in A, K x) * volume.real (Metric.ball (0 : ℝ^n) r) := by
    have h := integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf hg
    change (∫ y, F y) = (∫ x, f x) * (∫ x, g x) at h
    simpa only [f, g, integral_indicator hA.measurableSet,
      integral_indicator measurableSet_ball, setIntegral_const, smul_eq_mul, mul_one] using h
  rw [htotal, integral_indicator hB.measurableSet, setIntegral_const, smul_eq_mul] at hi
  simpa only [mul_comm (∫ x in A, K x)] using hi

end PDE.Analysis
