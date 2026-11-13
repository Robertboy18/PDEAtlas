/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Prod
public import PDE.Parabolic.Heat.MeanValue.Geometry
import PDE.Analysis.MeasureTheory.SpaceTime
import PDE.Parabolic.Heat.MeanValue.Topology

/-!
# Fubini slicing of heat-ball integrals

Canonical spacetime stores time in coordinate zero.  After transporting
Euclidean volume to `ℝ × ℝ^n`, the exact slice theorem identifies the
heat-ball indicator with the indicator of Evans's backward time interval
followed by the indicator of the corresponding spatial ball.  Fubini's
theorem then gives an iterated integral over time and spatial balls, for any
integrable integrand.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.2, definition of the heat ball.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (SpaceTime)

noncomputable section

namespace HeatEquation

open PDE.Common
open MeasureTheory

variable {n : ℕ}

/-- A heat-ball indicator at `(s, y)` is the indicator of the backward time
interval followed by the indicator of the spatial slice ball. -/
private theorem heatBall_indicator_timeSpaceCons
    (hn : 0 < n) {x : ℝ^n} {t r : ℝ} (hr : 0 < r)
    {E : Type*} [NormedAddCommGroup E] (F : SpaceTime n → E) (s : ℝ) (y : ℝ^n) :
    (heatBall x t r).indicator F (timeSpaceCons s y) =
      (Set.Ioo (t - r ^ 2 / (4 * Real.pi)) t).indicator
        (fun s ↦
          (Metric.ball x (heatBallSliceRadius n r (t - s))).indicator
            (fun y ↦ F (timeSpaceCons s y)) y)
        s := by
  by_cases hs : s ∈ Set.Ioo (t - r ^ 2 / (4 * Real.pi)) t
  · have hslice := timeSpaceCons_mem_heatBall_iff_mem_ball (x := x) (y := y) hn hr hs
    by_cases hy : y ∈ Metric.ball x (heatBallSliceRadius n r (t - s))
    · simp [hs, hy, hslice.2 hy]
    · simp [hs, hy, mt hslice.1 hy]
  · have hp : timeSpaceCons s y ∉ heatBall x t r := fun hp ↦
      hs (time_mem_Ioo_of_mem_heatBall hn hr hp)
    simp [hs, hp]

/-- The sliced indicator of an integrable heat-ball function is integrable on
`ℝ × ℝ^n`. -/
private theorem integrable_heatBall_slice_indicator
    (hn : 0 < n) {x : ℝ^n} {t r : ℝ} (hr : 0 < r)
    {E : Type*} [NormedAddCommGroup E]
    (F : SpaceTime n → E)
    (hF : IntegrableOn F (heatBall x t r)
      (volume : Measure (SpaceTime n))) :
    Integrable (fun q : ℝ × ℝ^n ↦
      (Set.Ioo (t - r ^ 2 / (4 * Real.pi)) t).indicator
        (fun s ↦
          (Metric.ball x (heatBallSliceRadius n r (t - s))).indicator
            (fun y ↦ F (timeSpaceCons s y)) q.2)
        q.1)
      ((volume : Measure ℝ).prod (volume : Measure (ℝ^n))) := by
  let A : SpaceTime n ≃L[ℝ] ℝ × ℝ^n := timeSpaceContinuousLinearEquiv n
  have hA : MeasurePreserving (A : SpaceTime n → ℝ × ℝ^n) volume volume :=
    PDE.Common.measurePreserving_timeSpaceContinuousLinearEquiv (n := n)
  rw [← Measure.volume_eq_prod ℝ (ℝ^n)]
  exact (((hA.symm A.toHomeomorph.toMeasurableEquiv).integrable_comp_emb
    A.symm.toHomeomorph.measurableEmbedding).2
      (hF.integrable_indicator (isOpen_heatBall hr).measurableSet)).congr
    (.of_forall fun q ↦ heatBall_indicator_timeSpaceCons hn hr F q.1 q.2)

/-- Fubini decomposition of an integrable heat-ball integral into its exact
Euclidean spatial slices. -/
theorem setIntegral_heatBall_eq_integral_slices
    (hn : 0 < n) {x : ℝ^n} {t r : ℝ} (hr : 0 < r)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : SpaceTime n → E)
    (hF : IntegrableOn F (heatBall x t r)
      (volume : Measure (SpaceTime n))) :
    (∫ p in heatBall x t r,
        F p ∂(volume : Measure (SpaceTime n))) =
      ∫ s in Set.Ioo (t - r ^ 2 / (4 * Real.pi)) t,
        ∫ y in
          Metric.ball x (heatBallSliceRadius n r (t - s)),
          F (timeSpaceCons s y) ∂(volume : Measure (ℝ^n))
        ∂(volume : Measure ℝ) := by
  let A : SpaceTime n ≃L[ℝ] ℝ × ℝ^n := timeSpaceContinuousLinearEquiv n
  let H : ℝ × ℝ^n → E := fun q ↦
    (Set.Ioo (t - r ^ 2 / (4 * Real.pi)) t).indicator
      (fun s ↦
        (Metric.ball x (heatBallSliceRadius n r (t - s))).indicator
          (fun y ↦ F (timeSpaceCons s y)) q.2)
      q.1
  have hA : MeasurePreserving (A : SpaceTime n → ℝ × ℝ^n) volume volume :=
    PDE.Common.measurePreserving_timeSpaceContinuousLinearEquiv (n := n)
  calc (∫ p in heatBall x t r, F p) = ∫ q, (heatBall x t r).indicator F (A.symm q) := by
        rw [← integral_indicator (isOpen_heatBall hr).measurableSet]
        exact ((hA.symm A.toHomeomorph.toMeasurableEquiv).integral_comp
          A.symm.toHomeomorph.measurableEmbedding _).symm
    _ = ∫ s, ∫ y, H (s, y) := by
        rw [Measure.volume_eq_prod,
          ← integral_prod H (integrable_heatBall_slice_indicator hn hr F hF)]
        exact integral_congr_ae
          (.of_forall fun q ↦ heatBall_indicator_timeSpaceCons hn hr F q.1 q.2)
    _ = _ := by
        rw [← integral_indicator measurableSet_Ioo]
        refine integral_congr_ae (.of_forall fun s ↦ ?_)
        by_cases hs : s ∈ Set.Ioo (t - r ^ 2 / (4 * Real.pi)) t
        · simp only [H, hs, Set.indicator_of_mem]
          rw [integral_indicator Metric.isOpen_ball.measurableSet]
        · simp [H, hs]

/-- The spatial slice integrals of an integrable heat-ball function are
integrable in time.  This is the integrability half of the same Fubini
argument as `setIntegral_heatBall_eq_integral_slices`. -/
theorem intervalIntegrable_heatBall_slices
    (hn : 0 < n) {x : ℝ^n} {t r : ℝ} (hr : 0 < r)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : SpaceTime n → E)
    (hF : IntegrableOn F (heatBall x t r)
      (volume : Measure (SpaceTime n))) :
    IntervalIntegrable
      (fun s ↦
        ∫ y in
          Metric.ball x (heatBallSliceRadius n r (t - s)),
          F (timeSpaceCons s y) ∂(volume : Measure (ℝ^n)))
      (volume : Measure ℝ)
      (t - r ^ 2 / (4 * Real.pi)) t := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le
      (by linarith [show 0 ≤ r ^ 2 / (4 * Real.pi) by positivity]),
    ← integrable_indicator_iff measurableSet_Ioo]
  refine (integrable_heatBall_slice_indicator hn hr F hF).integral_prod_left.congr
    (.of_forall fun s ↦ ?_)
  by_cases hs : s ∈ Set.Ioo (t - r ^ 2 / (4 * Real.pi)) t
  · simp only [hs, Set.indicator_of_mem]
    rw [integral_indicator Metric.isOpen_ball.measurableSet]
  · simp [hs]

/-- Fubini decomposition of the unit heat ball in positive backward time.

This is the coordinate form used in Watson's flux argument. It follows from
`setIntegral_heatBall_eq_integral_slices` by the substitution `τ = -s`. -/
theorem setIntegral_unitHeatBall_eq_integral_backward_slices
    (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : SpaceTime n → E)
    (hF : IntegrableOn F (heatBall (0 : ℝ^n) 0 1)
      (volume : Measure (SpaceTime n))) :
    (∫ p in heatBall (0 : ℝ^n) 0 1,
        F p ∂(volume : Measure (SpaceTime n))) =
      ∫ τ in Set.Ioo (0 : ℝ) (1 / (4 * Real.pi)),
        ∫ y in
          Metric.ball (0 : ℝ^n) (heatBallSliceRadius n 1 τ),
          F (timeSpaceCons (-τ) y)
            ∂(volume : Measure (ℝ^n))
        ∂(volume : Measure ℝ) := by
  let T : ℝ := 1 / (4 * Real.pi)
  let G : ℝ → E := fun s ↦
    ∫ y in Metric.ball (0 : ℝ^n) (heatBallSliceRadius n 1 (-s)), F (timeSpaceCons s y)
  have hT : 0 < T := by positivity
  calc (∫ p in heatBall (0 : ℝ^n) 0 1, F p) = ∫ s in Set.Ioo (-T) 0, G s := by
        simpa [T, G] using setIntegral_heatBall_eq_integral_slices hn (x := (0 : ℝ^n)) (t := 0)
          zero_lt_one F hF
    _ = ∫ τ in Set.Ioo (0 : ℝ) T, G (-τ) := by
        rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
          ← intervalIntegral.integral_of_le (by linarith : -T ≤ 0),
          ← intervalIntegral.integral_of_le hT.le, intervalIntegral.integral_comp_neg, neg_zero]
    _ = _ := by simp only [T, G, neg_neg]

/-- The backward-time spatial slice integrals of an integrable function on
the unit heat ball are interval integrable. -/
theorem intervalIntegrable_unitHeatBall_backward_slices
    (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : SpaceTime n → E)
    (hF : IntegrableOn F (heatBall (0 : ℝ^n) 0 1)
      (volume : Measure (SpaceTime n))) :
    IntervalIntegrable
      (fun τ ↦
        ∫ y in
          Metric.ball (0 : ℝ^n) (heatBallSliceRadius n 1 τ),
          F (timeSpaceCons (-τ) y)
            ∂(volume : Measure (ℝ^n)))
      (volume : Measure ℝ) 0 (1 / (4 * Real.pi)) := by
  let G : ℝ → E := fun s ↦
    ∫ y in Metric.ball (0 : ℝ^n)
        (heatBallSliceRadius n 1 (-s)),
      F (timeSpaceCons s y) ∂(volume : Measure (ℝ^n))
  have hforward :
      IntervalIntegrable G (volume : Measure ℝ)
        (-(1 / (4 * Real.pi))) 0 := by
    simpa [G] using
      intervalIntegrable_heatBall_slices
        (n := n) hn (x := (0 : ℝ^n)) (t := 0) (r := 1)
        zero_lt_one F hF
  have hbackward :
      IntervalIntegrable (fun τ ↦ G (-τ))
        (volume : Measure ℝ) (1 / (4 * Real.pi)) 0 := by
    simpa only [neg_neg, neg_zero] using
      (IntervalIntegrable.iff_comp_neg).mp hforward
  simpa [G] using hbackward.symm

end HeatEquation
