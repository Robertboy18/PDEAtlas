/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.MeanValue

/-!
# A zero trace and a quadratic weight at infinity

A C1 function vanishing at the origin grows at most linearly on each fixed
ball. Local integrability of the weight therefore controls its square after
division by the distance to the origin. Outside that ball, a quadratic upper
bound on the weight reduces the same integral to the unweighted L2 norm.
-/

@[expose] public noncomputable section

namespace MeasureTheory

open Metric Set
open scoped ENNReal

/-- Local integrability of a nonnegative weight and a quadratic upper bound
at infinity suffice for the weighted L2 norm of `f / ‖x‖`. The C1 zero trace
controls the origin; unweighted L2 controls infinity. All weight bounds may
hold only almost everywhere, and the ambient measure need not be finite. -/
theorem memLp_div_norm_mul_sqrt_of_contDiff_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    {ν : Measure E} {f Φ : E → ℝ} {A R : ℝ}
    (hf : ContDiff ℝ 1 f) (hf0 : f 0 = 0) (hfLp : MemLp f 2 ν)
    (hΦ : LocallyIntegrable Φ ν) (hpos : 0 ≤ᵐ[ν] Φ)
    (htail : ∀ᵐ x ∂ν, R < ‖x‖ → Φ x ≤ A * ‖x‖ ^ 2) :
    MemLp (fun x ↦ (f x / ‖x‖) * √(Φ x)) 2 ν := by
  let K := closedBall (0 : E) (max R 0)
  have hK : IsCompact K := isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (contDiff_one_iff_fderiv.mp hf).2.continuousOn
  let B := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  have hlinear (x : E) (hx : x ∈ K) : |f x| ≤ B * ‖x‖ := by
    have h := (convex_closedBall (0 : E) (max R 0)).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ ↦ hf.differentiable (by norm_num) y)
      (fun y hy ↦ (hC y hy).trans (le_max_left C 0))
      (mem_closedBall_self (le_max_right R 0)) hx
    simpa only [hf0, sub_zero, Real.norm_eq_abs] using h
  have hquotient (x : E) (hx : x ∈ K) : |f x / ‖x‖| ≤ B := by
    by_cases hx0 : x = 0
    · simpa only [hx0, norm_zero, div_zero, abs_zero] using hB
    · rw [abs_div, abs_of_nonneg (norm_nonneg x)]
      exact (div_le_iff₀ (norm_pos_iff.mpr hx0)).2 (hlinear x hx)
  have hq : AEStronglyMeasurable (fun x ↦ f x / ‖x‖) ν :=
    (hf.continuous.measurable.div continuous_norm.measurable).aestronglyMeasurable
  have hw : Integrable (K.indicator Φ) ν :=
    (integrable_indicator_iff hK.measurableSet).2 (hΦ.integrableOn_isCompact hK)
  have hdom : Integrable
      (fun x ↦ B ^ 2 * K.indicator Φ x + max A 0 * f x ^ 2) ν :=
    (hw.const_mul (B ^ 2)).add (hfLp.integrable_sq.const_mul (max A 0))
  have henergy : Integrable (fun x ↦ (f x / ‖x‖) ^ 2 * Φ x) ν := by
    refine hdom.mono' ((hq.pow 2).mul hΦ.aestronglyMeasurable) ?_
    filter_upwards [hpos, htail] with x hposx htailx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hposx)]
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      have hsq : (f x / ‖x‖) ^ 2 ≤ B ^ 2 :=
        sq_le_sq.2 ((hquotient x hx).trans (le_abs_self B))
      exact (mul_le_mul_of_nonneg_right hsq hposx).trans
        (le_add_of_nonneg_right (mul_nonneg (le_max_right A 0) (sq_nonneg _)))
    · rw [Set.indicator_of_notMem hx, mul_zero, zero_add]
      have hr : max R 0 < ‖x‖ := by
        simpa only [K, mem_closedBall, dist_zero_right, not_le] using hx
      have hn : ‖x‖ ≠ 0 := ((le_max_right R 0).trans_lt hr).ne'
      have hweight : Φ x ≤ max A 0 * ‖x‖ ^ 2 :=
        (htailx ((le_max_left R 0).trans_lt hr)).trans
          (mul_le_mul_of_nonneg_right (le_max_left A 0) (sq_nonneg _))
      calc
        (f x / ‖x‖) ^ 2 * Φ x ≤
            (f x / ‖x‖) ^ 2 * (max A 0 * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hweight (sq_nonneg _)
        _ = max A 0 * ((f x / ‖x‖) ^ 2 * ‖x‖ ^ 2) := by ring
        _ = max A 0 * f x ^ 2 := by rw [← mul_pow, div_mul_cancel₀ _ hn]
  have hm : AEStronglyMeasurable
      (fun x ↦ (f x / ‖x‖) * √(Φ x)) ν :=
    hq.mul (Real.continuous_sqrt.comp_aestronglyMeasurable hΦ.aestronglyMeasurable)
  apply (memLp_two_iff_integrable_sq hm).2
  apply henergy.congr
  filter_upwards [hpos] with x hx
  simp only [mul_pow, Real.sq_sqrt hx]

end MeasureTheory
