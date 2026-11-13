/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import PDE.Common.Euclidean

/-!
# Convolution with bounded sources continuous almost everywhere

A locally integrable kernel convolved with a bounded compact source is continuous
when the source is continuous outside a null set. After translating the kernel
variable, dominated convergence ignores the source's null set of discontinuities.
This includes piecewise continuous sources whose jumps lie on hyperplanes.

## Main results

* `continuous_convolution_of_ae_continuousAt`: a bounded compactly supported source that is
  continuous almost everywhere has a continuous convolution with any locally integrable scalar
  kernel.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Convolution

namespace PDE.Analysis

/-- A bounded compact source continuous almost everywhere has a continuous
convolution with any locally integrable scalar kernel. -/
theorem continuous_convolution_of_ae_continuousAt
    {n : ℕ} {K F : ℝ^n → ℝ} (hK : LocallyIntegrable K volume)
    (hF : AEStronglyMeasurable F volume) (hc : HasCompactSupport F)
    {M : ℝ} (hbound : ∀ y, ‖F y‖ ≤ M)
    (hcont : ∀ᵐ y ∂volume, ContinuousAt F y) :
    Continuous (K ⋆[ContinuousLinearMap.mul ℝ ℝ] F) := by
  obtain ⟨R, _, hR⟩ := hc.isCompact.isBounded.exists_pos_norm_le
  refine continuous_iff_continuousAt.mpr fun x₀ ↦ ?_
  let B := Metric.closedBall (0 : ℝ^n) (‖x₀‖ + 1 + R)
  have hbi : Integrable (B.indicator (fun y ↦ ‖K y‖ * M)) volume := by
    apply (integrable_indicator_iff measurableSet_closedBall).2
    exact (hK.integrableOn_isCompact (isCompact_closedBall _ _)).norm.mul_const M
  have hb : ∀ᶠ x in 𝓝 x₀, ∀ᵐ y ∂volume,
      ‖K y * F (x - y)‖ ≤ B.indicator (fun y ↦ ‖K y‖ * M) y := by
    filter_upwards [Metric.ball_mem_nhds x₀ (show (0 : ℝ) < 1 by norm_num)] with x hx
    filter_upwards with y
    by_cases hy : y ∈ B
    · rw [indicator_of_mem hy, norm_mul]
      exact mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)
    · rw [indicator_of_notMem hy]
      have hzero : F (x - y) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        have hxy := hR (x - y) hmem
        have hdist : ‖x - x₀‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hx
        have hxnorm : ‖x‖ ≤ ‖x - x₀‖ + ‖x₀‖ := by
          calc
            ‖x‖ = ‖(x - x₀) + x₀‖ := by rw [sub_add_cancel]
            _ ≤ _ := norm_add_le _ _
        have hynorm : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
          calc
            ‖y‖ = ‖x - (x - y)‖ := by rw [sub_sub_cancel]
            _ ≤ _ := norm_sub_le _ _
        apply hy
        change dist y 0 ≤ ‖x₀‖ + 1 + R
        rw [dist_zero_right]
        linarith
      simp [hzero]
  change ContinuousAt (fun x ↦ ∫ y, K y * F (x - y)) x₀
  refine continuousAt_of_dominated ?_ hb hbi ?_
  · exact Eventually.of_forall fun x ↦
      hK.aestronglyMeasurable.convolution_integrand_snd (ContinuousLinearMap.mul ℝ ℝ) hF x
  · filter_upwards [(quasiMeasurePreserving_sub_left_of_right_invariant
      (volume : Measure (ℝ^n)) x₀).ae hcont] with y hy
    have hshift : ContinuousAt (fun x : ℝ^n ↦ x - y) x₀ :=
      continuousAt_id.sub continuousAt_const
    exact continuousAt_const.mul (hy.comp (f := fun x : ℝ^n ↦ x - y) hshift)

end PDE.Analysis
