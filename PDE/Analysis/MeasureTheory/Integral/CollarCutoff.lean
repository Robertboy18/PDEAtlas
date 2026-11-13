/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Vanishing lower-order collar terms

A bounded transverse cutoff, zero beyond unit height, tends to zero at every
point of positive height as the collar thickness tends to zero. Dominated
convergence applies to any integrable coefficient supported at positive height.
The coefficient may be an L² pairing; no boundary values of either factor occur.
-/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A uniformly bounded cutoff of a shrinking positive collar kills any
integrable coefficient supported where the height is positive. -/
theorem tendsto_integral_collar_cutoff_mul_zero
    {d F : X → ℝ} {χ : ℝ → ℝ} {C : ℝ}
    (hd : Measurable d) (hF : Integrable F μ) (hχ : Continuous χ)
    (hbound : ∀ s, ‖χ s‖ ≤ C) (hzero : ∀ s, 1 ≤ s → χ s = 0)
    (hpos : ∀ᵐ x ∂μ, F x ≠ 0 → 0 < d x) :
    Tendsto (fun t : ℝ ↦ ∫ x, χ (d x / t) * F x ∂μ) (𝓝[>] 0) (𝓝 0) := by
  have hlim : ∀ᵐ x ∂μ,
      Tendsto (fun t : ℝ ↦ χ (d x / t) * F x) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    filter_upwards [hpos] with x hx
    by_cases hFx : F x = 0
    · simpa only [hFx, mul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (0 : ℝ)) (𝓝[>] 0) (𝓝 0))
    · apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (eventually_lt_nhds (hx hFx))] with t ht htd
      rw [hzero _ ((le_div_iff₀ ht).mpr (by simpa using htd.le)), zero_mul]
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (fun x ↦ C * ‖F x‖)
    (Filter.Eventually.of_forall fun t ↦
      ((hχ.measurable.comp (hd.div_const t)).aestronglyMeasurable).mul
        hF.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t ↦ Filter.Eventually.of_forall fun x ↦ by
      simp only [Pi.mul_apply, Function.comp_apply, norm_mul]
      exact mul_le_mul_of_nonneg_right (hbound _) (norm_nonneg _))
    (hF.norm.const_mul C) hlim
  simpa only [integral_zero, Pi.mul_apply, Function.comp_apply] using ht

end MeasureTheory
