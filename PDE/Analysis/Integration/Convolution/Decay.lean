/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Decay of inverse-distance potentials

The inverse-distance potential of compactly supported integrable data tends to
zero at infinity. Compact support gives a single integrable bound outside a
large ball, so dominated convergence applies for any measure. The normed target
need not be complete.
-/

@[expose] public section

open MeasureTheory Filter Bornology
open scoped Topology

namespace MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [ProperSpace E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} {f : E → F}

/-- The inverse-distance potential of compactly supported integrable data vanishes
at infinity. No local integrability assumption on the bare kernel is required. -/
theorem tendsto_integral_norm_sub_inv_smul (hf : Integrable f μ)
    (hfc : HasCompactSupport f) :
    Tendsto (fun x : E ↦ ∫ y, ‖x - y‖⁻¹ • f y ∂μ) (cocompact E) (𝓝 0) := by
  have : (cocompact E).IsCountablyGenerated := by
    rw [← Metric.cobounded_eq_cocompact, ← comap_norm_atTop]
    infer_instance
  obtain ⟨R, hR⟩ := hfc.isBounded.exists_norm_le
  have hbound : ∀ᶠ x : E in cocompact E, ∀ᵐ y ∂μ,
      ‖‖x - y‖⁻¹ • f y‖ ≤ ‖f y‖ := by
    filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop (R + 1)] with x hx
    apply Eventually.of_forall
    intro y
    by_cases hy : f y = 0
    · simp [hy]
    · have hyR : ‖y‖ ≤ R := hR y (subset_tsupport f (Function.mem_support.mpr hy))
      have hdist : 1 ≤ ‖x - y‖ := by
        have hn := norm_sub_norm_le x y
        linarith
      rw [norm_smul, norm_inv, norm_norm]
      exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ hdist)
  have hlim (y : E) : Tendsto (fun x : E ↦ ‖x - y‖) (cocompact E) atTop := by
    apply tendsto_atTop_mono (fun x ↦ norm_sub_norm_le x y)
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right (cocompact E) (-‖y‖) tendsto_norm_cocompact_atTop
  have h := tendsto_integral_filter_of_dominated_convergence (fun y ↦ ‖f y‖)
    (F := fun x y : E ↦ ‖x - y‖⁻¹ • f y) (f := fun _ ↦ (0 : F))
    (Eventually.of_forall fun x ↦
      ((continuous_const.sub continuous_id).norm.measurable.inv.aestronglyMeasurable.smul
        hf.aestronglyMeasurable)) hbound hf.norm
    (Eventually.of_forall fun y ↦ by
      simpa only [zero_smul, Function.comp_apply] using
        (tendsto_inv_atTop_zero.comp (hlim y)).smul_const (f y))
  simpa only [integral_zero] using h

end MeasureTheory
