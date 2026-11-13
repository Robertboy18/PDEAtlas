/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Measurability of section norms

For a jointly measurable family, the extended Lp norm of each section is a
measurable function of the parameter when the exponent is finite and positive.
This applies to both normed-group-valued and extended-nonnegative-valued families.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

/-- Finite positive spatial Lp norms of a jointly measurable family are measurable. -/
theorem Measurable.eLpNorm_prod_right {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [TopologicalSpace E] [ContinuousENorm E]
    [MeasurableSpace E] [OpensMeasurableSpace E] [SecondCountableTopology E]
    [TopologicalSpace.PseudoMetrizableSpace E]
    {ν : Measure β} [SFinite ν] {f : α × β → E} {p : ℝ≥0∞}
    (hf : Measurable f) (hp₀ : p ≠ 0) (hp_top : p ≠ ∞) :
    Measurable (fun x ↦ eLpNorm (fun y ↦ f (x, y)) p ν) := by
  have heq (x : α) : eLpNorm (fun y ↦ f (x, y)) p ν =
      (∫⁻ y, ‖f (x, y)‖ₑ ^ p.toReal ∂ν) ^ (1 / p.toReal) :=
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp_top
      (hf.comp measurable_prodMk_left).aestronglyMeasurable
  simp_rw [heq]
  exact (hf.enorm.pow_const _).lintegral_prod_right.pow_const _
