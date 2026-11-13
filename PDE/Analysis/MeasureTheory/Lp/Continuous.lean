/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Local Lᵖ membership of continuous functions

Continuity on a compact set bounds the function and gives strong measurability
on every measurable subset. A measure finite on compact sets then gives Lᵖ
membership for every exponent, including infinity.
Composition with a continuous function also preserves essential boundedness
when the source of that function has compact closed balls.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

/-- A function continuous on a compact set belongs to every Lᵖ space on a measurable
subset, for any measure finite on compact sets. The target need not be separable. -/
theorem ContinuousOn.memLp_of_subset_isCompact
    {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {f : X → E} {s t : Set X} {p : ℝ≥0∞}
    (hf : ContinuousOn f s) (hs : IsCompact s) (ht : MeasurableSet t) (hts : t ⊆ s) :
    MemLp f p (μ.restrict t) := by
  let : IsFiniteMeasure (μ.restrict t) := isFiniteMeasure_restrict.mpr
    (ne_top_of_le_ne_top hs.measure_lt_top.ne (measure_mono hts))
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn hf
  exact MemLp.of_bound (hf.aestronglyMeasurable_of_subset_isCompact hs ht hts) C
    ((ae_restrict_mem ht).mono fun x hx ↦ hC x (hts hx))

/-- A continuous function of an essentially bounded field is essentially
bounded when closed balls in its domain are compact. Neither finite measure
nor a zero value of the continuous function at the origin is required. -/
theorem Continuous.comp_memLp_top
    {X E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [ProperSpace E] [NormedAddCommGroup F]
    {μ : Measure X} {f : E → F} {u : X → E}
    (hf : Continuous f) (hu : MemLp u ∞ μ) :
    MemLp (f ∘ u) ∞ μ := by
  have hbound : eLpNormEssSup u μ < ⊤ := by
    simpa only [eLpNorm_exponent_top hu.aestronglyMeasurable] using hu.eLpNorm_lt_top
  obtain ⟨K, hK⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp hbound
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : E) (K : ℝ)).exists_bound_of_continuousOn hf.continuousOn
  apply memLp_top_of_bound (hf.comp_aestronglyMeasurable hu.aestronglyMeasurable) C
  filter_upwards [hK] with x hx
  apply hC (u x)
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    (show ‖u x‖ ≤ (K : ℝ) from hx)
