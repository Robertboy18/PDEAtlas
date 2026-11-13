/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Local integrability from bounds on compact sets

Bounds are imposed only on the set carrying the restricted measure. Thus they
control integrability near its boundary without imposing values outside it.
A continuous map on a proper normed state space preserves these local bounds.
-/

@[expose] public section

open MeasureTheory Set

namespace MeasureTheory

variable {X E F : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [OpensMeasurableSpace X] [T2Space X] [LocallyCompactSpace X]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {s : Set X}

/-- Measurability and bounds on every compact set give local integrability
for the restricted measure, including at points of the boundary of `s`. -/
theorem locallyIntegrable_restrict_of_bound_on_compacts
    (hs : MeasurableSet s) {f : X → E} (hf : AEStronglyMeasurable f (μ.restrict s))
    (hbound : ∀ K : Set X, IsCompact K →
      ∃ C : ℝ, ∀ x ∈ K, x ∈ s → ‖f x‖ ≤ C) :
    LocallyIntegrable f (μ.restrict s) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  obtain ⟨C, hC⟩ := hbound K hK
  have hc : IntegrableOn (fun _ : X ↦ C) K (μ.restrict s) :=
    integrableOn_const hK.measure_ne_top
  apply hc.mono' hf.restrict
  filter_upwards [ae_restrict_mem hK.measurableSet,
    ae_restrict_of_ae (self_mem_ae_restrict hs)] with x hx hxs
  exact hC x hx hxs

/-- A continuous map on a proper normed space takes locally bounded measurable
states to locally integrable fields for the restricted measure. -/
theorem locallyIntegrable_comp_restrict_of_bound_on_compacts [ProperSpace E]
    (hs : MeasurableSet s) {u : X → E} (hu : AEStronglyMeasurable u (μ.restrict s))
    (hbound : ∀ K : Set X, IsCompact K →
      ∃ C : ℝ, ∀ x ∈ K, x ∈ s → ‖u x‖ ≤ C)
    {f : E → F} (hf : Continuous f) :
    LocallyIntegrable (fun x ↦ f (u x)) (μ.restrict s) := by
  apply locallyIntegrable_restrict_of_bound_on_compacts hs (hf.comp_aestronglyMeasurable hu)
  intro K hK
  obtain ⟨C, hC⟩ := hbound K hK
  obtain ⟨B, hB⟩ := ((isCompact_closedBall (0 : E) C).image hf).isBounded.exists_norm_le
  refine ⟨B, fun x hx hxs ↦ hB _ ⟨u x, ?_, rfl⟩⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using hC x hx hxs

end MeasureTheory
