/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.MeasureTheory.StronglyMeasurable.Distance
public import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Bochner measurability of weakly continuous maps

In a separable normed space, weak continuity suffices for Bochner measurability.
Closed norm balls are weakly closed, so distances along the map are lower
semicontinuous. The countable distance embedding then gives strong measurability
without asserting continuity for the norm topology.
-/

@[expose] public section

open Set TopologicalSpace

namespace MeasureTheory

/-- A weakly continuous map into a separable real normed space is Bochner
measurable for every measure on its source. -/
theorem aestronglyMeasurable_of_continuous_weakSpace
    {α E : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [SeparableSpace E]
    {f : α → E} (hf : Continuous (fun t ↦ toWeakSpace ℝ E (f t)))
    (μ : Measure α) : AEStronglyMeasurable f μ := by
  apply aestronglyMeasurable_of_aemeasurable_dist
  intro x
  have hdist : LowerSemicontinuous (fun t ↦ dist (f t) x) := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro r
    have hball : IsClosed ((toWeakSpace ℝ E) '' Metric.closedBall x r) := by
      rw [← closure_eq_iff_isClosed, ← (convex_closedBall x r).toWeakSpace_closure ℝ,
        Metric.isClosed_closedBall.closure_eq]
    have hpre := hball.preimage hf
    convert hpre using 1
    ext t
    simp only [mem_preimage, mem_Iic, mem_image, Metric.mem_closedBall,
      (toWeakSpace ℝ E).injective.eq_iff, exists_eq_right]
  exact hdist.measurable.aemeasurable

end MeasureTheory
