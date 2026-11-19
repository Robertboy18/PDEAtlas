/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Lifting continuous representatives through a closed embedding

A continuous curve which belongs almost everywhere to a closed embedded
space belongs to it at every time of a nondegenerate closed interval.
Lifting the curve gives a continuous representative in the embedded space.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Topology.IsClosedEmbedding

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  {J : X → Y} {a b : ℝ}

/-- A closed embedding lifts an almost-everywhere continuous representative
to a continuous representative on the whole closed time interval, including
both endpoints. No measurability of the originally chosen representatives
is needed beyond the given almost-everywhere equality. -/
theorem exists_continuousOn_lift_ae_eq (hJ : IsClosedEmbedding J)
    (hab : a < b) (u : ℝ → X) (z : ℝ → Y)
    (hz : ContinuousOn z (Icc a b))
    (hzu : z =ᵐ[volume.restrict (Ioc a b)] J ∘ u) :
    ∃ v : ℝ → X, ContinuousOn v (Icc a b) ∧
      v =ᵐ[volume.restrict (Ioc a b)] u ∧ EqOn (J ∘ v) z (Icc a b) := by
  classical
  have hdist : (fun t ↦ Metric.infDist (z t) (range J)) =ᵐ[
      volume.restrict (Icc a b)] fun _ ↦ (0 : ℝ) := by
    rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
    filter_upwards [hzu] with t ht
    rw [ht]
    exact Metric.infDist_zero_of_mem (mem_range_self (u t))
  have hd := Measure.eqOn_Icc_of_ae_eq volume hab.ne hdist
    ((Metric.continuous_infDist_pt (range J)).comp_continuousOn hz) continuousOn_const
  have hm (t : ℝ) (ht : t ∈ Icc a b) : z t ∈ range J :=
    (hJ.isClosed_range.mem_iff_infDist_zero ⟨J (u a), mem_range_self _⟩).mpr (hd ht)
  let v (t : ℝ) : X := if h : z t ∈ range J then Classical.choose h else u a
  have hv (t : ℝ) (ht : t ∈ Icc a b) : J (v t) = z t := by
    dsimp only [v]
    rw [dite_eq_left (hm t ht)]
    exact Classical.choose_spec (hm t ht)
  refine ⟨v, ?_, ?_, hv⟩
  · intro t ht
    apply hJ.tendsto_nhds_iff.mpr
    rw [hv t ht]
    exact (hz t ht).congr' (Filter.eventuallyEq_of_mem self_mem_nhdsWithin
      fun s hs ↦ (hv s hs).symm)
  · filter_upwards [hzu, ae_restrict_mem measurableSet_Ioc] with t ht hti
    exact hJ.injective ((hv t (Ioc_subset_Icc_self hti)).trans ht)

end Topology.IsClosedEmbedding
