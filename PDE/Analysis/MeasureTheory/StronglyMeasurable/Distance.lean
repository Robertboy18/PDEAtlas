/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Order.ProjIcc

/-!
# Strong measurability from distances

In a separable metric target, distances to a countable dense sequence determine both
points and the topology. Mathlib realizes this as an embedding into the Hilbert cube.
Pulling strong measurability back through that embedding lets scalar distance estimates
establish strong measurability of a map into a function space.
-/

@[expose] public section

noncomputable section

open TopologicalSpace unitInterval

namespace MeasureTheory

/-- A map into a nonempty separable metric space is a.e. strongly measurable if
its distance to each fixed point is a.e. measurable. The proof uses Mathlib's
countable distance embedding, so no measurability of the original map is assumed. -/
theorem aestronglyMeasurable_of_aemeasurable_dist
    {α X : Type*} [MeasurableSpace α] [MetricSpace X] [SeparableSpace X] [Nonempty X]
    {μ : Measure α} {f : α → X}
    (hdist : ∀ x : X, AEMeasurable (fun t ↦ dist (f t) x) μ) :
    AEStronglyMeasurable f μ := by
  have hcube : AEStronglyMeasurable
      (fun t n ↦ Metric.PiNatEmbed.distDenseSeq X n (f t)) μ := by
    apply AEMeasurable.aestronglyMeasurable
    apply AEMeasurable.of_eval
    intro n
    exact continuous_projIcc.measurable.comp_aemeasurable (hdist (denseSeq X n))
  have hembed := (Metric.PiNatEmbed.isUniformEmbedding_embed
    (Metric.PiNatEmbed.injective_distDenseSeq (X := X))).isEmbedding
  have hlift : AEStronglyMeasurable
      (fun t ↦ Metric.PiNatEmbed.toPiNat (f t) :
        α → Metric.PiNatEmbed X (fun _ : ℕ ↦ I) (Metric.PiNatEmbed.distDenseSeq X)) μ :=
    hembed.aestronglyMeasurable_comp_iff.mp hcube
  exact Metric.PiNatEmbed.continuous_distDenseSeq_inv.comp_aestronglyMeasurable hlift

end MeasureTheory
