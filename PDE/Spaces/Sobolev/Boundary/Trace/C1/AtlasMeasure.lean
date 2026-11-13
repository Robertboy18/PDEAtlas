/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Area
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Geometry

/-!
# Global surface measure from a `C¹` boundary atlas

The Jacobian-weighted measure associated with each boundary chart agrees with the other chart
measures on overlaps (`chartBoundaryMeasure_restrict_source`). That compatibility lets us
assemble a single finite measure `atlasBoundaryMeasure` on the whole boundary `∂Ω`.

The finite chart cover of `∂Ω` is disjointized in its fixed atlas order: the cell of chart `i` is
the part of its boundary patch not covered by an earlier chart. Restricting each chart measure to
its cell and summing prevents double counting, while overlap compatibility shows that the sum
restricts to the original chart measure on every chart source. This local characterization also
determines the measure uniquely among frontier-supported measures, so the result does not depend
on the disjointization.

The final theorem reduces equality with intrinsic codimension-one Hausdorff measure
`surfaceMeasure Ω` to equality on every chart source. The chartwise area formula in
`PDE.Spaces.Sobolev.Boundary.Trace.C1.Area.Hausdorff` proves this local equality, identifying
the assembled measure with Hausdorff measure. `Trace.C1.MeasureClass` also gives a separate
proof that the two measures are mutually absolutely continuous.

## Main results

* `chartBoundaryCell`, `pairwise_disjoint_chartBoundaryCell`, `iUnion_chartBoundaryCell`: the
  disjointized cells and the fact that they partition `∂Ω`.
* `atlasBoundaryMeasure`, `isFiniteMeasure_atlasBoundaryMeasure`: the assembled finite measure.
* `atlasBoundaryMeasure_restrict_chartSource`: on each chart source the assembled measure is the
  chart measure.
* `eq_atlasBoundaryMeasure_of_restrict_chartSource`: uniqueness.
* `atlasBoundaryMeasure_eq_surfaceMeasure_iff`: reduction of the global area formula to the
  chartwise one.
* `integral_atlasBoundaryMeasure_eq_sum_cells`,
  `integral_atlasBoundaryMeasure_restrict_chartSource`: integration formulas.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace
namespace Trace.C1

open MeasureTheory Set
open scoped ENNReal

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

open Boundary.Geometry.SurfaceMeasure

/-- The parameter measure of a boundary chart is concentrated on its
parameter domain. -/
theorem ae_mem_chartBoundaryParameterMeasure (i : Fin hΩ.N) :
    ∀ᵐ y
      ∂chartBoundaryParameterMeasure (m := m) (Ω := Ω) i,
      y ∈ chartBoundaryParameterDomain (m := m) (Ω := Ω) i := by
  rw [chartBoundaryParameterMeasure]
  exact
    (withDensity_absolutelyContinuous _ _).ae_le <|
      ae_restrict_mem <|
        (isOpen_chartBoundaryParameterDomain
          (m := m) (Ω := Ω) i).measurableSet

/-- Every Jacobian-weighted chart parameter measure has finite total mass. -/
theorem chartBoundaryParameterMeasure_univ_lt_top (i : Fin hΩ.N) :
    (chartBoundaryParameterMeasure (m := m) (Ω := Ω) i) Set.univ < ∞ := by
  have hdomainBounded :
      Bornology.IsBounded
        (chartBoundaryParameterDomain (m := m) (Ω := Ω) i) :=
    (isometry_flatEmbedding (n := m)).antilipschitzWith.isBounded_preimage
      (hΩ.chart_target_bounded i)
  obtain ⟨C, hC⟩ :=
    hdomainBounded.isCompact_closure.exists_bound_of_continuousOn
      (continuous_chartBoundaryJacobian
        (m := m) (Ω := Ω) i).continuousOn
  let Cnn : NNReal := ⟨max C 0, le_max_right C 0⟩
  rw [chartBoundaryParameterMeasure,
    withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  exact
    setLIntegral_lt_top_of_le_nnreal
      (hdomainBounded.measure_lt_top
        (μ := (volume : Measure (ℝ^m)))).ne
      ⟨Cnn, fun y hy ↦ by
        rw [ENNReal.ofReal_le_coe]
        change
          chartBoundaryJacobian (m := m) (Ω := Ω) i y ≤ max C 0
        calc
          chartBoundaryJacobian (m := m) (Ω := Ω) i y ≤
              ‖chartBoundaryJacobian (m := m) (Ω := Ω) i y‖ :=
            Real.le_norm_self _
          _ ≤ C := hC y (subset_closure hy)
          _ ≤ max C 0 := le_max_left C 0⟩

/-- A physical chart measure is concentrated on the boundary portion covered
by that chart. -/
theorem ae_mem_chartBoundaryMeasure (i : Fin hΩ.N) :
    ∀ᵐ x ∂chartBoundaryMeasure (m := m) (Ω := Ω) i,
      x ∈ (hΩ.chart i).source ∩ frontier Ω := by
  rw [chartBoundaryMeasure]
  refine
    (MeasureTheory.ae_map_iff
      (contDiff_chartBoundaryParametrization
        (m := m) (Ω := Ω) i).continuous.measurable.aemeasurable
      ((hΩ.chart i).open_source.measurableSet.inter
        isClosed_frontier.measurableSet)).2 ?_
  filter_upwards [
    ae_mem_chartBoundaryParameterMeasure
      (m := m) (Ω := Ω) i
  ] with y hy
  rw [← image_chartBoundaryParametrization
    (m := m) (Ω := Ω) i]
  exact ⟨y, hy, rfl⟩

/-- Restricting a chart measure to its own chart source changes nothing. -/
theorem chartBoundaryMeasure_restrict_source_self (i : Fin hΩ.N) :
    (chartBoundaryMeasure (m := m) (Ω := Ω) i).restrict
        (hΩ.chart i).source =
      chartBoundaryMeasure (m := m) (Ω := Ω) i := by
  apply Measure.restrict_eq_self_of_ae_mem
  exact
    (ae_mem_chartBoundaryMeasure
      (m := m) (Ω := Ω) i).mono fun _ hx ↦ hx.1

/-- Restricting a chart measure to the frontier changes nothing. -/
theorem chartBoundaryMeasure_restrict_frontier (i : Fin hΩ.N) :
    (chartBoundaryMeasure (m := m) (Ω := Ω) i).restrict
        (frontier Ω) =
      chartBoundaryMeasure (m := m) (Ω := Ω) i := by
  apply Measure.restrict_eq_self_of_ae_mem
  exact
    (ae_mem_chartBoundaryMeasure
      (m := m) (Ω := Ω) i).mono fun _ hx ↦ hx.2

/-- Every physical chart measure has finite total mass. -/
theorem chartBoundaryMeasure_univ_lt_top (i : Fin hΩ.N) :
    (chartBoundaryMeasure (m := m) (Ω := Ω) i) Set.univ < ∞ := by
  rw [chartBoundaryMeasure,
    Measure.map_apply
      (contDiff_chartBoundaryParametrization
        (m := m) (Ω := Ω) i).continuous.measurable
      MeasurableSet.univ,
    preimage_univ]
  exact chartBoundaryParameterMeasure_univ_lt_top
    (m := m) (Ω := Ω) i

/-- The part of chart `i`'s physical boundary patch not assigned to an
earlier chart in the fixed finite atlas order. -/
def chartBoundaryCell (i : Fin hΩ.N) : Set (ℝ^(m + 1)) :=
  disjointed
    (fun j : Fin hΩ.N ↦ (hΩ.chart j).source ∩ frontier Ω) i

/-- Every disjointized boundary cell is measurable. -/
theorem measurableSet_chartBoundaryCell (i : Fin hΩ.N) :
    MeasurableSet (chartBoundaryCell (m := m) (Ω := Ω) i) := by
  apply disjointedRec
    (f := fun j : Fin hΩ.N ↦ (hΩ.chart j).source ∩ frontier Ω)
  · intro t j ht
    exact ht.diff <|
      (hΩ.chart j).open_source.measurableSet.inter
        isClosed_frontier.measurableSet
  · exact
      (hΩ.chart i).open_source.measurableSet.inter
        isClosed_frontier.measurableSet

/-- A disjointized cell remains inside its original physical chart patch. -/
theorem chartBoundaryCell_subset_patch (i : Fin hΩ.N) :
    chartBoundaryCell (m := m) (Ω := Ω) i ⊆
      (hΩ.chart i).source ∩ frontier Ω :=
  disjointed_subset _ i

/-- Distinct disjointized boundary cells are disjoint. -/
theorem pairwise_disjoint_chartBoundaryCell :
    Pairwise
      (fun i j ↦
        Disjoint
          (chartBoundaryCell (m := m) (Ω := Ω) i)
          (chartBoundaryCell (m := m) (Ω := Ω) j)) :=
  disjoint_disjointed _

/-- The disjointized boundary cells cover the entire frontier. -/
theorem iUnion_chartBoundaryCell :
    ⋃ i : Fin hΩ.N, chartBoundaryCell (m := m) (Ω := Ω) i =
      frontier Ω := by
  calc
    ⋃ i : Fin hΩ.N, chartBoundaryCell (m := m) (Ω := Ω) i =
        ⋃ i : Fin hΩ.N, (hΩ.chart i).source ∩ frontier Ω := by
      simpa only [chartBoundaryCell] using
        (iUnion_disjointed
          (f := fun i : Fin hΩ.N ↦
            (hΩ.chart i).source ∩ frontier Ω))
    _ = frontier Ω := by
      apply Set.Subset.antisymm
      · intro x hx
        obtain ⟨i, hxSource, hxFrontier⟩ :=
          Set.mem_iUnion.1 hx
        exact hxFrontier
      · intro x hx
        obtain ⟨i, hxSource⟩ :=
          exists_chart_source_of_mem_frontier
            (n := m + 1) (Ω := Ω) hx
        exact Set.mem_iUnion.2 ⟨i, hxSource, hx⟩

/-- Global boundary measure assembled from the compatible chart measures.
Each physical boundary point is counted in the first chart cell containing
it. -/
noncomputable def atlasBoundaryMeasure : Measure (ℝ^(m + 1)) :=
  Measure.sum fun i : Fin hΩ.N ↦
    (chartBoundaryMeasure (m := m) (Ω := Ω) i).restrict
      (chartBoundaryCell (m := m) (Ω := Ω) i)

/-- The assembled atlas boundary measure has finite total mass. -/
theorem atlasBoundaryMeasure_univ_lt_top :
    (atlasBoundaryMeasure (m := m) (Ω := Ω)) Set.univ < ∞ := by
  rw [atlasBoundaryMeasure, Measure.sum_apply_of_countable, tsum_fintype]
  exact ENNReal.sum_lt_top.mpr fun i _ ↦ by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact
      (measure_mono (subset_univ
        (chartBoundaryCell (m := m) (Ω := Ω) i))).trans_lt <|
          chartBoundaryMeasure_univ_lt_top
            (m := m) (Ω := Ω) i

/-- The global boundary measure assembled from a finite operational atlas is
a finite measure. -/
instance isFiniteMeasure_atlasBoundaryMeasure :
    IsFiniteMeasure (atlasBoundaryMeasure (m := m) (Ω := Ω)) :=
  ⟨atlasBoundaryMeasure_univ_lt_top (m := m) (Ω := Ω)⟩

/-- A nonnegative integral against the atlas measure is the finite sum of
the integrals over its disjoint chart cells. -/
theorem lintegral_atlasBoundaryMeasure_eq_sum_cells
    (f : ℝ^(m + 1) → ℝ≥0∞) :
    ∫⁻ x, f x ∂atlasBoundaryMeasure (m := m) (Ω := Ω) =
      ∑ i : Fin hΩ.N,
        ∫⁻ x in chartBoundaryCell (m := m) (Ω := Ω) i,
          f x ∂chartBoundaryMeasure (m := m) (Ω := Ω) i := by
  rw [atlasBoundaryMeasure, lintegral_sum_measure, tsum_fintype]

/-- An integrable function's integral against the atlas measure is the
finite sum of its integrals over the disjoint chart cells. -/
theorem integral_atlasBoundaryMeasure_eq_sum_cells
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ^(m + 1) → E)
    (hf : Integrable f (atlasBoundaryMeasure (m := m) (Ω := Ω))) :
    ∫ x, f x ∂atlasBoundaryMeasure (m := m) (Ω := Ω) =
      ∑ i : Fin hΩ.N,
        ∫ x in chartBoundaryCell (m := m) (Ω := Ω) i,
          f x ∂chartBoundaryMeasure (m := m) (Ω := Ω) i := by
  unfold atlasBoundaryMeasure at hf ⊢
  rw [integral_sum_measure hf, tsum_fintype]

/-- Restricting one cell contribution to another chart source replaces its
chart measure by the compatible measure from that chart. -/
theorem chartBoundaryMeasure_restrict_cell_restrict_source
    (i j : Fin hΩ.N) :
    ((chartBoundaryMeasure (m := m) (Ω := Ω) i).restrict
        (chartBoundaryCell (m := m) (Ω := Ω) i)).restrict
        (hΩ.chart j).source =
      (chartBoundaryMeasure (m := m) (Ω := Ω) j).restrict
        (chartBoundaryCell (m := m) (Ω := Ω) i) := by
  calc
    ((chartBoundaryMeasure (m := m) (Ω := Ω) i).restrict
        (chartBoundaryCell (m := m) (Ω := Ω) i)).restrict
        (hΩ.chart j).source =
        ((chartBoundaryMeasure (m := m) (Ω := Ω) i).restrict
          (hΩ.chart j).source).restrict
            (chartBoundaryCell (m := m) (Ω := Ω) i) :=
      Measure.restrict_comm (hΩ.chart j).open_source.measurableSet
    _ =
        ((chartBoundaryMeasure (m := m) (Ω := Ω) j).restrict
          (hΩ.chart i).source).restrict
            (chartBoundaryCell (m := m) (Ω := Ω) i) := by
      rw [chartBoundaryMeasure_restrict_source
        (m := m) (Ω := Ω) i j]
    _ =
        (chartBoundaryMeasure (m := m) (Ω := Ω) j).restrict
          (chartBoundaryCell (m := m) (Ω := Ω) i) := by
      exact Measure.restrict_restrict_of_subset <|
        (chartBoundaryCell_subset_patch
          (m := m) (Ω := Ω) i).trans inter_subset_left

/-- The assembled measure restricts on each chart source to that chart's
Jacobian-weighted physical measure. -/
theorem atlasBoundaryMeasure_restrict_chartSource (j : Fin hΩ.N) :
    (atlasBoundaryMeasure (m := m) (Ω := Ω)).restrict
        (hΩ.chart j).source =
      chartBoundaryMeasure (m := m) (Ω := Ω) j := by
  calc
    (atlasBoundaryMeasure (m := m) (Ω := Ω)).restrict
        (hΩ.chart j).source =
        Measure.sum fun i : Fin hΩ.N ↦
          ((chartBoundaryMeasure (m := m) (Ω := Ω) i).restrict
            (chartBoundaryCell (m := m) (Ω := Ω) i)).restrict
              (hΩ.chart j).source := by
      rw [atlasBoundaryMeasure, Measure.restrict_sum_of_countable]
    _ =
        Measure.sum fun i : Fin hΩ.N ↦
          (chartBoundaryMeasure (m := m) (Ω := Ω) j).restrict
            (chartBoundaryCell (m := m) (Ω := Ω) i) := by
      congr 1
      funext i
      exact chartBoundaryMeasure_restrict_cell_restrict_source
        (m := m) (Ω := Ω) i j
    _ =
        (chartBoundaryMeasure (m := m) (Ω := Ω) j).restrict
          (⋃ i : Fin hΩ.N,
            chartBoundaryCell (m := m) (Ω := Ω) i) := by
      exact
        (Measure.restrict_iUnion
          (pairwise_disjoint_chartBoundaryCell
            (m := m) (Ω := Ω))
          (measurableSet_chartBoundaryCell
            (m := m) (Ω := Ω))).symm
    _ =
        (chartBoundaryMeasure (m := m) (Ω := Ω) j).restrict
          (frontier Ω) := by
      rw [iUnion_chartBoundaryCell (m := m) (Ω := Ω)]
    _ = chartBoundaryMeasure (m := m) (Ω := Ω) j :=
      chartBoundaryMeasure_restrict_frontier
        (m := m) (Ω := Ω) j

/-- The assembled atlas measure is concentrated on the frontier. -/
theorem atlasBoundaryMeasure_restrict_frontier :
    (atlasBoundaryMeasure (m := m) (Ω := Ω)).restrict
        (frontier Ω) =
      atlasBoundaryMeasure (m := m) (Ω := Ω) := by
  rw [atlasBoundaryMeasure, Measure.restrict_sum_of_countable]
  congr 1
  funext i
  rw [Measure.restrict_restrict isClosed_frontier.measurableSet]
  rw [inter_eq_right.mpr <|
    (chartBoundaryCell_subset_patch
      (m := m) (Ω := Ω) i).trans inter_subset_right]

/-- A frontier-supported measure with the prescribed chart restrictions is
the assembled atlas boundary measure. -/
theorem eq_atlasBoundaryMeasure_of_restrict_chartSource
    (μ : Measure (ℝ^(m + 1)))
    (hμFrontier : μ.restrict (frontier Ω) = μ)
    (hμChart :
      ∀ i : Fin hΩ.N,
        μ.restrict (hΩ.chart i).source =
          chartBoundaryMeasure (m := m) (Ω := Ω) i) :
    μ = atlasBoundaryMeasure (m := m) (Ω := Ω) := by
  have hcells :
      μ.restrict
          (⋃ i : Fin hΩ.N,
            chartBoundaryCell (m := m) (Ω := Ω) i) =
        (atlasBoundaryMeasure (m := m) (Ω := Ω)).restrict
          (⋃ i : Fin hΩ.N,
            chartBoundaryCell (m := m) (Ω := Ω) i) := by
    apply (Measure.restrict_iUnion_congr).2
    intro i
    calc
      μ.restrict (chartBoundaryCell (m := m) (Ω := Ω) i) =
          (μ.restrict (hΩ.chart i).source).restrict
            (chartBoundaryCell (m := m) (Ω := Ω) i) := by
        exact
          (Measure.restrict_restrict_of_subset <|
            (chartBoundaryCell_subset_patch
              (m := m) (Ω := Ω) i).trans inter_subset_left).symm
      _ =
          (chartBoundaryMeasure (m := m) (Ω := Ω) i).restrict
            (chartBoundaryCell (m := m) (Ω := Ω) i) := by
        rw [hμChart i]
      _ =
          ((atlasBoundaryMeasure (m := m) (Ω := Ω)).restrict
            (hΩ.chart i).source).restrict
              (chartBoundaryCell (m := m) (Ω := Ω) i) := by
        rw [atlasBoundaryMeasure_restrict_chartSource
          (m := m) (Ω := Ω) i]
      _ =
          (atlasBoundaryMeasure (m := m) (Ω := Ω)).restrict
            (chartBoundaryCell (m := m) (Ω := Ω) i) := by
        exact Measure.restrict_restrict_of_subset <|
          (chartBoundaryCell_subset_patch
            (m := m) (Ω := Ω) i).trans inter_subset_left
  calc
    μ = μ.restrict (frontier Ω) := hμFrontier.symm
    _ =
        (atlasBoundaryMeasure (m := m) (Ω := Ω)).restrict
          (frontier Ω) := by
      simpa only [iUnion_chartBoundaryCell
        (m := m) (Ω := Ω)] using hcells
    _ = atlasBoundaryMeasure (m := m) (Ω := Ω) :=
      atlasBoundaryMeasure_restrict_frontier
        (m := m) (Ω := Ω)

/-- The global atlas measure equals intrinsic codimension-one Hausdorff
surface measure exactly when that equality holds locally in every chart. -/
theorem atlasBoundaryMeasure_eq_surfaceMeasure_iff :
    atlasBoundaryMeasure (m := m) (Ω := Ω) =
        surfaceMeasure Ω ↔
      ∀ i : Fin hΩ.N,
        (surfaceMeasure Ω).restrict (hΩ.chart i).source =
          chartBoundaryMeasure (m := m) (Ω := Ω) i := by
  constructor
  · intro h i
    rw [← h]
    exact atlasBoundaryMeasure_restrict_chartSource
      (m := m) (Ω := Ω) i
  · intro h
    have hsurfaceFrontier :
        (surfaceMeasure Ω).restrict (frontier Ω) =
          surfaceMeasure Ω := by
      rw [surfaceMeasure,
        Measure.restrict_restrict isClosed_frontier.measurableSet,
        inter_self]
    exact
      (eq_atlasBoundaryMeasure_of_restrict_chartSource
        (m := m) (Ω := Ω) (surfaceMeasure Ω)
        hsurfaceFrontier h).symm

/-- On a chart source, integration against the global atlas measure is the
usual Jacobian-weighted integral in tangential coordinates. -/
theorem integral_atlasBoundaryMeasure_restrict_chartSource
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin hΩ.N) (f : ℝ^(m + 1) → E)
    (hf :
      AEStronglyMeasurable f
        ((atlasBoundaryMeasure (m := m) (Ω := Ω)).restrict
          (hΩ.chart i).source)) :
    ∫ x, f x
        ∂((atlasBoundaryMeasure (m := m) (Ω := Ω)).restrict
          (hΩ.chart i).source) =
      ∫ y in chartBoundaryParameterDomain (m := m) (Ω := Ω) i,
        chartBoundaryJacobian (m := m) (Ω := Ω) i y •
          f (chartBoundaryParametrization (m := m) (Ω := Ω) i y) := by
  rw [atlasBoundaryMeasure_restrict_chartSource
    (m := m) (Ω := Ω)] at hf ⊢
  exact integral_chartBoundaryMeasure
    (m := m) (Ω := Ω) i f hf

end Trace.C1
end SobolevSpace
