/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.AtlasMeasure
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Physicalization
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import PDE.Analysis.MeasureTheory.ParametrizedArea
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Geometry

/-!
# Measure class of the `C¹` atlas boundary measure

The operational atlas measure `atlasBoundaryMeasure` is assembled from Jacobian-weighted boundary
parametrizations, whereas the trace theorem uses intrinsic Euclidean Hausdorff surface measure
`surfaceMeasure Ω`. We prove that the two measures have the same null sets, and hence the same
almost-everywhere notions, and express each as a density times the other via the
Lebesgue–Radon–Nikodym theorem, in the form of Mathlib's `Measure.rnDeriv` and
`Measure.withDensity_rnDeriv_eq`.

The comparison goes through an unweighted reference measure on each chart: the pushforward of
Lebesgue measure on the tangential parameter domain under the boundary parametrization. The
Jacobian-weighted chart measure is equivalent to it because the Jacobian is positive and finite,
and the intrinsic surface measure restricted to the chart patch is equivalent to it because the
chart and its inverse are Lipschitz on the relevant bounded sets, so both transport
`(n-1)`-dimensional Hausdorff null sets to null sets.

Mutual absolute continuity is weaker than equality. The equality
`atlasBoundaryMeasure_eq_surfaceMeasure` is proved from the `C¹` area formula in
`Trace.C1.Area.Hausdorff`; the argument here does not use it.

## Main results

* `atlasBoundaryMeasure_absolutelyContinuous_surfaceMeasure`,
  `surfaceMeasure_absolutelyContinuous_atlasBoundaryMeasure`: mutual absolute continuity.
* `atlasBoundaryMeasure_apply_eq_zero_iff_surfaceMeasure`,
  `ae_eq_atlasBoundaryMeasure_iff_surfaceMeasure`: same null sets, same a.e. equality.
* `surfaceMeasureDensity`, `atlasBoundaryMeasureDensity`: the two Radon–Nikodym derivatives,
  positive and finite a.e. and reciprocal to each other.
* `atlasBoundaryMeasure_withDensity_surfaceMeasureDensity`,
  `integral_surfaceMeasureDensity_smul`: each measure is a density times the other, and the
  corresponding change of integration measure.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley, 1999,
  for the Lebesgue–Radon–Nikodym theorem.
  <https://www.wiley.com/en-us/Real+Analysis%3A+Modern+Techniques+and+Their+Applications%2C+2nd+Edition-p-9780471317166>
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

/-- The unweighted pushforward of Lebesgue measure on a chart's tangential
parameter domain. It is a convenient reference measure for comparing
Jacobian-weighted and intrinsic surface measures. -/
noncomputable def chartBoundaryReferenceMeasure
    (i : Fin hΩ.N) : Measure (ℝ^(m + 1)) :=
  Measure.map
    (chartBoundaryParametrization (m := m) (Ω := Ω) i)
    ((volume : Measure (ℝ^m)).restrict
      (chartBoundaryParameterDomain (m := m) (Ω := Ω) i))

private theorem chartBoundaryParameterDensity_ne_zero_ae
    (i : Fin hΩ.N) :
    ∀ᵐ y
      ∂((volume : Measure (ℝ^m)).restrict
        (chartBoundaryParameterDomain (m := m) (Ω := Ω) i)),
      ENNReal.ofReal
        (chartBoundaryJacobian (m := m) (Ω := Ω) i y) ≠ 0 := by
  filter_upwards [
    ae_restrict_mem
      (isOpen_chartBoundaryParameterDomain
        (m := m) (Ω := Ω) i).measurableSet
  ] with y hy
  exact ENNReal.ofReal_ne_zero_iff.mpr <|
    chartBoundaryJacobian_pos (m := m) (Ω := Ω) i hy

/-- A Jacobian-weighted chart measure is absolutely continuous with respect
to its unweighted parametrized reference measure. -/
theorem chartBoundaryMeasure_absolutelyContinuous_referenceMeasure
    (i : Fin hΩ.N) :
    chartBoundaryMeasure (m := m) (Ω := Ω) i ≪
      chartBoundaryReferenceMeasure (m := m) (Ω := Ω) i := by
  unfold chartBoundaryMeasure chartBoundaryReferenceMeasure
  exact
    (withDensity_absolutelyContinuous _ _).map <|
      (contDiff_chartBoundaryParametrization
        (m := m) (Ω := Ω) i).continuous.measurable

/-- The unweighted parametrized reference measure is absolutely continuous
with respect to the Jacobian-weighted chart measure. -/
theorem chartBoundaryReferenceMeasure_absolutelyContinuous_boundaryMeasure
    (i : Fin hΩ.N) :
    chartBoundaryReferenceMeasure (m := m) (Ω := Ω) i ≪
      chartBoundaryMeasure (m := m) (Ω := Ω) i := by
  unfold chartBoundaryMeasure chartBoundaryReferenceMeasure
  apply Measure.AbsolutelyContinuous.map
  · exact withDensity_absolutelyContinuous'
      ((continuous_chartBoundaryJacobian
        (m := m) (Ω := Ω) i).measurable.ennreal_ofReal.aemeasurable)
      (chartBoundaryParameterDensity_ne_zero_ae
        (m := m) (Ω := Ω) i)
  · exact
      (contDiff_chartBoundaryParametrization
        (m := m) (Ω := Ω) i).continuous.measurable

private theorem image_flatEmbedding_inter_preimage
    (i : Fin hΩ.N) (s : Set (ℝ^(m + 1))) :
    flatEmbedding ''
        (chartBoundaryParametrization (m := m) (Ω := Ω) i ⁻¹' s ∩
          chartBoundaryParameterDomain (m := m) (Ω := Ω) i) =
      hΩ.chart i ''
        (s ∩ chartBoundaryPatch (m := m) (Ω := Ω) i) := by
  ext z
  constructor
  · rintro ⟨y, ⟨hyS, hyDomain⟩, rfl⟩
    let x := chartBoundaryParametrization (m := m) (Ω := Ω) i y
    have hxPatch : x ∈ chartBoundaryPatch (m := m) (Ω := Ω) i := by
      change x ∈ (hΩ.chart i).source ∩ frontier Ω
      rw [← image_chartBoundaryParametrization
        (m := m) (Ω := Ω) i]
      exact ⟨y, hyDomain, rfl⟩
    refine ⟨x, ⟨hyS, hxPatch⟩, ?_⟩
    exact (hΩ.chart i).right_inv hyDomain
  · rintro ⟨x, ⟨hxS, hxSource, hxFrontier⟩, rfl⟩
    let y : ℝ^m := flatProjection (hΩ.chart i x)
    have hxFlat : hΩ.chart i x ∈ HalfSpace.boundary (m + 1) :=
      (chart_mem_boundary_iff
        (n := m + 1) (Ω := Ω) i hxSource).2 hxFrontier
    have hlast : PDE.Common.lastIndex (n := m + 1) = Fin.last m := by
      apply Fin.ext
      simp [PDE.Common.lastIndex]
    have hflat : flatEmbedding y = hΩ.chart i x := by
      apply flatEmbedding_flatProjection_of_last_eq_zero
      simpa [HalfSpace.boundary, hlast] using hxFlat
    refine ⟨y, ⟨?_, ?_⟩, hflat⟩
    · change (hΩ.chart i).symm (flatEmbedding y) ∈ s
      rw [hflat, (hΩ.chart i).left_inv hxSource]
      exact hxS
    · change flatEmbedding y ∈ (hΩ.chart i).target
      rw [hflat]
      exact (hΩ.chart i).map_source hxSource

private theorem symm_image_chart_image_inter_patch
    (i : Fin hΩ.N) (s : Set (ℝ^(m + 1))) :
    (hΩ.chart i).symm ''
        (hΩ.chart i ''
          (s ∩ chartBoundaryPatch (m := m) (Ω := Ω) i)) =
      s ∩ chartBoundaryPatch (m := m) (Ω := Ω) i := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [(hΩ.chart i).left_inv hy.2.1]
    exact hy
  · intro hx
    refine ⟨hΩ.chart i x, ⟨x, hx, rfl⟩, ?_⟩
    exact (hΩ.chart i).left_inv hx.2.1

/-- The unweighted parametrized chart measure is absolutely continuous with
respect to intrinsic surface measure. -/
theorem chartBoundaryReferenceMeasure_absolutelyContinuous_surfaceMeasure
    (i : Fin hΩ.N) :
    chartBoundaryReferenceMeasure (m := m) (Ω := Ω) i ≪
      Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hsSurface ↦ ?_
  rw [chartBoundaryReferenceMeasure,
    Measure.map_apply
      (contDiff_chartBoundaryParametrization
        (m := m) (Ω := Ω) i).continuous.measurable hs,
    Measure.restrict_apply
      ((contDiff_chartBoundaryParametrization
        (m := m) (Ω := Ω) i).continuous.measurable hs)]
  rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume m]
  rw [← (isometry_flatEmbedding (n := m)).euclideanHausdorffMeasure_image]
  rw [image_flatEmbedding_inter_preimage
    (m := m) (Ω := Ω) i s]
  obtain ⟨C, hLip⟩ :=
    exists_chart_lipschitzOnWith_boundary_piece
      (n := m + 1) (Ω := Ω) i
  have hSurfaceInter :
      Measure.euclideanHausdorffMeasure m
          (s ∩ chartBoundaryPatch (m := m) (Ω := Ω) i) = 0 := by
    have hsFrontier :
        Measure.euclideanHausdorffMeasure m (s ∩ frontier Ω) = 0 := by
      simpa [Boundary.Geometry.SurfaceMeasure.surfaceMeasure,
        Measure.restrict_apply hs] using hsSurface
    exact measure_mono_null (by
      intro x hx
      exact ⟨hx.1, hx.2.2⟩) hsFrontier
  have hSurfaceInter' :
      Measure.euclideanHausdorffMeasure m
          (s ∩ ((hΩ.chart i).source ∩ frontier Ω)) = 0 := by
    simpa [chartBoundaryPatch] using hSurfaceInter
  exact nonpos_iff_eq_zero.mp <|
    ((hLip.mono inter_subset_right).euclideanHausdorffMeasure_image_le m).trans_eq
      (by simp [hSurfaceInter'])

/-- Intrinsic surface measure restricted to a chart patch is absolutely
continuous with respect to the unweighted parametrized chart measure. -/
theorem surfaceMeasure_restrict_chartBoundaryPatch_absolutelyContinuous_referenceMeasure
    (i : Fin hΩ.N) :
    (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω).restrict
        (chartBoundaryPatch (m := m) (Ω := Ω) i) ≪
      chartBoundaryReferenceMeasure (m := m) (Ω := Ω) i := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hsReference ↦ ?_
  have hParameter :
      (volume : Measure (ℝ^m))
        (chartBoundaryParametrization (m := m) (Ω := Ω) i ⁻¹' s ∩
          chartBoundaryParameterDomain (m := m) (Ω := Ω) i) = 0 := by
    simpa [chartBoundaryReferenceMeasure,
      Measure.map_apply
        (contDiff_chartBoundaryParametrization
          (m := m) (Ω := Ω) i).continuous.measurable hs,
      Measure.restrict_apply
        ((contDiff_chartBoundaryParametrization
          (m := m) (Ω := Ω) i).continuous.measurable hs)] using hsReference
  have hFlat :
      Measure.euclideanHausdorffMeasure m
        (flatEmbedding ''
          (chartBoundaryParametrization (m := m) (Ω := Ω) i ⁻¹' s ∩
            chartBoundaryParameterDomain (m := m) (Ω := Ω) i)) = 0 := by
    rw [(isometry_flatEmbedding (n := m)).euclideanHausdorffMeasure_image]
    simpa [EuclideanSpace.euclideanHausdorffMeasure_eq_volume] using hParameter
  obtain ⟨C, hLip⟩ :=
    exists_chart_symm_lipschitzOnWith
      (n := m + 1) (Ω := Ω) i
  have hChartImage :
      Measure.euclideanHausdorffMeasure m
          ((hΩ.chart i).symm ''
            (hΩ.chart i ''
              (s ∩ chartBoundaryPatch (m := m) (Ω := Ω) i))) = 0 := by
    have hTarget :
        hΩ.chart i ''
            (s ∩ chartBoundaryPatch (m := m) (Ω := Ω) i) ⊆
          (hΩ.chart i).target := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hΩ.chart i).map_source hx.2.1
    have hImageZero :
        Measure.euclideanHausdorffMeasure m
            (hΩ.chart i ''
              (s ∩ chartBoundaryPatch (m := m) (Ω := Ω) i)) = 0 := by
      rw [← image_flatEmbedding_inter_preimage
        (m := m) (Ω := Ω) i s]
      exact hFlat
    exact nonpos_iff_eq_zero.mp <|
      ((hLip.mono hTarget).euclideanHausdorffMeasure_image_le m).trans_eq
        (by simp [hImageZero])
  have hPhysical :
      Measure.euclideanHausdorffMeasure m
          (s ∩ chartBoundaryPatch (m := m) (Ω := Ω) i) = 0 := by
    rw [← symm_image_chart_image_inter_patch
      (m := m) (Ω := Ω) i s]
    exact hChartImage
  have hRestrict :
      (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω).restrict
          (chartBoundaryPatch (m := m) (Ω := Ω) i) =
        (Measure.euclideanHausdorffMeasure m).restrict
          (chartBoundaryPatch (m := m) (Ω := Ω) i) := by
    rw [Boundary.Geometry.SurfaceMeasure.surfaceMeasure,
      Measure.restrict_restrict
        (measurableSet_chartBoundaryPatch
          (m := m) (Ω := Ω) i)]
    congr 1
    ext x
    simp [chartBoundaryPatch, and_left_comm, and_comm]
  rw [hRestrict, Measure.restrict_apply hs]
  exact hPhysical

/-- A Jacobian-weighted chart measure is absolutely continuous with respect
to intrinsic surface measure. -/
theorem chartBoundaryMeasure_absolutelyContinuous_surfaceMeasure
    (i : Fin hΩ.N) :
    chartBoundaryMeasure (m := m) (Ω := Ω) i ≪
      Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω :=
  (chartBoundaryMeasure_absolutelyContinuous_referenceMeasure
    (m := m) (Ω := Ω) i).trans <|
      chartBoundaryReferenceMeasure_absolutelyContinuous_surfaceMeasure
        (m := m) (Ω := Ω) i

/-- Intrinsic surface measure restricted to a chart patch is absolutely
continuous with respect to its Jacobian-weighted chart measure. -/
theorem surfaceMeasure_restrict_chartBoundaryPatch_absolutelyContinuous_boundaryMeasure
    (i : Fin hΩ.N) :
    (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω).restrict
        (chartBoundaryPatch (m := m) (Ω := Ω) i) ≪
      chartBoundaryMeasure (m := m) (Ω := Ω) i :=
  (surfaceMeasure_restrict_chartBoundaryPatch_absolutelyContinuous_referenceMeasure
    (m := m) (Ω := Ω) i).trans <|
      chartBoundaryReferenceMeasure_absolutelyContinuous_boundaryMeasure
        (m := m) (Ω := Ω) i

/-- The assembled atlas boundary measure is absolutely continuous with
respect to intrinsic surface measure. -/
theorem atlasBoundaryMeasure_absolutelyContinuous_surfaceMeasure :
    atlasBoundaryMeasure (m := m) (Ω := Ω) ≪
      Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω := by
  rw [atlasBoundaryMeasure]
  apply Measure.absolutelyContinuous_sum_left
  intro i
  exact Measure.absolutelyContinuous_restrict.trans <|
    chartBoundaryMeasure_absolutelyContinuous_surfaceMeasure
      (m := m) (Ω := Ω) i

/-- Intrinsic surface measure is absolutely continuous with respect to the
assembled atlas boundary measure. -/
theorem surfaceMeasure_absolutelyContinuous_atlasBoundaryMeasure :
    Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω ≪
      atlasBoundaryMeasure (m := m) (Ω := Ω) := by
  have hCell :
      ∀ i : Fin hΩ.N,
        (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω).restrict
            (chartBoundaryCell (m := m) (Ω := Ω) i) ≪
          atlasBoundaryMeasure (m := m) (Ω := Ω) := by
    intro i
    have hLocal :=
      (surfaceMeasure_restrict_chartBoundaryPatch_absolutelyContinuous_boundaryMeasure
        (m := m) (Ω := Ω) i).restrict
          (chartBoundaryCell (m := m) (Ω := Ω) i)
    change
      ((Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω).restrict
        ((hΩ.chart i).source ∩ frontier Ω)).restrict
          (chartBoundaryCell (m := m) (Ω := Ω) i) ≪
        (chartBoundaryMeasure (m := m) (Ω := Ω) i).restrict
          (chartBoundaryCell (m := m) (Ω := Ω) i) at hLocal
    rw [Measure.restrict_restrict_of_subset
      (chartBoundaryCell_subset_patch
        (m := m) (Ω := Ω) i)] at hLocal
    exact hLocal.trans <| by
      unfold atlasBoundaryMeasure
      exact Measure.absolutelyContinuous_sum_right i
        Measure.AbsolutelyContinuous.rfl
  have hSum :
      Measure.sum (fun i : Fin hΩ.N ↦
        (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω).restrict
          (chartBoundaryCell (m := m) (Ω := Ω) i)) ≪
        atlasBoundaryMeasure (m := m) (Ω := Ω) :=
    Measure.absolutelyContinuous_sum_left hCell
  have hDecomp :
      Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω =
        Measure.sum (fun i : Fin hΩ.N ↦
          (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω).restrict
            (chartBoundaryCell (m := m) (Ω := Ω) i)) := by
    calc
      Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω =
          (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω).restrict
            (frontier Ω) := by
        simp [Boundary.Geometry.SurfaceMeasure.surfaceMeasure,
          Measure.restrict_restrict isClosed_frontier.measurableSet]
      _ =
          (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω).restrict
            (⋃ i : Fin hΩ.N,
              chartBoundaryCell (m := m) (Ω := Ω) i) := by
        rw [iUnion_chartBoundaryCell (m := m) (Ω := Ω)]
      _ = Measure.sum (fun i : Fin hΩ.N ↦
          (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω).restrict
            (chartBoundaryCell (m := m) (Ω := Ω) i)) :=
        Measure.restrict_iUnion
          (pairwise_disjoint_chartBoundaryCell
            (m := m) (Ω := Ω))
          (measurableSet_chartBoundaryCell
            (m := m) (Ω := Ω))
  rw [hDecomp]
  exact hSum

/-- The atlas and intrinsic surface measures have the same null sets. -/
theorem atlasBoundaryMeasure_apply_eq_zero_iff_surfaceMeasure
    (s : Set (ℝ^(m + 1))) :
    atlasBoundaryMeasure (m := m) (Ω := Ω) s = 0 ↔
      Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω s = 0 :=
  ⟨fun hs ↦
      surfaceMeasure_absolutelyContinuous_atlasBoundaryMeasure
        (m := m) (Ω := Ω) hs,
    fun hs ↦
      atlasBoundaryMeasure_absolutelyContinuous_surfaceMeasure
        (m := m) (Ω := Ω) hs⟩

/-- Almost-everywhere equality is the same for the atlas and intrinsic
surface measures. -/
theorem ae_eq_atlasBoundaryMeasure_iff_surfaceMeasure
    {α : Type*} {f g : ℝ^(m + 1) → α} :
    f =ᵐ[atlasBoundaryMeasure (m := m) (Ω := Ω)] g ↔
      f =ᵐ[Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω] g :=
  ⟨(surfaceMeasure_absolutelyContinuous_atlasBoundaryMeasure
      (m := m) (Ω := Ω)).ae_eq,
    (atlasBoundaryMeasure_absolutelyContinuous_surfaceMeasure
      (m := m) (Ω := Ω)).ae_eq⟩

/-- Radon-Nikodym density of intrinsic surface measure with respect to the
operational atlas measure. -/
noncomputable def surfaceMeasureDensity : ℝ^(m + 1) → ℝ≥0∞ :=
  (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω).rnDeriv
    (atlasBoundaryMeasure (m := m) (Ω := Ω))

/-- Radon-Nikodym density of the operational atlas measure with respect to
intrinsic surface measure. -/
noncomputable def atlasBoundaryMeasureDensity : ℝ^(m + 1) → ℝ≥0∞ :=
  (atlasBoundaryMeasure (m := m) (Ω := Ω)).rnDeriv
    (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω)

/-- The intrinsic-to-atlas Radon-Nikodym density is measurable. -/
theorem measurable_surfaceMeasureDensity :
    Measurable (surfaceMeasureDensity (m := m) (Ω := Ω)) := by
  exact Measure.measurable_rnDeriv _ _

/-- The atlas-to-intrinsic Radon-Nikodym density is measurable. -/
theorem measurable_atlasBoundaryMeasureDensity :
    Measurable (atlasBoundaryMeasureDensity (m := m) (Ω := Ω)) := by
  exact Measure.measurable_rnDeriv _ _

/-- Weighting the atlas measure by `surfaceMeasureDensity` recovers intrinsic
surface measure exactly. -/
theorem atlasBoundaryMeasure_withDensity_surfaceMeasureDensity :
    (atlasBoundaryMeasure (m := m) (Ω := Ω)).withDensity
        (surfaceMeasureDensity (m := m) (Ω := Ω)) =
      Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω := by
  exact Measure.withDensity_rnDeriv_eq _ _
    (surfaceMeasure_absolutelyContinuous_atlasBoundaryMeasure
      (m := m) (Ω := Ω))

/-- Weighting intrinsic surface measure by `atlasBoundaryMeasureDensity`
recovers the atlas measure exactly. -/
theorem surfaceMeasure_withDensity_atlasBoundaryMeasureDensity :
    (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω).withDensity
        (atlasBoundaryMeasureDensity (m := m) (Ω := Ω)) =
      atlasBoundaryMeasure (m := m) (Ω := Ω) := by
  exact Measure.withDensity_rnDeriv_eq _ _
    (atlasBoundaryMeasure_absolutelyContinuous_surfaceMeasure
      (m := m) (Ω := Ω))

/-- The intrinsic-to-atlas density is strictly positive almost everywhere
for the atlas measure. -/
theorem surfaceMeasureDensity_pos_ae :
    ∀ᵐ x ∂atlasBoundaryMeasure (m := m) (Ω := Ω),
      0 < surfaceMeasureDensity (m := m) (Ω := Ω) x := by
  change
    ∀ᵐ x ∂atlasBoundaryMeasure (m := m) (Ω := Ω),
      0 <
        (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω).rnDeriv
          (atlasBoundaryMeasure (m := m) (Ω := Ω)) x
  exact Filter.Eventually.filter_mono
    (atlasBoundaryMeasure_absolutelyContinuous_surfaceMeasure
      (m := m) (Ω := Ω)).ae_le
    (Measure.rnDeriv_pos
      (surfaceMeasure_absolutelyContinuous_atlasBoundaryMeasure
        (m := m) (Ω := Ω)))

/-- The intrinsic-to-atlas density is finite almost everywhere for the atlas
measure. -/
theorem surfaceMeasureDensity_lt_top_ae :
    ∀ᵐ x ∂atlasBoundaryMeasure (m := m) (Ω := Ω),
      surfaceMeasureDensity (m := m) (Ω := Ω) x < ∞ := by
  simpa [surfaceMeasureDensity] using
    Measure.rnDeriv_lt_top
      (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω)
      (atlasBoundaryMeasure (m := m) (Ω := Ω))

/-- The atlas-to-intrinsic density is strictly positive almost everywhere
for intrinsic surface measure. -/
theorem atlasBoundaryMeasureDensity_pos_ae :
    ∀ᵐ x ∂Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω,
      0 < atlasBoundaryMeasureDensity (m := m) (Ω := Ω) x := by
  change
    ∀ᵐ x ∂Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω,
      0 <
        (atlasBoundaryMeasure (m := m) (Ω := Ω)).rnDeriv
          (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω) x
  exact Filter.Eventually.filter_mono
    (surfaceMeasure_absolutelyContinuous_atlasBoundaryMeasure
      (m := m) (Ω := Ω)).ae_le
    (Measure.rnDeriv_pos
      (atlasBoundaryMeasure_absolutelyContinuous_surfaceMeasure
        (m := m) (Ω := Ω)))

/-- The atlas-to-intrinsic density is finite almost everywhere for intrinsic
surface measure. -/
theorem atlasBoundaryMeasureDensity_lt_top_ae :
    ∀ᵐ x ∂Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω,
      atlasBoundaryMeasureDensity (m := m) (Ω := Ω) x < ∞ := by
  simpa [atlasBoundaryMeasureDensity] using
    Measure.rnDeriv_lt_top
      (atlasBoundaryMeasure (m := m) (Ω := Ω))
      (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω)

/-- The two Radon-Nikodym densities are reciprocal almost everywhere for
the atlas measure. -/
theorem surfaceMeasureDensity_inv_ae :
    (surfaceMeasureDensity (m := m) (Ω := Ω))⁻¹
        =ᵐ[atlasBoundaryMeasure (m := m) (Ω := Ω)]
      atlasBoundaryMeasureDensity (m := m) (Ω := Ω) := by
  change
    ((Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω).rnDeriv
        (atlasBoundaryMeasure (m := m) (Ω := Ω)))⁻¹
      =ᵐ[atlasBoundaryMeasure (m := m) (Ω := Ω)]
    (atlasBoundaryMeasure (m := m) (Ω := Ω)).rnDeriv
      (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω)
  exact Filter.Eventually.filter_mono
    (atlasBoundaryMeasure_absolutelyContinuous_surfaceMeasure
      (m := m) (Ω := Ω)).ae_le
    (Measure.inv_rnDeriv
      (surfaceMeasure_absolutelyContinuous_atlasBoundaryMeasure
        (m := m) (Ω := Ω)))

/-- Nonnegative integration against intrinsic surface measure is exactly
weighted integration against the operational atlas measure. -/
theorem lintegral_surfaceMeasureDensity_mul
    {f : ℝ^(m + 1) → ℝ≥0∞}
    (hf : AEMeasurable f
      (atlasBoundaryMeasure (m := m) (Ω := Ω))) :
    ∫⁻ x,
        surfaceMeasureDensity (m := m) (Ω := Ω) x * f x
        ∂atlasBoundaryMeasure (m := m) (Ω := Ω) =
      ∫⁻ x, f x
        ∂Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω := by
  simpa [surfaceMeasureDensity] using
    lintegral_rnDeriv_mul
      (surfaceMeasure_absolutelyContinuous_atlasBoundaryMeasure
        (m := m) (Ω := Ω)) hf

/-- Bochner integrability against intrinsic surface measure is equivalent to
integrability of the density-weighted function against the atlas measure. -/
theorem integrable_surfaceMeasureDensity_smul_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ^(m + 1) → E} :
    Integrable
        (fun x ↦
          (surfaceMeasureDensity (m := m) (Ω := Ω) x).toReal • f x)
        (atlasBoundaryMeasure (m := m) (Ω := Ω)) ↔
      Integrable f
        (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω) := by
  simpa [surfaceMeasureDensity] using
    integrable_rnDeriv_smul_iff
      (surfaceMeasure_absolutelyContinuous_atlasBoundaryMeasure
        (m := m) (Ω := Ω)) (f := f)

/-- Bochner integration against intrinsic surface measure is exactly
density-weighted integration against the operational atlas measure. -/
theorem integral_surfaceMeasureDensity_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ^(m + 1) → E} :
    ∫ x,
        (surfaceMeasureDensity (m := m) (Ω := Ω) x).toReal • f x
        ∂atlasBoundaryMeasure (m := m) (Ω := Ω) =
      ∫ x, f x
        ∂Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω := by
  simpa [surfaceMeasureDensity] using
    integral_rnDeriv_smul
      (surfaceMeasure_absolutelyContinuous_atlasBoundaryMeasure
        (m := m) (Ω := Ω)) (f := f)

end Trace.C1
end SobolevSpace
