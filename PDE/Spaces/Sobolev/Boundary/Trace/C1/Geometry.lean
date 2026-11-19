/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Cutoffs
public import PDE.Spaces.Sobolev.Boundary.Geometry.SurfaceMeasure
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import PDE.Analysis.MeasureTheory.ParametrizedArea

/-!
# Boundary charts for the `C¹` trace theorem

We begin the globalization of the flat trace theorem (Evans, PDE, §5.5). The operational
`Boundary.C1ExtensionAtlas` charts identify the domain with an upper half-space on each chart
source. Since open partial homeomorphisms transport frontiers, they also identify the topological
boundary `∂Ω` with the flat boundary hyperplane `{xₙ = 0}`, pointwise and as sets.

Two further consequences of the atlas are recorded. First, the partition of unity extends by
continuity from `Ω` to `closure Ω`; since the interior cutoff vanishes on `∂Ω`, the boundary
cutoffs alone sum to `1` there, and in particular the chart sources cover `∂Ω`. Second, the
charts and their inverses are Lipschitz on the relevant bounded sets (by the mean value inequality
on a compact convex neighbourhood), and Lipschitz maps distort codimension-one Hausdorff measure
by at most a power of the constant. Since each chart maps its boundary piece onto a bounded subset
of the hyperplane, whose surface measure is finite, the intrinsic surface measure of `∂Ω` is
finite.

## Main results

* `chart_isImage_domain`, `chart_isImage_boundary`, `chart_mem_boundary_iff`,
  `chart_image_boundary`: charts carry `Ω` to the upper half-space and `∂Ω` to the hyperplane.
* `chart_height_le_mul_infDist_frontier_on_boundarySupport`: on a compact boundary support the
  flattened height `(chart x)ₙ` is bounded by a constant times the distance from `x` to `∂Ω`.
* `partitionSum_eq_one_on_closure`, `sum_boundary_partition_eq_one`,
  `frontier_subset_iUnion_chart_source`: the partition of unity on `closure Ω` and the covering
  of `∂Ω` by chart sources.
* `exists_chart_symm_lipschitzOnWith`, `exists_chart_lipschitzOnWith_boundary_piece`,
  `exists_chart_symm_surfaceMeasure_image_le`: Lipschitz bounds and the resulting surface-measure
  distortion bound.
* `surfaceMeasure_lt_top_of_isC1ExtensionAtlas`, `isFiniteMeasure_surfaceMeasure`: `∂Ω` has
  finite surface measure.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.5, Theorem 1, steps 2 and 3 of the proof, pp. 272-273,
  which straighten the boundary and cover it by finitely many such pieces.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace
namespace Trace.C1

open MeasureTheory Set
open scoped NNReal ENNReal

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- A boundary chart identifies `Ω` with the upper half-space wherever the
chart is defined. -/
theorem chart_isImage_domain (i : Fin hΩ.N) :
    (hΩ.chart i).IsImage Ω (HalfSpace.upper n) := by
  intro x hx
  exact (hΩ.chart_mem_iff_upper i x hx).symm

/-- Consequently, the same chart identifies their topological boundaries. -/
theorem chart_isImage_boundary (i : Fin hΩ.N) :
    (hΩ.chart i).IsImage (frontier Ω) (HalfSpace.boundary n) := by
  simpa [HalfSpace.frontier_upper (n := n)] using
    (chart_isImage_domain (n := n) (Ω := Ω) i).frontier

/-- Pointwise boundary membership in a chart: a point is on `∂Ω` exactly when
its flattened normal coordinate is zero. -/
theorem chart_mem_boundary_iff (i : Fin hΩ.N) {x : ℝ^n}
    (hx : x ∈ (hΩ.chart i).source) :
    hΩ.chart i x ∈ HalfSpace.boundary n ↔ x ∈ frontier Ω :=
  (chart_isImage_boundary (n := n) (Ω := Ω) i).apply_mem_iff hx

/-- The bounded atlas domain is not the whole space. -/
private theorem ne_univ : Ω ≠ Set.univ := by
  have : Nontrivial (ℝ^n) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using (Fact.out : 0 < n))
  exact fun hEq ↦ NormedSpace.unbounded_univ ℝ (ℝ^n) (hEq ▸ hΩ.bounded)

/-- An interior point of the bounded open atlas domain has positive distance
from its topological boundary. -/
theorem infDist_frontier_pos_of_mem {x : ℝ^n} (hx : x ∈ Ω) :
    0 < Metric.infDist x (frontier Ω) := by
  have hΩne : Ω ≠ Set.univ := ne_univ
  obtain ⟨z, hzFrontier, _⟩ :=
    exists_mem_frontier_infDist_compl_eq_dist hx hΩne
  have hxInterior : x ∈ interior Ω := by
    simpa [hΩ.isOpen.interior_eq] using hx
  have hxNotFrontier : x ∉ frontier Ω :=
    (mem_interior_iff_notMem_frontier hx).1 hxInterior
  exact
    (isClosed_frontier.notMem_iff_infDist_pos ⟨z, hzFrontier⟩).1
      hxNotFrontier

/-- On a compact boundary-chart support, flattened height is controlled by
physical distance to the boundary. -/
theorem chart_height_le_mul_infDist_frontier_on_boundarySupport
    (i : Fin hΩ.N) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈
          Boundary.C1ExtensionAtlas.DerivedCutoffs.boundarySupport
            (n := n) (Ω := Ω) i ∩ Ω,
        (hΩ.chart i x) (PDE.Common.lastIndex (n := n)) ≤
          C * Metric.infDist x (frontier Ω) := by
  let K : Set (ℝ^n) :=
    Boundary.C1ExtensionAtlas.DerivedCutoffs.boundarySupport (n := n) (Ω := Ω) i
  have hKcompact : IsCompact K :=
    Boundary.C1ExtensionAtlas.DerivedCutoffs.isCompact_boundarySupport (n := n) (Ω := Ω) i
  have hKsource : K ⊆ (hΩ.chart i).source :=
    Boundary.C1ExtensionAtlas.DerivedCutoffs.boundarySupport_subset_source (n := n) (Ω := Ω) i
  obtain ⟨δ, hδ, hthick⟩ :=
    hKcompact.exists_cthickening_subset_open (hΩ.chart i).open_source hKsource
  obtain ⟨R, hR, hKball⟩ := hKcompact.isBounded.subset_closedBall_lt 0 (0 : ℝ^n)
  obtain ⟨L, hLip⟩ := (hΩ.chart_contDiff i).contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall (0 : ℝ^n) (R + δ)) (isCompact_closedBall (0 : ℝ^n) (R + δ))
  obtain ⟨M, hM⟩ := hKcompact.exists_bound_of_continuousOn
    ((PiLp.continuous_apply 2 (fun _ : Fin n ↦ ℝ) (PDE.Common.lastIndex (n := n))).comp
      (hΩ.chart_contDiff i).continuous).continuousOn
  refine ⟨max (L : ℝ) (max M 0 / δ), L.2.trans (le_max_left _ _), fun x ⟨hxK, hxΩ⟩ ↦ ?_⟩
  obtain ⟨z, hzFrontier, hdistComplement⟩ :=
    exists_mem_frontier_infDist_compl_eq_dist hxΩ ne_univ
  have hdist : Metric.infDist x (frontier Ω) = dist x z :=
    le_antisymm (Metric.infDist_le_dist_of_mem hzFrontier) (hdistComplement ▸
      Metric.infDist_le_infDist_of_subset
        (fun y hy ↦ (hΩ.isOpen.frontier_eq ▸ hy : y ∈ closure Ω \ Ω).2) ⟨z, hzFrontier⟩)
  have hxR := Metric.mem_closedBall.1 (hKball hxK)
  rw [hdist]
  by_cases hnear : dist x z ≤ δ
  · have hzx : dist z x ≤ δ := dist_comm x z ▸ hnear
    have hzFlat : hΩ.chart i z ∈ frontier (HalfSpace.upper n) := by
      simpa [HalfSpace.frontier_upper (n := n)] using (chart_mem_boundary_iff (n := n) (Ω := Ω) i
        (hthick (Metric.mem_cthickening_of_dist_le z x δ K hxK hzx))).2 hzFrontier
    rw [← HalfSpace.infDist_frontier_upper_eq_last (n := n)
      ((hΩ.chart_mem_iff_upper i x (hKsource hxK)).1 hxΩ)]
    calc _ ≤ dist (hΩ.chart i x) (hΩ.chart i z) := Metric.infDist_le_dist_of_mem hzFlat
      _ ≤ L * dist x z := hLip.dist_le_mul x (Metric.mem_closedBall.2 (by linarith)) z
          (Metric.mem_closedBall.2 (by linarith [dist_triangle z x 0]))
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg
  · calc _ ≤ max M 0 := (Real.le_norm_self _).trans ((hM x hxK).trans (le_max_left M 0))
      _ ≤ max M 0 / δ * dist x z := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
        exact mul_le_mul_of_nonneg_left (not_le.1 hnear).le (le_max_right M 0)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg

/-- The image of the portion of `∂Ω` covered by a chart is exactly the portion
of the flat boundary lying in the chart target. -/
theorem chart_image_boundary (i : Fin hΩ.N) :
    hΩ.chart i '' ((hΩ.chart i).source ∩ frontier Ω) =
      (hΩ.chart i).target ∩ HalfSpace.boundary n :=
  (chart_isImage_boundary (n := n) (Ω := Ω) i).image_eq

/-- The partition function supplied by the operational `Boundary.C1ExtensionAtlas`. -/
def partitionSum (x : ℝ^n) : ℝ :=
  hΩ.interiorCutoff.toFun x + ∑ i, (hΩ.boundaryCutoff i).toFun x

/-- The partition sum is continuous, being a finite sum of test functions. -/
theorem continuous_partitionSum :
    Continuous (partitionSum (n := n) (Ω := Ω)) := by
  exact hΩ.interiorCutoff.continuous.add
    (continuous_finsetSum _ fun i _ ↦ (hΩ.boundaryCutoff i).continuous)

/-- The partition identity extends from the open domain to its closure. -/
theorem partitionSum_eq_one_on_closure {x : ℝ^n} (hx : x ∈ closure Ω) :
    partitionSum (n := n) (Ω := Ω) x = 1 := by
  have heq : Set.EqOn (partitionSum (n := n) (Ω := Ω)) (fun _ ↦ (1 : ℝ)) Ω := by
    intro y hy
    exact hΩ.cutoff_sum_eq_one y hy
  exact heq.closure (continuous_partitionSum (n := n) (Ω := Ω))
    continuous_const hx

/-- The interior partition term vanishes on the boundary, so the boundary
chart functions alone sum to one there. -/
theorem sum_boundary_partition_eq_one {x : ℝ^n} (hx : x ∈ frontier Ω) :
    ∑ i, (hΩ.boundaryCutoff i).toFun x = 1 := by
  have hxClosure : x ∈ closure Ω := frontier_subset_closure hx
  have hxNot : x ∉ Ω := by
    rw [hΩ.isOpen.frontier_eq] at hx
    exact hx.2
  have hψ₀ : hΩ.interiorCutoff.toFun x = 0 := by
    by_contra hne
    exact hxNot (hΩ.interiorCutoff_support (subset_tsupport _ hne))
  have h := partitionSum_eq_one_on_closure
    (n := n) (Ω := Ω) hxClosure
  simpa [partitionSum, hψ₀] using h

/-- Every boundary point belongs to the source of at least one boundary
chart.  Thus chart coverage is derived from the partition data, not
added as another assumption. -/
theorem exists_chart_source_of_mem_frontier {x : ℝ^n}
    (hx : x ∈ frontier Ω) :
    ∃ i : Fin hΩ.N, x ∈ (hΩ.chart i).source := by
  classical
  have hxClosure : x ∈ closure Ω := frontier_subset_closure hx
  have hxNot : x ∉ Ω := by
    rw [hΩ.isOpen.frontier_eq] at hx
    exact hx.2
  have hψ₀ : hΩ.interiorCutoff.toFun x = 0 := by
    by_contra hne
    exact hxNot (hΩ.interiorCutoff_support (subset_tsupport _ hne))
  have hsum : ∑ i, (hΩ.boundaryCutoff i).toFun x = 1 := by
    have h := partitionSum_eq_one_on_closure
      (n := n) (Ω := Ω) hxClosure
    simpa [partitionSum, hψ₀] using h
  have hex : ∃ i : Fin hΩ.N, (hΩ.boundaryCutoff i).toFun x ≠ 0 := by
    by_contra h
    push Not at h
    have : (∑ i, (hΩ.boundaryCutoff i).toFun x) = 0 := by simp [h]
    linarith
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, hΩ.boundaryCutoff_support i (subset_tsupport _ hi)⟩

/-- The boundary chart sources cover `∂Ω`. This is a consequence of the partition of unity: the
interior cutoff vanishes on `∂Ω`, so at each boundary point some boundary cutoff is nonzero, and
that cutoff is supported in its chart source. -/
theorem frontier_subset_iUnion_chart_source :
    frontier Ω ⊆ ⋃ i : Fin hΩ.N, (hΩ.chart i).source := by
  intro x hx
  obtain ⟨i, hi⟩ := exists_chart_source_of_mem_frontier
    (n := n) (Ω := Ω) hx
  exact Set.mem_iUnion.2 ⟨i, hi⟩

/-- An inverse boundary chart is Lipschitz on its bounded chart target.  The
constant is obtained from the bounded derivative on the compact closure of
the target's convex hull. -/
theorem exists_chart_symm_lipschitzOnWith (i : Fin hΩ.N) :
    ∃ C : ℝ≥0, LipschitzOnWith C (hΩ.chart i).symm (hΩ.chart i).target := by
  let K : Set (ℝ^n) := closure (convexHull ℝ (hΩ.chart i).target)
  have hKBounded : Bornology.IsBounded K := by
    exact (isBounded_convexHull.mpr (hΩ.chart_target_bounded i)).closure
  have hKCompact : IsCompact K := by
    simpa [K] using hKBounded.isCompact_closure
  have htargetK : (hΩ.chart i).target ⊆ K :=
    (subset_convexHull ℝ _).trans subset_closure
  have hKConvex : Convex ℝ K :=
    (convex_convexHull ℝ (hΩ.chart i).target).closure
  obtain ⟨C, hC⟩ :=
    (hΩ.chart_symm_contDiff i).contDiffOn.exists_lipschitzOnWith
      (by norm_num) hKConvex hKCompact
  exact ⟨C, hC.mono htargetK⟩

/-- A boundary chart is Lipschitz on the bounded physical boundary piece
covered by that chart. -/
theorem exists_chart_lipschitzOnWith_boundary_piece (i : Fin hΩ.N) :
    ∃ C : ℝ≥0,
      LipschitzOnWith C (hΩ.chart i)
        ((hΩ.chart i).source ∩ frontier Ω) := by
  let A : Set (ℝ^n) := (hΩ.chart i).source ∩ frontier Ω
  let K : Set (ℝ^n) := closure (convexHull ℝ A)
  have hABounded : Bornology.IsBounded A := by
    exact hΩ.bounded.closure.subset fun _ hx ↦
      frontier_subset_closure hx.2
  have hKBounded : Bornology.IsBounded K := by
    exact (isBounded_convexHull.mpr hABounded).closure
  have hKCompact : IsCompact K := by
    simpa [K] using hKBounded.isCompact_closure
  have hAK : A ⊆ K :=
    (subset_convexHull ℝ _).trans subset_closure
  have hKConvex : Convex ℝ K :=
    (convex_convexHull ℝ A).closure
  obtain ⟨C, hC⟩ :=
    (hΩ.chart_contDiff i).contDiffOn.exists_lipschitzOnWith
      (by norm_num) hKConvex hKCompact
  exact ⟨C, hC.mono hAK⟩

/-- Quantitative codimension-one surface-measure distortion under an inverse
boundary chart. -/
theorem exists_chart_symm_surfaceMeasure_image_le (i : Fin hΩ.N) :
    ∃ C : ℝ≥0, ∀ s : Set (ℝ^n), s ⊆ (hΩ.chart i).target →
      Measure.euclideanHausdorffMeasure (n - 1) ((hΩ.chart i).symm '' s) ≤
        (C : ℝ≥0∞) ^ ((n - 1 : ℕ) : ℝ) *
          Measure.euclideanHausdorffMeasure (n - 1) s := by
  obtain ⟨C, hLip⟩ :=
    exists_chart_symm_lipschitzOnWith (n := n) (Ω := Ω) i
  refine ⟨C, fun s hs ↦ ?_⟩
  exact
    (hLip.mono hs).euclideanHausdorffMeasure_image_le (n - 1)

/-- Every chart-covered boundary piece has finite intrinsic surface measure. -/
theorem chartBoundaryPiece_surfaceMeasure_lt_top
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (i : Fin hΩ.N) :
    Measure.euclideanHausdorffMeasure m
      ((hΩ.chart i).source ∩ frontier Ω) < ∞ := by
  let s : Set (ℝ^(m + 1)) := (hΩ.chart i).target ∩ HalfSpace.boundary (m + 1)
  have hsMeas : MeasurableSet s := (hΩ.chart i).open_target.measurableSet.inter
    (HalfSpace.frontier_upper (n := m + 1) ▸ isClosed_frontier.measurableSet)
  have hlast : PDE.Common.lastIndex (n := m + 1) = Fin.last m :=
    Fin.ext (by simp [PDE.Common.lastIndex])
  have hflatEq : Measure.euclideanHausdorffMeasure m s =
      Boundary.Geometry.SurfaceMeasure.flatSurfaceMeasure (n := m) s := by
    rw [Boundary.Geometry.SurfaceMeasure.flatSurfaceMeasure, Measure.restrict_apply hsMeas,
      inter_eq_self_of_subset_left fun x hx ↦ by simpa [HalfSpace.boundary, hlast] using hx.2]
  obtain ⟨C, hC⟩ := exists_chart_symm_surfaceMeasure_image_le (n := m + 1) (Ω := Ω) i
  have hdist := hC s inter_subset_left
  rw [show (hΩ.chart i).symm '' s = (hΩ.chart i).source ∩ frontier Ω by
    simpa [s] using (chart_isImage_boundary (n := m + 1) (Ω := Ω) i).symm_image_eq] at hdist
  have hrhs : (C : ℝ≥0∞) ^ (m : ℝ) * Measure.euclideanHausdorffMeasure m s < ∞ := by
    rw [hflatEq]
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.coe_ne_top)
      (Boundary.Geometry.SurfaceMeasure.flatSurfaceMeasure_lt_top_of_bounded
        ((hΩ.chart_target_bounded i).subset inter_subset_left))
  exact lt_of_le_of_lt (by simpa using hdist) hrhs

/-- A bounded operational `C¹` domain has finite intrinsic boundary surface
measure. -/
theorem surfaceMeasure_lt_top_of_isC1ExtensionAtlas
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω] :
    Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω Set.univ < ∞ := by
  let μ : Measure (ℝ^(m + 1)) :=
    Measure.euclideanHausdorffMeasure m
  let piece : Fin hΩ.N → Set (ℝ^(m + 1)) := fun i ↦
    (hΩ.chart i).source ∩ frontier Ω
  have hcover : frontier Ω ⊆ ⋃ i, piece i := by
    intro x hx
    obtain ⟨i, hi⟩ := exists_chart_source_of_mem_frontier
      (n := m + 1) (Ω := Ω) hx
    exact Set.mem_iUnion.2 ⟨i, hi, hx⟩
  have hpieces : μ (⋃ i, piece i) < ∞ := by
    have h := measure_biUnion_lt_top
      (μ := μ) (s := (Set.univ : Set (Fin hΩ.N))) Set.finite_univ
      (fun i _ ↦ chartBoundaryPiece_surfaceMeasure_lt_top
        (m := m) (Ω := Ω) i)
    simpa [piece, μ] using h
  have hfrontier : μ (frontier Ω) < ∞ :=
    (measure_mono hcover).trans_lt hpieces
  simpa [Boundary.Geometry.SurfaceMeasure.surfaceMeasure, μ] using hfrontier

/-- Intrinsic surface measure on a bounded operational `C¹` domain is a
finite measure. -/
instance isFiniteMeasure_surfaceMeasure
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [Boundary.C1ExtensionAtlas (m + 1) Ω] :
    IsFiniteMeasure
      (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω) :=
  ⟨surfaceMeasure_lt_top_of_isC1ExtensionAtlas
    (m := m) (Ω := Ω)⟩

end Trace.C1
end SobolevSpace
