/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Cutoffs
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Physicalization
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Geometry

/-!
# C¹ chart representatives with values in a real normed space

For a finite C¹ extension atlas, the boundary partition localizes an ambient C¹ function.
Composing each piece with the inverse chart and multiplying by the auxiliary target cutoff
gives a compactly supported C¹ function. Transporting its flat boundary class back to the
physical surface recovers exactly one boundary partition factor. Their finite sum recovers
the original boundary values.

The target need not be finite-dimensional or complete. Compact support is supplied by the
chart cutoff, so the ambient function itself need not have compact support.
-/

@[expose] public noncomputable section

namespace SobolevSpace.VectorValued.Trace.C1

open MeasureTheory Set
open Boundary.Geometry.SurfaceMeasure
open Boundary.C1ExtensionAtlas.DerivedCutoffs
open SobolevSpace.Trace.C1 (chartPhysicalization chartPhysicalization_apply_ae
  chartBoundaryPatch measurableSet_chartBoundaryPatch measurePreserving_chart_boundaryPatch
  chartPushedSurfaceMeasure_le sum_boundary_partition_eq_one)
open scoped ENNReal Sobolev

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A boundary partition piece in chart coordinates, with a compact target cutoff. -/
def flattenedClassicalPiece (i : Fin hΩ.N) (f : ℝ^(m + 1) → F) :
    ℝ^(m + 1) → F :=
  fun y ↦ (targetSupportCutoff i).toFun y •
    ((hΩ.boundaryCutoff i).toFun ((hΩ.chart i).symm y) • f ((hΩ.chart i).symm y))

/-- A C¹ chart preserves C¹ regularity of the localized representative. -/
theorem flattenedClassicalPiece_contDiff (i : Fin hΩ.N) {f : ℝ^(m + 1) → F}
    (hf : ContDiff ℝ 1 f) : ContDiff ℝ 1 (flattenedClassicalPiece i f) := by
  exact ((targetSupportCutoff i).contDiff.of_le (by simp)).smul
    ((((hΩ.boundaryCutoff i).contDiff.of_le (by simp)).comp
      (hΩ.chart_symm_contDiff i)).smul (hf.comp (hΩ.chart_symm_contDiff i)))

/-- The target cutoff supplies compact support independently of the ambient function. -/
theorem flattenedClassicalPiece_hasCompactSupport (i : Fin hΩ.N)
    (f : ℝ^(m + 1) → F) : HasCompactSupport (flattenedClassicalPiece i f) :=
  (targetSupportCutoff i).hasCompactSupport.smul_right

/-- On the chart source, the target cutoff leaves the boundary partition piece unchanged. -/
theorem flattenedClassicalPiece_chart_apply (i : Fin hΩ.N) (f : ℝ^(m + 1) → F)
    {x : ℝ^(m + 1)} (hx : x ∈ (hΩ.chart i).source) :
    flattenedClassicalPiece i f (hΩ.chart i x) =
      (hΩ.boundaryCutoff i).toFun x • f x := by
  by_cases hψ : (hΩ.boundaryCutoff i).toFun x = 0
  · simp [flattenedClassicalPiece, (hΩ.chart i).left_inv hx, hψ]
  · have hη := targetSupportCutoff_eq_one_on_boundarySupportInTarget i
      (hΩ.chart i x) ⟨x, subset_tsupport _ hψ, rfl⟩
    simp [flattenedClassicalPiece, (hΩ.chart i).left_inv hx, hη]

/-- The compact chart representative belongs to every flat surface `Lᵖ` space. -/
theorem flattenedClassicalPiece_memLp (p : ℝ≥0∞) (i : Fin hΩ.N)
    {f : ℝ^(m + 1) → F} (hf : ContDiff ℝ 1 f) :
    MemLp (flattenedClassicalPiece i f) p (flatSurfaceMeasure (n := m)) := by
  let : IsFiniteMeasureOnCompacts (flatSurfaceMeasure (n := m)) :=
    ⟨fun {_} hK ↦ flatSurfaceMeasure_lt_top_of_bounded hK.isBounded⟩
  exact (flattenedClassicalPiece_contDiff i hf).continuous.memLp_of_hasCompactSupport
    (flattenedClassicalPiece_hasCompactSupport i f)

/-- Physicalization of the compact chart representative recovers its boundary partition piece. -/
theorem chartPhysicalization_flattenedClassicalPiece (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (i : Fin hΩ.N) {f : ℝ^(m + 1) → F} (hf : ContDiff ℝ 1 f) :
    (chartPhysicalization p i
      ((flattenedClassicalPiece_memLp p i hf).toLp (flattenedClassicalPiece i f)) :
        ℝ^(m + 1) → F) =ᵐ[surfaceMeasure Ω] fun x ↦
          (hΩ.boundaryCutoff i).toFun x • f x := by
  have hrep := (flattenedClassicalPiece_memLp p i hf).coeFn_toLp
  have hcomp := (measurePreserving_chart_boundaryPatch i).quasiMeasurePreserving.ae
    ((Measure.absolutelyContinuous_of_le_smul (chartPushedSurfaceMeasure_le i)).ae_eq hrep)
  have hphysical := (chartPhysicalization_apply_ae p i
    ((flattenedClassicalPiece_memLp p i hf).toLp (flattenedClassicalPiece i f))).trans
      ((ae_eq_restrict_iff_indicator_ae_eq (measurableSet_chartBoundaryPatch i)).mp hcomp)
  have hfrontier : ∀ᵐ x ∂surfaceMeasure Ω, x ∈ frontier Ω :=
    ae_restrict_mem isClosed_frontier.measurableSet
  filter_upwards [hphysical, hfrontier] with x hx hxFrontier
  rw [hx]
  by_cases hxPatch : x ∈ chartBoundaryPatch (Ω := Ω) i
  · rw [indicator_of_mem hxPatch, flattenedClassicalPiece_chart_apply i f hxPatch.1]
  · rw [indicator_of_notMem hxPatch]
    have hψ : (hΩ.boundaryCutoff i).toFun x = 0 := by
      by_contra hne
      exact hxPatch ⟨hΩ.boundaryCutoff_support i (subset_tsupport _ hne), hxFrontier⟩
    simp [hψ]

/-- The finite chart partition reconstructs the physical boundary values of a C¹ function. -/
theorem sum_chartPhysicalization_flattenedClassicalPiece (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {f : ℝ^(m + 1) → F} (hf : ContDiff ℝ 1 f) :
    ((∑ i : Fin hΩ.N, chartPhysicalization p i
      ((flattenedClassicalPiece_memLp p i hf).toLp (flattenedClassicalPiece i f)) :
        Lp F p (surfaceMeasure Ω)) : ℝ^(m + 1) → F) =ᵐ[surfaceMeasure Ω] f := by
  classical
  let g (i : Fin hΩ.N) : Lp F p (surfaceMeasure Ω) :=
    chartPhysicalization p i
      ((flattenedClassicalPiece_memLp p i hf).toLp (flattenedClassicalPiece i f))
  have hsum (s : Finset (Fin hΩ.N)) :
      ((∑ i ∈ s, g i : Lp F p (surfaceMeasure Ω)) : ℝ^(m + 1) → F)
        =ᵐ[surfaceMeasure Ω] fun x ↦ ∑ i ∈ s, (hΩ.boundaryCutoff i).toFun x • f x := by
    induction s using Finset.induction_on with
    | empty =>
        filter_upwards [Lp.coeFn_zero F p (surfaceMeasure Ω)] with x hx
        simpa using hx
    | @insert i s hi ih =>
        filter_upwards [Lp.coeFn_add (g i) (∑ j ∈ s, g j),
          chartPhysicalization_flattenedClassicalPiece p i hf, ih] with x hadd hcut hsum
        simp only [Finset.sum_insert hi]
        rw [hadd]
        change g i x + (∑ j ∈ s, g j) x = _
        rw [hcut, hsum]
  have hfrontier : ∀ᵐ x ∂surfaceMeasure Ω, x ∈ frontier Ω :=
    ae_restrict_mem isClosed_frontier.measurableSet
  filter_upwards [hsum Finset.univ, hfrontier] with x hx hxFrontier
  rw [hx, ← Finset.sum_smul, sum_boundary_partition_eq_one hxFrontier, one_smul]

end SobolevSpace.VectorValued.Trace.C1
