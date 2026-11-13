/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.ChartTransport
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.Coordinates
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Geometry

/-!
# Reconstructing localized surface data

The coordinate of a surface datum already contains its partition factor `ψᵢ`.
The auxiliary target cutoff is one wherever this coordinate can be nonzero.
Consequently chart physicalization recovers `ψᵢ g`, without a second partition
factor. All representative identities below are almost-everywhere identities.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1.Fractional

open MeasureTheory Set
open Boundary.Geometry.SurfaceMeasure
open Boundary.C1ExtensionAtlas.DerivedCutoffs
open scoped ENNReal Sobolev

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- Physicalization carries any flat representative to its chartwise surface representative. -/
theorem chartPhysicalization_apply_ae_of_ae (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (i : Fin hΩ.N) {g : Lp ℝ p (flatSurfaceMeasure (n := m))}
    {f : ℝ^(m + 1) → ℝ}
    (hg : (g : ℝ^(m + 1) → ℝ) =ᵐ[flatSurfaceMeasure (n := m)] f) :
    (chartPhysicalization p i g : ℝ^(m + 1) → ℝ) =ᵐ[surfaceMeasure Ω]
      (chartBoundaryPatch i).indicator (fun x ↦ f (hΩ.chart i x)) := by
  have hcomp := (measurePreserving_chart_boundaryPatch i).quasiMeasurePreserving.ae
    ((Measure.absolutelyContinuous_of_le_smul (chartPushedSurfaceMeasure_le i)).ae_eq hg)
  exact (chartPhysicalization_apply_ae p i g).trans
    ((ae_eq_restrict_iff_indicator_ae_eq (measurableSet_chartBoundaryPatch i)).mp hcomp)

/-- On the flat hyperplane, localized coordinates are the partitioned inverse-chart pullback. -/
theorem liftLp_localizedBoundaryCoordinates_apply_ae (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (i : Fin hΩ.N) (g : Lp ℝ p (surfaceMeasure Ω)) :
    (liftLp p (localizedBoundaryCoordinates p i g) : ℝ^(m + 1) → ℝ)
      =ᵐ[flatSurfaceMeasure (n := m)]
        (hΩ.chart i).target.indicator (fun y ↦
          (hΩ.boundaryCutoff i).toFun ((hΩ.chart i).symm y) *
            g ((hΩ.chart i).symm y)) := by
  have hcoords := (measurePreserving_flatProjection (n := m)).quasiMeasurePreserving.ae
    (localizedBoundaryCoordinates_apply_ae p i g)
  have hflat : ∀ᵐ y ∂flatSurfaceMeasure (n := m), y (Fin.last m) = 0 :=
    ae_restrict_mem (isClosed_eq
      (PiLp.continuous_apply 2 (fun _ : Fin (m + 1) ↦ ℝ) (Fin.last m))
      continuous_const).measurableSet
  filter_upwards [liftLp_apply_ae p (localizedBoundaryCoordinates p i g), hcoords, hflat]
    with y hy hc hn
  rw [hy, hc]
  have he := flatEmbedding_flatProjection_of_last_eq_zero hn
  by_cases hyT : y ∈ (hΩ.chart i).target
  · have hyD : flatProjection y ∈ chartBoundaryParameterDomain (Ω := Ω) i := by
      change flatEmbedding (flatProjection y) ∈ (hΩ.chart i).target
      rwa [he]
    rw [indicator_of_mem hyD, indicator_of_mem hyT]
    simp only [chartBoundaryParametrization, he]
  · have hyD : flatProjection y ∉ chartBoundaryParameterDomain (Ω := Ω) i := by
      change flatEmbedding (flatProjection y) ∉ (hΩ.chart i).target
      rwa [he]
    rw [indicator_of_notMem hyD, indicator_of_notMem hyT]

/-- The auxiliary target cutoff fixes data already localized by the boundary partition. -/
theorem flatTargetCutoff_lift_localizedBoundaryCoordinates
    (i : Fin hΩ.N) (g : Lp ℝ 2 (surfaceMeasure Ω)) :
    flatTargetCutoff i (liftLp 2 (localizedBoundaryCoordinates 2 i g)) =
      liftLp 2 (localizedBoundaryCoordinates 2 i g) := by
  apply Lp.ext
  filter_upwards [
    flatTargetCutoff_apply_ae i (liftLp 2 (localizedBoundaryCoordinates 2 i g)),
    liftLp_localizedBoundaryCoordinates_apply_ae 2 i g
  ] with y hmul hcoords
  rw [hmul, hcoords]
  by_cases hyT : y ∈ (hΩ.chart i).target
  · rw [indicator_of_mem hyT]
    by_cases hψ : (hΩ.boundaryCutoff i).toFun ((hΩ.chart i).symm y) = 0
    · simp [hψ]
    · have hη := targetSupportCutoff_eq_one_on_boundarySupportInTarget i y
        ⟨(hΩ.chart i).symm y, subset_tsupport _ hψ, (hΩ.chart i).right_inv hyT⟩
      rw [hη, one_mul]
  · rw [indicator_of_notMem hyT, mul_zero]

/-- Pulling localized coordinates back to the surface recovers exactly one partition factor. -/
theorem chartPhysicalization_lift_localizedBoundaryCoordinates
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : Fin hΩ.N)
    (g : Lp ℝ p (surfaceMeasure Ω)) :
    chartPhysicalization p i (liftLp p (localizedBoundaryCoordinates p i g)) =
      boundaryCutoff p i g := by
  apply Lp.ext
  have hphysical := chartPhysicalization_apply_ae_of_ae p i
    (liftLp_localizedBoundaryCoordinates_apply_ae p i g)
  have hfrontier : ∀ᵐ x ∂surfaceMeasure Ω, x ∈ frontier Ω :=
    ae_restrict_mem isClosed_frontier.measurableSet
  filter_upwards [hphysical, boundaryCutoff_apply_ae p i g, hfrontier]
    with x hx hcut hxFrontier
  rw [hx, hcut]
  by_cases hxPatch : x ∈ chartBoundaryPatch (Ω := Ω) i
  · rw [indicator_of_mem hxPatch,
      indicator_of_mem ((hΩ.chart i).map_source hxPatch.1),
      (hΩ.chart i).left_inv hxPatch.1]
  · rw [indicator_of_notMem hxPatch]
    have hψ : (hΩ.boundaryCutoff i).toFun x = 0 := by
      by_contra hne
      exact hxPatch ⟨hΩ.boundaryCutoff_support i (subset_tsupport _ hne), hxFrontier⟩
    simp [hψ]

/-- The finite boundary partition reconstructs every surface `Lᵖ` datum. -/
theorem sum_boundaryCutoff (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (g : Lp ℝ p (surfaceMeasure Ω)) :
    ∑ i : Fin hΩ.N, boundaryCutoff p i g = g := by
  classical
  have hsum (s : Finset (Fin hΩ.N)) :
      ((∑ i ∈ s, boundaryCutoff p i g : Lp ℝ p (surfaceMeasure Ω)) :
        ℝ^(m + 1) → ℝ) =ᵐ[surfaceMeasure Ω]
          fun x ↦ ∑ i ∈ s, (hΩ.boundaryCutoff i).toFun x * g x := by
    induction s using Finset.induction_on with
    | empty =>
        filter_upwards [Lp.coeFn_zero ℝ p (surfaceMeasure Ω)] with x hx
        simpa using hx
    | @insert i s hi ih =>
        have hadd := Lp.coeFn_add (boundaryCutoff p i g) (∑ j ∈ s, boundaryCutoff p j g)
        filter_upwards [hadd, boundaryCutoff_apply_ae p i g, ih]
          with x hxadd hxcut hxsum
        simp only [Finset.sum_insert hi]
        rw [hxadd]
        change boundaryCutoff p i g x + (∑ j ∈ s, boundaryCutoff p j g) x = _
        rw [hxcut, hxsum]
  apply Lp.ext
  have hfrontier : ∀ᵐ x ∂surfaceMeasure Ω, x ∈ frontier Ω :=
    ae_restrict_mem isClosed_frontier.measurableSet
  filter_upwards [hsum Finset.univ, hfrontier] with x hx hxFrontier
  rw [hx, ← Finset.sum_mul, sum_boundary_partition_eq_one hxFrontier, one_mul]

end SobolevSpace.Trace.C1.Fractional
