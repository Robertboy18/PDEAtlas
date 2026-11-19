/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.Coordinates
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.FiniteExponent.LocalTrace
import PDE.Spaces.Sobolev.Boundary.Trace.C1.ZeroTrace.Localization

/-!
# Fractional regularity of the physical boundary coordinates

The partitioned surface trace, transported to Euclidean chart coordinates and extended
by zero off the chart target, is exactly the base coordinate of the localized Gagliardo
trace. The support and measure-transport arguments include the complement of each chart.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1.Fractional.FiniteExponent

open MeasureTheory Set
open SobolevSpace.Fractional
open Boundary.Geometry.SurfaceMeasure Extension.C1.BoundaryPiece
open scoped ENNReal Sobolev

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
variable (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]

/-- A chart contribution to the physical trace is multiplication by its partition factor. -/
theorem localPhysicalTraceLp_eq_boundaryCutoff (i : Fin hΩ.N)
    (u : W^{1,ENNReal.ofReal p}(Ω)) :
    localPhysicalTraceLp p i u = boundaryCutoff (ENNReal.ofReal p) i (traceLp p u) := by
  apply Lp.ext
  exact (localPhysicalTraceLp_eq_cutoff_mul_ae p i u).trans
    (boundaryCutoff_apply_ae (ENNReal.ofReal p) i _).symm

/-- The zero-extended chart coordinates of the physical trace are its flat Lᵖ trace. -/
theorem localizedBoundaryCoordinates_traceLp (hp : 1 < p) (i : Fin hΩ.N)
    (u : W^{1,ENNReal.ofReal p}(Ω)) :
    localizedBoundaryCoordinates (ENNReal.ofReal p) i (traceLp p u) =
      HalfSpace.traceLp m p hp.le (flattenCLM (p := ENNReal.ofReal p) i u) := by
  let f := localFlatTraceLp p i u
  let v := HalfSpace.traceLp m p hp.le (flattenCLM (p := ENNReal.ofReal p) i u)
  have hflatMap : MeasurePreserving (flatEmbedding (n := m))
      (volume : Measure (ℝ^m)) (flatSurfaceMeasure (n := m)) :=
    ⟨(isometry_flatEmbedding (n := m)).continuous.measurable, map_flatEmbedding_volume⟩
  have hfv : (f : ℝ^(m + 1) → ℝ) =ᵐ[flatSurfaceMeasure (n := m)]
      fun x ↦ v (flatProjection x) := by
    have h := liftLp_apply_ae (n := m) (ENNReal.ofReal p) v
    change (f : ℝ^(m + 1) → ℝ) =ᵐ[flatSurfaceMeasure (n := m)] _ at h
    exact h
  have hfv' : (fun y ↦ f (flatEmbedding y)) =ᵐ[volume] v := by
    filter_upwards [hflatMap.quasiMeasurePreserving.ae hfv] with y hy
    simpa only [flatProjection_flatEmbedding] using hy
  have hphysical := (chartBoundaryReferenceMeasure_absolutelyContinuous_surfaceMeasure i).ae_eq
    (localPhysicalTraceLp_apply_ae p i u)
  have hparameter := (measurePreserving_chartBoundaryParametrization i).quasiMeasurePreserving.ae
    hphysical
  have hon : ∀ᵐ y ∂(volume : Measure (ℝ^m)).restrict (chartBoundaryParameterDomain i),
      localPhysicalTraceLp p i u (chartBoundaryParametrization i y) = f (flatEmbedding y) := by
    filter_upwards [hparameter,
      ae_restrict_mem (isOpen_chartBoundaryParameterDomain (Ω := Ω) i).measurableSet]
      with y hy hyD
    have hx : chartBoundaryParametrization i y ∈ chartBoundaryPatch (Ω := Ω) i := by
      change chartBoundaryParametrization i y ∈ (hΩ.chart i).source ∩ frontier Ω
      rw [← image_chartBoundaryParametrization i]
      exact mem_image_of_mem _ hyD
    rw [indicator_of_mem hx] at hy
    simpa only [chartBoundaryParametrization, (hΩ.chart i).right_inv hyD] using hy
  have hon' := (ae_restrict_iff'
    (isOpen_chartBoundaryParameterDomain (Ω := Ω) i).measurableSet).mp hon
  have hoff := (ae_restrict_iff' (hΩ.chart i).open_target.measurableSet.compl).mp
    (localFlatTraceLp_eq_zero_off_target p i u)
  have hoff' := hflatMap.quasiMeasurePreserving.ae hoff
  change boundaryCoordinates (ENNReal.ofReal p) i
    (boundaryCutoff (ENNReal.ofReal p) i (traceLp p u)) = v
  rw [← localPhysicalTraceLp_eq_boundaryCutoff]
  apply Lp.ext
  filter_upwards [boundaryCoordinates_apply_ae (ENNReal.ofReal p) i (localPhysicalTraceLp p i u),
    hon', hoff', hfv']
    with y hy honY hoffY hfvY
  rw [hy]
  by_cases hyD : y ∈ chartBoundaryParameterDomain (Ω := Ω) i
  · rw [indicator_of_mem hyD, honY hyD, hfvY]
  · rw [indicator_of_notMem hyD]
    exact (hfvY.symm.trans (hoffY hyD)).symm

/-- The chart graph has precisely the localized physical trace as its base coordinate. -/
theorem toLp_localTrace_eq_localizedBoundaryCoordinates (hp : 1 < p) (i : Fin hΩ.N)
    (u : W^{1,ENNReal.ofReal p}(Ω)) :
    GagliardoSpace.toLp m (1 - 1 / p) univ (localTrace p hp i u) =
      Lp.restrictionCLMOfLE Measure.restrict_le_self
        (localizedBoundaryCoordinates (ENNReal.ofReal p) i (traceLp p u)) := by
  rw [toLp_localTrace, localizedBoundaryCoordinates_traceLp p hp]

/-- Every partitioned coordinate of a trace has order `1 - 1 / p` regularity. -/
theorem memGagliardo_localizedBoundaryCoordinates_traceLp (hp : 1 < p) (i : Fin hΩ.N)
    (u : W^{1,ENNReal.ofReal p}(Ω)) :
    MemGagliardo m (1 - 1 / p) univ
      (localizedBoundaryCoordinates (ENNReal.ofReal p) i (traceLp p u) : ℝ^m → ℝ)
      (p := ENNReal.ofReal p) := by
  rw [localizedBoundaryCoordinates_traceLp p hp]
  exact HalfSpace.memGagliardo_traceLp m p hp _

end SobolevSpace.Trace.C1.Fractional.FiniteExponent
