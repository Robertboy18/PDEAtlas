/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.MeasureClass
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Geometry
import PDE.Analysis.MeasureTheory.ParametrizedArea

/-!
# Boundary data in unweighted chart coordinates

The forward chart is Lipschitz on its physical boundary patch. Hausdorff measure
distortion therefore bounds unweighted parameter measure by intrinsic surface measure.
This is the quantitative direction needed to pull physical boundary data into a
Euclidean fractional space; no Jacobian density is multiplied into the boundary value.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Trace.C1.Fractional

open MeasureTheory Set
open Boundary.Geometry.SurfaceMeasure
open scoped ENNReal NNReal

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- The unweighted reference measure is quantitatively controlled by surface measure. -/
theorem exists_chartBoundaryReferenceMeasure_le (i : Fin hΩ.N) :
    ∃ c : ℝ≥0, chartBoundaryReferenceMeasure (Ω := Ω) i ≤
      (c : ℝ≥0∞) • surfaceMeasure Ω := by
  obtain ⟨C, hLip⟩ := exists_chart_lipschitzOnWith_boundary_piece
    (n := m + 1) (Ω := Ω) i
  refine ⟨C ^ m, Measure.le_iff.mpr fun s hs ↦ ?_⟩
  have himage :
      flatEmbedding '' (chartBoundaryParametrization (Ω := Ω) i ⁻¹' s ∩
        chartBoundaryParameterDomain i) =
      hΩ.chart i '' (s ∩ chartBoundaryPatch i) := by
    ext z
    constructor
    · rintro ⟨y, ⟨hyS, hyD⟩, rfl⟩
      have hx : chartBoundaryParametrization i y ∈ chartBoundaryPatch (Ω := Ω) i := by
        change chartBoundaryParametrization i y ∈ (hΩ.chart i).source ∩ frontier Ω
        rw [← image_chartBoundaryParametrization i]
        exact mem_image_of_mem _ hyD
      exact ⟨chartBoundaryParametrization i y, ⟨hyS, hx⟩, (hΩ.chart i).right_inv hyD⟩
    · rintro ⟨x, ⟨hxS, hxSource, hxFrontier⟩, rfl⟩
      let y := flatProjection (hΩ.chart i x)
      have hxFlat : hΩ.chart i x ∈ HalfSpace.boundary (m + 1) :=
        (chart_mem_boundary_iff (n := m + 1) (Ω := Ω) i hxSource).mpr hxFrontier
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
  rw [chartBoundaryReferenceMeasure,
    Measure.map_apply (contDiff_chartBoundaryParametrization i).continuous.measurable hs,
    Measure.restrict_apply
      ((contDiff_chartBoundaryParametrization i).continuous.measurable hs),
    ← EuclideanSpace.euclideanHausdorffMeasure_eq_volume m,
    ← (isometry_flatEmbedding (n := m)).euclideanHausdorffMeasure_image, himage]
  have hdist := (hLip.mono (inter_subset_right (s := s))).euclideanHausdorffMeasure_image_le m
  have hmono :
      Measure.euclideanHausdorffMeasure m (s ∩ chartBoundaryPatch (Ω := Ω) i) ≤
        surfaceMeasure Ω s := by
    rw [surfaceMeasure, Measure.restrict_apply hs]
    exact measure_mono (fun _ hx ↦ ⟨hx.1, hx.2.2⟩)
  simpa only [Measure.smul_apply, ENNReal.coe_pow, ENNReal.rpow_natCast,
    smul_eq_mul, chartBoundaryPatch] using
    hdist.trans (mul_le_mul_right hmono ((C : ℝ≥0∞) ^ (m : ℝ)))

/-- A finite chart distortion bound for pulling surface data to parameter coordinates. -/
def chartCoordinateBound (i : Fin hΩ.N) : ℝ≥0 :=
  (exists_chartBoundaryReferenceMeasure_le (Ω := Ω) i).choose

/-- The chosen coordinate distortion bound controls unweighted reference measure. -/
theorem chartBoundaryReferenceMeasure_le (i : Fin hΩ.N) :
    chartBoundaryReferenceMeasure (Ω := Ω) i ≤
      (chartCoordinateBound i : ℝ≥0∞) • surfaceMeasure Ω :=
  (exists_chartBoundaryReferenceMeasure_le (Ω := Ω) i).choose_spec

/-- Boundary parametrization preserves its unweighted pushforward measure. -/
theorem measurePreserving_chartBoundaryParametrization (i : Fin hΩ.N) :
    MeasurePreserving (chartBoundaryParametrization (Ω := Ω) i)
      ((volume : Measure (ℝ^m)).restrict (chartBoundaryParameterDomain i))
      (chartBoundaryReferenceMeasure i) :=
  ⟨(contDiff_chartBoundaryParametrization i).continuous.measurable, rfl⟩

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Pull physical boundary data to a chart's parameter domain and extend by zero. -/
def boundaryCoordinates (i : Fin hΩ.N) :
    Lp ℝ p (surfaceMeasure Ω) →L[ℝ] Lp ℝ p (volume : Measure (ℝ^m)) :=
  (Lp.extendByZeroₗᵢ (𝕜 := ℝ)
    (isOpen_chartBoundaryParameterDomain (Ω := Ω) i).measurableSet).toContinuousLinearMap.comp
      ((Lp.compMeasurePreservingₗᵢ ℝ (chartBoundaryParametrization (Ω := Ω) i)
        (measurePreserving_chartBoundaryParametrization i)).toContinuousLinearMap.comp
          (Lp.LpToLpOfMeasureLeSMul (p := p) (E := ℝ) ENNReal.coe_ne_top
            (chartBoundaryReferenceMeasure_le i)))

/-- Boundary coordinates are the unweighted composition with the inverse chart. -/
theorem boundaryCoordinates_apply_ae (i : Fin hΩ.N) (g : Lp ℝ p (surfaceMeasure Ω)) :
    (boundaryCoordinates p i g : ℝ^m → ℝ) =ᵐ[volume]
      (chartBoundaryParameterDomain i).indicator
        (fun y ↦ g (chartBoundaryParametrization i y)) := by
  let D := chartBoundaryParameterDomain (Ω := Ω) i
  let ρ := chartBoundaryReferenceMeasure (Ω := Ω) i
  let R : Lp ℝ p (surfaceMeasure Ω) →L[ℝ] Lp ℝ p ρ :=
    Lp.LpToLpOfMeasureLeSMul (p := p) (E := ℝ) ENNReal.coe_ne_top
      (chartBoundaryReferenceMeasure_le i)
  let P : Lp ℝ p ρ →ₗᵢ[ℝ] Lp ℝ p ((volume : Measure (ℝ^m)).restrict D) :=
    Lp.compMeasurePreservingₗᵢ ℝ (chartBoundaryParametrization i)
      (measurePreserving_chartBoundaryParametrization i)
  have hR : (R g : ℝ^(m + 1) → ℝ) =ᵐ[ρ] g :=
    Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.coe_ne_top
      (chartBoundaryReferenceMeasure_le i) g
  have hP : (P (R g) : ℝ^m → ℝ) =ᵐ[volume.restrict D]
      fun y ↦ R g (chartBoundaryParametrization i y) := by
    exact Lp.coeFn_compMeasurePreserving (R g)
      (measurePreserving_chartBoundaryParametrization i)
  have hcomp : (fun y ↦ R g (chartBoundaryParametrization i y)) =ᵐ[volume.restrict D]
      fun y ↦ g (chartBoundaryParametrization i y) :=
    (measurePreserving_chartBoundaryParametrization i).quasiMeasurePreserving.ae hR
  have hindicator := (ae_eq_restrict_iff_indicator_ae_eq
    (isOpen_chartBoundaryParameterDomain (Ω := Ω) i).measurableSet).mp (hP.trans hcomp)
  exact (Lp.extendByZeroₗᵢ_apply_ae (𝕜 := ℝ)
    (isOpen_chartBoundaryParameterDomain (Ω := Ω) i).measurableSet (P (R g))).trans hindicator

/-- The coordinate map has the expected surface-distortion bound at every normed exponent. -/
theorem norm_boundaryCoordinates_le (i : Fin hΩ.N) (g : Lp ℝ p (surfaceMeasure Ω)) :
    ‖boundaryCoordinates p i g‖ ≤
      (chartCoordinateBound (Ω := Ω) i : ℝ) ^ (1 / p).toReal * ‖g‖ := by
  let R := Lp.LpToLpOfMeasureLeSMul (p := p) (E := ℝ) ENNReal.coe_ne_top
    (chartBoundaryReferenceMeasure_le (Ω := Ω) i)
  calc
    ‖boundaryCoordinates p i g‖ = ‖R g‖ := by simp [boundaryCoordinates, R]
    _ ≤ ‖R‖ * ‖g‖ := R.le_opNorm g
    _ ≤ _ := by
      gcongr
      simpa using Lp.norm_LpToLpOfMeasureLeSMul_le
        (p := p) (E := ℝ) ENNReal.coe_ne_top (chartBoundaryReferenceMeasure_le i)

/-- The atlas boundary partition acting on surface `Lᵖ` data. -/
def boundaryCutoff (i : Fin hΩ.N) :
    Lp ℝ p (surfaceMeasure Ω) →L[ℝ] Lp ℝ p (surfaceMeasure Ω) :=
  let ψ := hΩ.boundaryCutoff i
  let hψ : MemLp ψ.toFun ∞ (surfaceMeasure Ω) :=
    ψ.contDiff.continuous.memLp_top_of_hasCompactSupport ψ.hasCompactSupport _
  (ContinuousLinearMap.mul ℝ ℝ).holderL (surfaceMeasure Ω) ∞ p p (hψ.toLp ψ.toFun)

/-- The boundary cutoff multiplies the physical representative by the partition function. -/
theorem boundaryCutoff_apply_ae (i : Fin hΩ.N) (g : Lp ℝ p (surfaceMeasure Ω)) :
    (boundaryCutoff p i g : ℝ^(m + 1) → ℝ) =ᵐ[surfaceMeasure Ω]
      fun x ↦ (hΩ.boundaryCutoff i).toFun x * g x := by
  let ψ := hΩ.boundaryCutoff i
  let hψ : MemLp ψ.toFun ∞ (surfaceMeasure Ω) :=
    ψ.contDiff.continuous.memLp_top_of_hasCompactSupport ψ.hasCompactSupport _
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder
    (r := p) (hψ.toLp ψ.toFun) g, hψ.coeFn_toLp] with x hx hψx
  change boundaryCutoff p i g x = (hψ.toLp ψ.toFun) x * g x at hx
  rw [hψx] at hx
  exact hx

/-- The localized boundary coordinates used to test fractional boundary regularity. -/
def localizedBoundaryCoordinates (i : Fin hΩ.N) :
    Lp ℝ p (surfaceMeasure Ω) →L[ℝ] Lp ℝ p (volume : Measure (ℝ^m)) :=
  (boundaryCoordinates p i).comp (boundaryCutoff p i)

/-- Localized coordinates are the zero extension of the partitioned physical boundary value. -/
theorem localizedBoundaryCoordinates_apply_ae (i : Fin hΩ.N)
    (g : Lp ℝ p (surfaceMeasure Ω)) :
    (localizedBoundaryCoordinates p i g : ℝ^m → ℝ) =ᵐ[volume]
      (chartBoundaryParameterDomain i).indicator (fun y ↦
        (hΩ.boundaryCutoff i).toFun (chartBoundaryParametrization i y) *
          g (chartBoundaryParametrization i y)) := by
  have hcutoff := (chartBoundaryReferenceMeasure_absolutelyContinuous_surfaceMeasure i).ae_eq
    (boundaryCutoff_apply_ae p i g)
  have hcomp := (measurePreserving_chartBoundaryParametrization i).quasiMeasurePreserving.ae
    hcutoff
  exact (boundaryCoordinates_apply_ae p i (boundaryCutoff p i g)).trans
    ((ae_eq_restrict_iff_indicator_ae_eq
      (isOpen_chartBoundaryParameterDomain (Ω := Ω) i).measurableSet).mp hcomp)

end SobolevSpace.Trace.C1.Fractional
