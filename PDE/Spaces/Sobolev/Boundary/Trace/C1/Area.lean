/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import PDE.Spaces.Sobolev.Boundary.Atlas.Definitions
public import PDE.Spaces.Sobolev.Boundary.Geometry.SurfaceMeasure
import PDE.Analysis.MeasureTheory.ParametrizedArea
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal

/-!
# Boundary parametrizations and tangential Jacobians

An operational `C¹` boundary chart maps the physical domain to an upper half-space. Restricting
the inverse chart to the flat boundary hyperplane therefore gives a `C¹` parametrization
`Φᵢ(y) = (chartᵢ)⁻¹(y, 0)` of the corresponding physical boundary piece
`(chartᵢ).source ∩ ∂Ω`, defined on the open set of tangential parameters `y ∈ ℝ^m` with
`(y, 0)` in the chart target.

The surface measure of a `C¹` hypersurface parametrized by `Φ` is the pushforward of
`J_Φ(y) dy`, where the tangential Jacobian `J_Φ = √det(DΦᵀ DΦ)` is Mathlib's
`LinearMap.normDet` of the injective derivative `DΦ(y) : ℝ^m → ℝ^(m+1)`. We prove that
`Φᵢ` is `C¹` and injective with injective derivative on its parameter domain, so `J_{Φᵢ} > 0`
there, and define the chart surface measure as that pushforward. Two charts covering the same
boundary points are related by a `C¹` transition map in tangential coordinates; the
change-of-variables formula for parametrized area (from
`PDE.Analysis.MeasureTheory.ParametrizedArea`) shows the Jacobian-weighted integrals agree on
overlaps, so the chart measures restrict to the same measure on the common source. The Bochner
integral against a chart measure is then the usual Jacobian-weighted integral in the parameter
domain.

## Main results

* `chartBoundaryParametrization`, `image_chartBoundaryParametrization`: the parametrization and
  the fact that it covers exactly `(chartᵢ).source ∩ ∂Ω`.
* `chartBoundaryTransition`, `chartBoundaryTransition_left_inv`,
  `image_chartBoundaryTransitionDomain`: the `C¹` transition maps between overlapping charts.
* `chartBoundaryJacobian`, `chartBoundaryJacobian_pos`: the tangential Jacobian and its
  positivity on the parameter domain.
* `lintegral_chartBoundaryTransition`: Jacobian-weighted integrals are invariant under transitions.
* `chartBoundaryParameterMeasure`, `chartBoundaryMeasure`,
  `chartBoundaryMeasure_restrict_source`, `integral_chartBoundaryMeasure`: the chart surface
  measure, its compatibility on overlaps, and the change-of-variables formula.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, App. C.2, Theorem 1, pp. 711-712, where the surface measure
  `dS` on the boundary of a `C¹` domain enters the Gauss-Green theorem.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace
namespace Trace.C1

open Set
open MeasureTheory

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

open Boundary.Geometry.SurfaceMeasure

/-- Tangential parameters whose flat embedding lies in a chart target. -/
def chartBoundaryParameterDomain (i : Fin hΩ.N) : Set (ℝ^m) :=
  flatEmbedding ⁻¹' (hΩ.chart i).target

/-- The tangential parameter domain of a boundary chart is open. -/
theorem isOpen_chartBoundaryParameterDomain (i : Fin hΩ.N) :
    IsOpen (chartBoundaryParameterDomain (m := m) (Ω := Ω) i) :=
  (hΩ.chart i).open_target.preimage
    (isometry_flatEmbedding (n := m)).continuous

/-- Parametrization of a chart piece of the physical boundary. -/
def chartBoundaryParametrization (i : Fin hΩ.N) (y : ℝ^m) : ℝ^(m + 1) :=
  (hΩ.chart i).symm (flatEmbedding y)

/-- A boundary-chart parametrization is continuously differentiable. -/
theorem contDiff_chartBoundaryParametrization (i : Fin hΩ.N) :
    ContDiff ℝ 1 (chartBoundaryParametrization (m := m) (Ω := Ω) i) := by
  exact (hΩ.chart_symm_contDiff i).comp
    (flatEmbeddingContinuousLinearMap (n := m)).contDiff

/-- A boundary parametrization is injective on its parameter domain. -/
theorem chartBoundaryParametrization_injOn (i : Fin hΩ.N) :
    Set.InjOn (chartBoundaryParametrization (m := m) (Ω := Ω) i)
      (chartBoundaryParameterDomain (m := m) (Ω := Ω) i) := by
  intro y hy z hz heq
  let e := hΩ.chart i
  have hyTarget : flatEmbedding y ∈ e.target := hy
  have hzTarget : flatEmbedding z ∈ e.target := hz
  have hflat : flatEmbedding y = flatEmbedding z := by
    calc
      flatEmbedding y = e (e.symm (flatEmbedding y)) :=
        (e.right_inv hyTarget).symm
      _ = e (e.symm (flatEmbedding z)) := congrArg e heq
      _ = flatEmbedding z := e.right_inv hzTarget
  exact (isometry_flatEmbedding (n := m)).injective hflat

/-- The parametrized chart piece is exactly the physical boundary inside
the chart source. -/
theorem image_chartBoundaryParametrization (i : Fin hΩ.N) :
    chartBoundaryParametrization (m := m) (Ω := Ω) i ''
        chartBoundaryParameterDomain (m := m) (Ω := Ω) i =
      (hΩ.chart i).source ∩ frontier Ω := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyTarget : flatEmbedding y ∈ (hΩ.chart i).target := hy
    have hxSource := (hΩ.chart i).map_target hyTarget
    refine ⟨hxSource, (chart_mem_boundary_iff (n := m + 1) (Ω := Ω) i hxSource).1 ?_⟩
    rw [(hΩ.chart i).right_inv hyTarget]
    exact flatEmbedding_apply_last y
  · rintro ⟨hxSource, hxBoundary⟩
    let e := hΩ.chart i
    have hxFlat : e x ∈ HalfSpace.boundary (m + 1) :=
      (chart_mem_boundary_iff (n := m + 1) (Ω := Ω) i hxSource).2 hxBoundary
    have hflat : flatEmbedding (flatProjection (e x)) = e x := by
      apply flatEmbedding_flatProjection_of_last_eq_zero
      have hlast : PDE.Common.lastIndex (n := m + 1) = Fin.last m :=
        Fin.ext (by simp [PDE.Common.lastIndex])
      simpa [HalfSpace.boundary, hlast] using hxFlat
    refine ⟨flatProjection (e x), ?_, ?_⟩
    · change flatEmbedding _ ∈ e.target
      simpa [hflat] using e.map_source hxSource
    · change e.symm (flatEmbedding _) = x
      rw [hflat, e.left_inv hxSource]

/-- Parameters in chart `i` whose physical boundary points also lie in the
source of chart `j`. -/
def chartBoundaryTransitionDomain (i j : Fin hΩ.N) : Set (ℝ^m) :=
  chartBoundaryParameterDomain (m := m) (Ω := Ω) i ∩
    chartBoundaryParametrization (m := m) (Ω := Ω) i ⁻¹'
      (hΩ.chart j).source

/-- Boundary-chart transition map in tangential coordinates. -/
def chartBoundaryTransition (i j : Fin hΩ.N) (y : ℝ^m) : ℝ^m :=
  flatProjection <|
    hΩ.chart j
      (chartBoundaryParametrization (m := m) (Ω := Ω) i y)

/-- The parameter overlap of two boundary charts is open. -/
theorem isOpen_chartBoundaryTransitionDomain (i j : Fin hΩ.N) :
    IsOpen (chartBoundaryTransitionDomain (m := m) (Ω := Ω) i j) := by
  exact
    (isOpen_chartBoundaryParameterDomain (m := m) (Ω := Ω) i).inter <|
      (hΩ.chart j).open_source.preimage <|
        (contDiff_chartBoundaryParametrization
          (m := m) (Ω := Ω) i).continuous

/-- Boundary-chart transition maps are continuously differentiable. -/
theorem contDiff_chartBoundaryTransition (i j : Fin hΩ.N) :
    ContDiff ℝ 1 (chartBoundaryTransition (m := m) (Ω := Ω) i j) := by
  exact
    (flatProjectionContinuousLinearMap (n := m)).contDiff.comp <|
      (hΩ.chart_contDiff j).comp <|
        contDiff_chartBoundaryParametrization
          (m := m) (Ω := Ω) i

/-- On a chart overlap, re-embedding the transition coordinates recovers the
flattened boundary point in the second chart. -/
theorem flatEmbedding_chartBoundaryTransition
    (i j : Fin hΩ.N) {y : ℝ^m}
    (hy : y ∈ chartBoundaryTransitionDomain (m := m) (Ω := Ω) i j) :
    flatEmbedding
        (chartBoundaryTransition (m := m) (Ω := Ω) i j y) =
      hΩ.chart j
        (chartBoundaryParametrization (m := m) (Ω := Ω) i y) := by
  let x := chartBoundaryParametrization (m := m) (Ω := Ω) i y
  have hxBoundary : x ∈ frontier Ω := by
    have hxImage :
        x ∈
          chartBoundaryParametrization (m := m) (Ω := Ω) i ''
            chartBoundaryParameterDomain (m := m) (Ω := Ω) i :=
      ⟨y, hy.1, rfl⟩
    rw [image_chartBoundaryParametrization
      (m := m) (Ω := Ω) i] at hxImage
    exact hxImage.2
  have hxFlat :
      hΩ.chart j x ∈ HalfSpace.boundary (m + 1) :=
    (chart_mem_boundary_iff
      (n := m + 1) (Ω := Ω) j hy.2).2 hxBoundary
  have hlast :
      PDE.Common.lastIndex (n := m + 1) = Fin.last m := by
    apply Fin.ext
    simp [PDE.Common.lastIndex]
  apply flatEmbedding_flatProjection_of_last_eq_zero
  simpa [HalfSpace.boundary, hlast] using hxFlat

/-- A chart transition sends its overlap domain into the parameter domain of
the second chart. -/
theorem chartBoundaryTransition_mem_parameterDomain
    (i j : Fin hΩ.N) {y : ℝ^m}
    (hy : y ∈ chartBoundaryTransitionDomain (m := m) (Ω := Ω) i j) :
    chartBoundaryTransition (m := m) (Ω := Ω) i j y ∈
      chartBoundaryParameterDomain (m := m) (Ω := Ω) j := by
  change
    flatEmbedding
        (chartBoundaryTransition (m := m) (Ω := Ω) i j y) ∈
      (hΩ.chart j).target
  rw [flatEmbedding_chartBoundaryTransition
    (m := m) (Ω := Ω) i j hy]
  exact (hΩ.chart j).map_source hy.2

/-- Transitioning to chart `j` and applying its parametrization recovers the
original physical boundary point. -/
theorem chartBoundaryParametrization_transition
    (i j : Fin hΩ.N) {y : ℝ^m}
    (hy : y ∈ chartBoundaryTransitionDomain (m := m) (Ω := Ω) i j) :
    chartBoundaryParametrization (m := m) (Ω := Ω) j
        (chartBoundaryTransition (m := m) (Ω := Ω) i j y) =
      chartBoundaryParametrization (m := m) (Ω := Ω) i y := by
  rw [chartBoundaryParametrization,
    flatEmbedding_chartBoundaryTransition
      (m := m) (Ω := Ω) i j hy]
  exact (hΩ.chart j).left_inv hy.2

/-- A boundary-chart transition lands in the reverse overlap domain. -/
theorem chartBoundaryTransition_mem_transitionDomain
    (i j : Fin hΩ.N) {y : ℝ^m}
    (hy : y ∈ chartBoundaryTransitionDomain (m := m) (Ω := Ω) i j) :
    chartBoundaryTransition (m := m) (Ω := Ω) i j y ∈
      chartBoundaryTransitionDomain (m := m) (Ω := Ω) j i := by
  refine
    ⟨chartBoundaryTransition_mem_parameterDomain
      (m := m) (Ω := Ω) i j hy, ?_⟩
  change
    chartBoundaryParametrization (m := m) (Ω := Ω) j
        (chartBoundaryTransition (m := m) (Ω := Ω) i j y) ∈
      (hΩ.chart i).source
  rw [chartBoundaryParametrization_transition
    (m := m) (Ω := Ω) i j hy]
  exact (hΩ.chart i).map_target hy.1

/-- Swapping the two charts gives the inverse transition on the overlap. -/
theorem chartBoundaryTransition_left_inv
    (i j : Fin hΩ.N) {y : ℝ^m}
    (hy : y ∈ chartBoundaryTransitionDomain (m := m) (Ω := Ω) i j) :
    chartBoundaryTransition (m := m) (Ω := Ω) j i
        (chartBoundaryTransition (m := m) (Ω := Ω) i j y) = y := by
  apply
    (chartBoundaryParametrization_injOn
      (m := m) (Ω := Ω) i)
  · exact chartBoundaryTransition_mem_parameterDomain
      (m := m) (Ω := Ω) j i <|
        chartBoundaryTransition_mem_transitionDomain
          (m := m) (Ω := Ω) i j hy
  · exact hy.1
  rw [chartBoundaryParametrization_transition
    (m := m) (Ω := Ω) j i <|
      chartBoundaryTransition_mem_transitionDomain
        (m := m) (Ω := Ω) i j hy]
  exact chartBoundaryParametrization_transition
    (m := m) (Ω := Ω) i j hy

/-- A boundary-chart transition is injective on its overlap domain. -/
theorem chartBoundaryTransition_injOn (i j : Fin hΩ.N) :
    Set.InjOn
      (chartBoundaryTransition (m := m) (Ω := Ω) i j)
      (chartBoundaryTransitionDomain (m := m) (Ω := Ω) i j) := by
  intro y hy z hz hyz
  apply
    (chartBoundaryParametrization_injOn
      (m := m) (Ω := Ω) i) hy.1 hz.1
  calc
    chartBoundaryParametrization (m := m) (Ω := Ω) i y =
        chartBoundaryParametrization (m := m) (Ω := Ω) j
          (chartBoundaryTransition (m := m) (Ω := Ω) i j y) :=
      (chartBoundaryParametrization_transition
        (m := m) (Ω := Ω) i j hy).symm
    _ =
        chartBoundaryParametrization (m := m) (Ω := Ω) j
          (chartBoundaryTransition (m := m) (Ω := Ω) i j z) := by
      rw [hyz]
    _ = chartBoundaryParametrization (m := m) (Ω := Ω) i z :=
      chartBoundaryParametrization_transition
        (m := m) (Ω := Ω) i j hz

/-- The image of one overlap domain under the chart transition is exactly the
reverse overlap domain. -/
theorem image_chartBoundaryTransitionDomain (i j : Fin hΩ.N) :
    chartBoundaryTransition (m := m) (Ω := Ω) i j ''
        chartBoundaryTransitionDomain (m := m) (Ω := Ω) i j =
      chartBoundaryTransitionDomain (m := m) (Ω := Ω) j i := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact chartBoundaryTransition_mem_transitionDomain
      (m := m) (Ω := Ω) i j hy
  · intro hz
    refine
      ⟨chartBoundaryTransition (m := m) (Ω := Ω) j i z,
        chartBoundaryTransition_mem_transitionDomain
          (m := m) (Ω := Ω) j i hz, ?_⟩
    exact chartBoundaryTransition_left_inv
      (m := m) (Ω := Ω) j i hz

/-- Tangential derivative of a boundary parametrization. -/
noncomputable def chartBoundaryTangentialDerivative
    (i : Fin hΩ.N) (y : ℝ^m) : ℝ^m →L[ℝ] ℝ^(m + 1) :=
  (fderiv ℝ (fun z ↦ (hΩ.chart i).symm z) (flatEmbedding y)).comp
    (flatEmbeddingContinuousLinearMap (n := m))

/-- The tangential derivative varies continuously with the boundary
parameter. -/
theorem continuous_chartBoundaryTangentialDerivative
    (i : Fin hΩ.N) :
    Continuous
      (chartBoundaryTangentialDerivative (m := m) (Ω := Ω) i) := by
  have hderiv :
      Continuous
        (fun y : ℝ^m ↦
          fderiv ℝ (fun z ↦ (hΩ.chart i).symm z) (flatEmbedding y)) :=
    ((hΩ.chart_symm_contDiff i).continuous_fderiv one_ne_zero).comp
      (isometry_flatEmbedding (n := m)).continuous
  change Continuous fun y : ℝ^m ↦
    (fderiv ℝ (fun z ↦ (hΩ.chart i).symm z) (flatEmbedding y)).comp
      (flatEmbeddingContinuousLinearMap (n := m))
  exact
    hderiv.clm_comp
      (continuous_const :
        Continuous
          (fun _ : ℝ^m ↦
            flatEmbeddingContinuousLinearMap (n := m)))

/-- The derivative of the boundary parametrization is its tangential
derivative. -/
theorem fderiv_chartBoundaryParametrization
    (i : Fin hΩ.N) (y : ℝ^m) :
    fderiv ℝ (chartBoundaryParametrization (m := m) (Ω := Ω) i) y =
      chartBoundaryTangentialDerivative (m := m) (Ω := Ω) i y := by
  change
    fderiv ℝ
        ((fun z ↦ (hΩ.chart i).symm z) ∘
          (flatEmbeddingContinuousLinearMap (n := m))) y =
      _
  rw [fderiv_comp y
    ((hΩ.chart_symm_contDiff i).differentiable (by norm_num) _)
    (flatEmbeddingContinuousLinearMap (n := m)).differentiableAt]
  simp [chartBoundaryTangentialDerivative]

/-- On a chart overlap, differentiating after a transition gives the
derivative of the original parametrization. -/
theorem fderiv_chartBoundaryParametrization_comp_transition
    (i j : Fin hΩ.N) {y : ℝ^m}
    (hy : y ∈ chartBoundaryTransitionDomain (m := m) (Ω := Ω) i j) :
    fderiv ℝ
        (chartBoundaryParametrization (m := m) (Ω := Ω) j ∘
          chartBoundaryTransition (m := m) (Ω := Ω) i j) y =
      fderiv ℝ
        (chartBoundaryParametrization (m := m) (Ω := Ω) i) y := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [
    (isOpen_chartBoundaryTransitionDomain
      (m := m) (Ω := Ω) i j).mem_nhds hy
  ] with z hz
  simpa only [Function.comp_apply] using
    chartBoundaryParametrization_transition
      (m := m) (Ω := Ω) i j hz

/-- The tangential derivative is injective on the chart parameter domain. -/
theorem chartBoundaryTangentialDerivative_injective
    (i : Fin hΩ.N) {y : ℝ^m}
    (hy : y ∈ chartBoundaryParameterDomain (m := m) (Ω := Ω) i) :
    Function.Injective
      (chartBoundaryTangentialDerivative (m := m) (Ω := Ω) i y) := by
  intro v w hvw
  let e := hΩ.chart i
  have hyTarget : flatEmbedding y ∈ e.target := hy
  have hinv := congrArg
    (fun A : ℝ^(m + 1) →L[ℝ] ℝ^(m + 1) ↦ A (flatEmbeddingContinuousLinearMap (n := m) (v - w)))
    (fderiv_chart_comp_fderiv_chart_symm (n := m + 1) (Ω := Ω) i (e.map_target hyTarget))
  have hderiv : chartBoundaryTangentialDerivative (m := m) (Ω := Ω) i y (v - w) = 0 := by
    simpa using sub_eq_zero.mpr hvw
  have hflat : flatEmbedding (n := m) (v - w) = 0 := by
    calc flatEmbedding (n := m) (v - w)
        = (fderiv ℝ (fun z ↦ e z) (e.symm (flatEmbedding y)))
          (chartBoundaryTangentialDerivative (m := m) (Ω := Ω) i y (v - w)) := by
          simpa [chartBoundaryTangentialDerivative, e, e.right_inv hyTarget] using hinv.symm
      _ = 0 := by rw [hderiv, map_zero]
  exact sub_eq_zero.mp ((isometry_flatEmbedding (n := m)).injective
    (hflat.trans (map_zero (flatEmbeddingContinuousLinearMap (n := m))).symm))

/-- Tangential surface Jacobian of a boundary parametrization. -/
noncomputable def chartBoundaryJacobian
    (i : Fin hΩ.N) (y : ℝ^m) : ℝ :=
  (chartBoundaryTangentialDerivative
    (m := m) (Ω := Ω) i y).toLinearMap.normDet

/-- The tangential surface Jacobian varies continuously with the boundary
parameter. -/
theorem continuous_chartBoundaryJacobian (i : Fin hΩ.N) :
    Continuous (chartBoundaryJacobian (m := m) (Ω := Ω) i) := by
  let b : OrthonormalBasis (Fin m) ℝ (ℝ^m) :=
    (stdOrthonormalBasis ℝ (ℝ^m)).reindex (finCongr finrank_euclideanSpace_fin)
  let D := chartBoundaryTangentialDerivative (m := m) (Ω := Ω) i
  have hD : Continuous D := continuous_chartBoundaryTangentialDerivative (m := m) (Ω := Ω) i
  have hgram : Continuous fun y ↦ Matrix.gram ℝ (fun j : Fin m ↦ (D y).toLinearMap (b j)) :=
    continuous_pi fun p ↦ continuous_pi fun q ↦ by
      simpa [Matrix.gram] using (hD.clm_apply continuous_const).inner
        (hD.clm_apply continuous_const : Continuous (fun y ↦ D y (b q)))
  convert Real.continuous_sqrt.comp hgram.matrix_det using 1
  funext y
  rw [Function.comp_apply, ← (D y).toLinearMap.normDet_sq_eq_det_gram b]
  exact (Real.sqrt_sq (D y).toLinearMap.normDet_nonneg).symm

/-- Jacobian-weighted boundary integrals agree under a transition between
two overlapping charts. -/
theorem lintegral_chartBoundaryTransition
    (i j : Fin hΩ.N) (g : ℝ^(m + 1) → ENNReal) :
    ∫⁻ z in chartBoundaryTransitionDomain (m := m) (Ω := Ω) j i,
        ENNReal.ofReal
            (chartBoundaryJacobian (m := m) (Ω := Ω) j z) *
          g (chartBoundaryParametrization (m := m) (Ω := Ω) j z)
          ∂volume =
      ∫⁻ y in chartBoundaryTransitionDomain (m := m) (Ω := Ω) i j,
        ENNReal.ofReal
            (chartBoundaryJacobian (m := m) (Ω := Ω) i y) *
          g (chartBoundaryParametrization (m := m) (Ω := Ω) i y)
          ∂volume := by
  have hchange := lintegral_image_eq_lintegral_normDet_fderiv_comp
    (isOpen_chartBoundaryTransitionDomain (m := m) (Ω := Ω) i j).measurableSet
    ((contDiff_chartBoundaryTransition (m := m) (Ω := Ω) i j).differentiable (by norm_num))
    (chartBoundaryTransition_injOn (m := m) (Ω := Ω) i j)
    ((contDiff_chartBoundaryParametrization (m := m) (Ω := Ω) j).differentiable (by norm_num)) g
  rw [image_chartBoundaryTransitionDomain (m := m) (Ω := Ω) i j] at hchange
  refine (setLIntegral_congr_fun (isOpen_chartBoundaryTransitionDomain (m := m) (Ω := Ω) j
    i).measurableSet fun z _ ↦ ?_).trans (hchange.trans (setLIntegral_congr_fun
      (isOpen_chartBoundaryTransitionDomain (m := m) (Ω := Ω) i j).measurableSet fun y hy ↦ ?_))
  · rw [fderiv_chartBoundaryParametrization]
    rfl
  · rw [fderiv_chartBoundaryParametrization_comp_transition (m := m) (Ω := Ω) i j hy,
      fderiv_chartBoundaryParametrization, Function.comp_apply,
      chartBoundaryParametrization_transition (m := m) (Ω := Ω) i j hy]
    rfl

/-- The tangential surface Jacobian is strictly positive on the chart
parameter domain. -/
theorem chartBoundaryJacobian_pos
    (i : Fin hΩ.N) {y : ℝ^m}
    (hy : y ∈ chartBoundaryParameterDomain (m := m) (Ω := Ω) i) :
    0 < chartBoundaryJacobian (m := m) (Ω := Ω) i y := by
  let f :=
    (chartBoundaryTangentialDerivative
      (m := m) (Ω := Ω) i y).toLinearMap
  have hinj : Function.Injective f :=
    chartBoundaryTangentialDerivative_injective
      (m := m) (Ω := Ω) i hy
  have hker : f.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hne : f.normDet ≠ 0 := by
    intro hzero
    exact (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp hzero) hker
  exact lt_of_le_of_ne f.normDet_nonneg (Ne.symm hne)

/-- The Jacobian-weighted Lebesgue measure on the flat parameter domain of a
boundary chart. -/
noncomputable def chartBoundaryParameterMeasure
    (i : Fin hΩ.N) : Measure (ℝ^m) :=
  ((volume : Measure (ℝ^m)).restrict
      (chartBoundaryParameterDomain (m := m) (Ω := Ω) i)).withDensity
    (fun y ↦
      ENNReal.ofReal
        (chartBoundaryJacobian (m := m) (Ω := Ω) i y))

/-- Integration against the chart parameter measure is precisely
Jacobian-weighted integration over the flat parameter domain. -/
theorem integral_chartBoundaryParameterMeasure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin hΩ.N) (g : ℝ^m → E) :
    ∫ y, g y ∂chartBoundaryParameterMeasure (m := m) (Ω := Ω) i =
      ∫ y in chartBoundaryParameterDomain (m := m) (Ω := Ω) i,
        chartBoundaryJacobian (m := m) (Ω := Ω) i y • g y := by
  rw [chartBoundaryParameterMeasure,
    integral_withDensity_eq_integral_toReal_smul₀]
  · congr 1
    funext y
    rw [ENNReal.toReal_ofReal]
    exact LinearMap.normDet_nonneg _
  · exact
      (continuous_chartBoundaryJacobian
        (m := m) (Ω := Ω) i).measurable.ennreal_ofReal.aemeasurable
  · filter_upwards
    intro y
    exact ENNReal.ofReal_lt_top

/-- Surface measure on one physical boundary-chart piece, defined as the
pushforward of the Jacobian-weighted parameter measure. -/
noncomputable def chartBoundaryMeasure
    (i : Fin hΩ.N) : Measure (ℝ^(m + 1)) :=
  Measure.map
    (chartBoundaryParametrization (m := m) (Ω := Ω) i)
    (chartBoundaryParameterMeasure (m := m) (Ω := Ω) i)

/-- Integrating against a chart measure on another chart's source is the
Jacobian-weighted integral over the parameter overlap. -/
theorem lintegral_chartBoundaryMeasure_restrict_source
    (i j : Fin hΩ.N) {g : ℝ^(m + 1) → ENNReal} (hg : Measurable g) :
    ∫⁻ x, g x
        ∂((chartBoundaryMeasure (m := m) (Ω := Ω) i).restrict
          (hΩ.chart j).source) =
      ∫⁻ y in chartBoundaryTransitionDomain (m := m) (Ω := Ω) i j,
        ENNReal.ofReal
            (chartBoundaryJacobian (m := m) (Ω := Ω) i y) *
          g (chartBoundaryParametrization (m := m) (Ω := Ω) i y)
          ∂volume := by
  have hφ := (contDiff_chartBoundaryParametrization (m := m) (Ω := Ω) i).continuous.measurable
  rw [chartBoundaryMeasure, setLIntegral_map (hΩ.chart j).open_source.measurableSet hg hφ,
    chartBoundaryParameterMeasure, setLIntegral_withDensity_eq_setLIntegral_mul _
      (continuous_chartBoundaryJacobian (m := m) (Ω := Ω) i).measurable.ennreal_ofReal
      (g := fun y ↦ g (chartBoundaryParametrization (m := m) (Ω := Ω) i y)) (hg.comp hφ)
      (hφ (hΩ.chart j).open_source.measurableSet),
    Measure.restrict_restrict (hφ (hΩ.chart j).open_source.measurableSet)]
  simp only [chartBoundaryTransitionDomain, Pi.mul_apply]
  rw [inter_comm]

/-- Surface measures defined in two boundary charts agree on their physical
overlap. -/
theorem chartBoundaryMeasure_restrict_source (i j : Fin hΩ.N) :
    (chartBoundaryMeasure (m := m) (Ω := Ω) i).restrict
        (hΩ.chart j).source =
      (chartBoundaryMeasure (m := m) (Ω := Ω) j).restrict
        (hΩ.chart i).source := by
  refine Measure.ext fun s hs ↦ ?_
  have hg : Measurable (s.indicator fun _ ↦ (1 : ENNReal)) := measurable_const.indicator hs
  have h := (lintegral_chartBoundaryMeasure_restrict_source (m := m) (Ω := Ω) i j hg).trans
    ((lintegral_chartBoundaryTransition (m := m) (Ω := Ω) i j _).symm.trans
      (lintegral_chartBoundaryMeasure_restrict_source (m := m) (Ω := Ω) j i hg).symm)
  simpa [lintegral_indicator_const hs] using h

/-- The chart surface measure satisfies the expected parametrized Bochner
integral formula. -/
theorem integral_chartBoundaryMeasure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin hΩ.N) (f : ℝ^(m + 1) → E)
    (hf :
      AEStronglyMeasurable f
        (chartBoundaryMeasure (m := m) (Ω := Ω) i)) :
    ∫ x, f x ∂chartBoundaryMeasure (m := m) (Ω := Ω) i =
      ∫ y in chartBoundaryParameterDomain (m := m) (Ω := Ω) i,
        chartBoundaryJacobian (m := m) (Ω := Ω) i y •
          f (chartBoundaryParametrization (m := m) (Ω := Ω) i y) := by
  rw [chartBoundaryMeasure,
    MeasureTheory.integral_map
      (contDiff_chartBoundaryParametrization
        (m := m) (Ω := Ω) i).continuous.measurable.aemeasurable hf]
  exact
    integral_chartBoundaryParameterMeasure
      (m := m) (Ω := Ω) i
      (fun y ↦
        f (chartBoundaryParametrization (m := m) (Ω := Ω) i y))

end Trace.C1
end SobolevSpace
