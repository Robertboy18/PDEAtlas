/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.IndicatorExtension
public import PDE.Spaces.Sobolev.Boundary.Atlas.Definitions
public import PDE.Spaces.Sobolev.Boundary.Geometry.SurfaceMeasure
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Geometry

/-!
# Transport from flat to physical boundary coordinates

We isolate the measure-theoretic transport used to globalize flat trace theorems on an
operational `C¹` domain. A flat trace produces an `Lᵖ` function on the hyperplane
`{xₙ = 0}` with respect to `flatSurfaceMeasure`; the physical trace must be an `Lᵖ` function on
`∂Ω` with respect to intrinsic surface measure. For each boundary chart the transport

1. changes from flat surface measure to the pushforward of intrinsic surface measure on the
   chart's boundary patch, which is dominated by a finite multiple of flat surface measure
   because the inverse chart is Lipschitz;
2. pulls the function back through the chart, which is measure preserving from the restricted
   surface measure to its pushforward;
3. extends the resulting function by zero off the physical chart patch.

Each step is a bounded linear map between `Lᵖ` spaces, and the composite `chartPhysicalization`
has norm at most `c^{1/p}` where `c` is the surface-measure distortion constant of the chart.
The construction works for every real normed target and `1 ≤ p ≤ ∞`; completeness
and finite-dimensionality of the target are not needed.

## Main results

* `exists_chart_surface_pushforward_le`, `chartSurfaceBound`, `chartPushedSurfaceMeasure_le`:
  the pushed-forward surface measure is bounded by a finite multiple of flat surface measure.
* `chartBoundaryPatch`, `measurePreserving_chart_boundaryPatch`: the physical boundary patch and
  the chart as a measure-preserving map on it.
* `chartPhysicalization`, `chartPhysicalization_apply_ae`, `norm_chartPhysicalization_apply_le`:
  the transport operator, its representative formula, and its norm bound.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.5, Theorem 1, step 2 of the proof, p. 272, where the flat
  estimate is transported to a curved boundary piece by a change of variables.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace
namespace Trace.C1

open MeasureTheory Set
open scoped NNReal ENNReal

/-- Surface measure on a physical boundary patch, pushed forward by its
flattening chart, is dominated by a finite multiple of flat surface measure. -/
theorem exists_chart_surface_pushforward_le
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (i : Fin hΩ.N) :
    ∃ c : ℝ≥0∞, c < ∞ ∧
      Measure.map (hΩ.chart i)
          ((Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω).restrict
            ((hΩ.chart i).source ∩ frontier Ω)) ≤
        c • Boundary.Geometry.SurfaceMeasure.flatSurfaceMeasure (n := m) := by
  let A : Set (ℝ^(m + 1)) := (hΩ.chart i).source ∩ frontier Ω
  let B : Set (ℝ^(m + 1)) :=
    (hΩ.chart i).target ∩ HalfSpace.boundary (m + 1)
  obtain ⟨C, hC⟩ := exists_chart_symm_surfaceMeasure_image_le
    (n := m + 1) (Ω := Ω) i
  let c : ℝ≥0∞ := (C : ℝ≥0∞) ^ (m : ℝ)
  have hcTop : c < ∞ := by
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.coe_ne_top
  refine ⟨c, hcTop, Measure.le_iff.2 fun t ht ↦ ?_⟩
  have hchartMeas : Measurable (hΩ.chart i : ℝ^(m + 1) → ℝ^(m + 1)) :=
    (hΩ.chart_contDiff i).continuous.measurable
  have hAmeas : MeasurableSet A :=
    (hΩ.chart i).open_source.measurableSet.inter isClosed_frontier.measurableSet
  have hpreMeas : MeasurableSet ((hΩ.chart i) ⁻¹' t) :=
    hchartMeas ht
  have hrestrict :
      (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω).restrict A =
        (Measure.euclideanHausdorffMeasure m).restrict A := by
    rw [Boundary.Geometry.SurfaceMeasure.surfaceMeasure, Measure.restrict_restrict hAmeas]
    congr 1
    simp only [A]
    ext x
    simp [and_left_comm, and_comm]
  have hset :
      (hΩ.chart i) ⁻¹' t ∩ A = (hΩ.chart i).symm '' (t ∩ B) := by
    ext x
    constructor
    · rintro ⟨hxt, hxSource, hxBoundary⟩
      let y := hΩ.chart i x
      have hyTarget : y ∈ (hΩ.chart i).target :=
        (hΩ.chart i).map_source hxSource
      have hyBoundary : y ∈ HalfSpace.boundary (m + 1) :=
        (chart_mem_boundary_iff (n := m + 1) (Ω := Ω) i hxSource).2 hxBoundary
      refine ⟨y, ⟨hxt, hyTarget, hyBoundary⟩, ?_⟩
      exact (hΩ.chart i).left_inv hxSource
    · rintro ⟨y, ⟨hyt, hyTarget, hyBoundary⟩, rfl⟩
      have hxSource : (hΩ.chart i).symm y ∈ (hΩ.chart i).source :=
        (hΩ.chart i).map_target hyTarget
      have hright := (hΩ.chart i).right_inv hyTarget
      have hxBoundary : (hΩ.chart i).symm y ∈ frontier Ω :=
        (chart_mem_boundary_iff (n := m + 1) (Ω := Ω) i hxSource).1
          (by simpa [hright] using hyBoundary)
      exact ⟨by simpa [hright] using hyt, hxSource, hxBoundary⟩
  have hBTarget : t ∩ B ⊆ (hΩ.chart i).target := by
    intro x hx
    exact hx.2.1
  have hdist := hC (t ∩ B) hBTarget
  have hlast : PDE.Common.lastIndex (n := m + 1) = Fin.last m := by
    apply Fin.ext
    simp [PDE.Common.lastIndex]
  have hBFlat : B ⊆ {x : ℝ^(m + 1) | x (Fin.last m) = 0} := by
    intro x hx
    simpa [B, HalfSpace.boundary, hlast] using hx.2
  have hflatMono :
      Measure.euclideanHausdorffMeasure m (t ∩ B) ≤
        Boundary.Geometry.SurfaceMeasure.flatSurfaceMeasure (n := m) t := by
    rw [Boundary.Geometry.SurfaceMeasure.flatSurfaceMeasure, Measure.restrict_apply ht]
    apply measure_mono
    intro x hx
    exact ⟨hx.1, hBFlat hx.2⟩
  rw [Measure.map_apply hchartMeas ht, hrestrict,
    Measure.restrict_apply hpreMeas, hset]
  simp only [Measure.smul_apply]
  exact hdist.trans (mul_le_mul_right hflatMono c)

/-- The physical portion of the boundary covered by one chart. -/
def chartBoundaryPatch
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (i : Fin hΩ.N) : Set (ℝ^(m + 1)) :=
  (hΩ.chart i).source ∩ frontier Ω

/-- A physical chart boundary patch is measurable. -/
theorem measurableSet_chartBoundaryPatch
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (i : Fin hΩ.N) :
    MeasurableSet (chartBoundaryPatch (m := m) (Ω := Ω) i) :=
  (hΩ.chart i).open_source.measurableSet.inter isClosed_frontier.measurableSet

/-- Surface measure of a chart patch, pushed to flattened coordinates. -/
noncomputable def chartPushedSurfaceMeasure
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (i : Fin hΩ.N) : Measure (ℝ^(m + 1)) :=
  Measure.map (hΩ.chart i)
    ((Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω).restrict
      (chartBoundaryPatch (m := m) (Ω := Ω) i))

/-- On one boundary patch, the chart preserves the restricted surface measure
and its pushforward by definition. -/
theorem measurePreserving_chart_boundaryPatch
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (i : Fin hΩ.N) :
    MeasurePreserving (hΩ.chart i)
      ((Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω).restrict
        (chartBoundaryPatch (m := m) (Ω := Ω) i))
      (chartPushedSurfaceMeasure (m := m) (Ω := Ω) i) := by
  refine ⟨(hΩ.chart_contDiff i).continuous.measurable, ?_⟩
  rfl

/-- The pushed-forward chart surface measure is bounded by a finite `ℝ≥0` multiple
of flat surface measure. -/
theorem exists_chart_surface_pushforward_le_nnreal
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (i : Fin hΩ.N) :
    ∃ k : ℝ≥0,
      chartPushedSurfaceMeasure (m := m) (Ω := Ω) i ≤
        (k : ℝ≥0∞) • Boundary.Geometry.SurfaceMeasure.flatSurfaceMeasure (n := m) := by
  obtain ⟨c, hc, hle⟩ := exists_chart_surface_pushforward_le
    (m := m) (Ω := Ω) i
  let k : ℝ≥0 := c.toNNReal
  refine ⟨k, ?_⟩
  simpa [chartPushedSurfaceMeasure, chartBoundaryPatch, k,
    ENNReal.coe_toNNReal hc.ne] using hle

/-- A finite distortion constant for one boundary chart. -/
noncomputable def chartSurfaceBound
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (i : Fin hΩ.N) : ℝ≥0 :=
  Classical.choose
    (exists_chart_surface_pushforward_le_nnreal
      (m := m) (Ω := Ω) i)

/-- The pushed-forward chart surface measure is controlled by flat surface
measure with the chosen finite distortion constant. -/
theorem chartPushedSurfaceMeasure_le
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (i : Fin hΩ.N) :
    chartPushedSurfaceMeasure (m := m) (Ω := Ω) i ≤
      (chartSurfaceBound (m := m) (Ω := Ω) i : ℝ≥0∞) •
        Boundary.Geometry.SurfaceMeasure.flatSurfaceMeasure (n := m) :=
  Classical.choose_spec
    (exists_chart_surface_pushforward_le_nnreal
      (m := m) (Ω := Ω) i)

/-- Transport flat `Lᵖ` boundary data to one physical chart patch, extending
the result by zero outside the patch. -/
noncomputable def chartPhysicalization
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : Fin hΩ.N) :
    MeasureTheory.Lp F p
        (Boundary.Geometry.SurfaceMeasure.flatSurfaceMeasure (n := m)) →L[ℝ]
      MeasureTheory.Lp F p
        (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω) :=
  (MeasureTheory.Lp.extendByZeroₗᵢ (𝕜 := ℝ)
      (measurableSet_chartBoundaryPatch (m := m) (Ω := Ω) i)).toContinuousLinearMap.comp
    ((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ (hΩ.chart i)
      (measurePreserving_chart_boundaryPatch
        (m := m) (Ω := Ω) i)).toContinuousLinearMap.comp
      (MeasureTheory.Lp.LpToLpOfMeasureLeSMul
        (p := p) (E := F) ENNReal.coe_ne_top
        (chartPushedSurfaceMeasure_le (m := m) (Ω := Ω) i)))

/-- A representative of chart physicalization is chart pullback on the
physical patch and zero off that patch. -/
theorem chartPhysicalization_apply_ae
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : Fin hΩ.N)
    (g : MeasureTheory.Lp F p
      (Boundary.Geometry.SurfaceMeasure.flatSurfaceMeasure (n := m))) :
    (chartPhysicalization (m := m) (Ω := Ω) p i g :
      ℝ^(m + 1) → F) =ᵐ[
        Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω]
      (chartBoundaryPatch (m := m) (Ω := Ω) i).indicator
        (fun x ↦ g (hΩ.chart i x)) := by
  let A := chartBoundaryPatch (m := m) (Ω := Ω) i
  let μ := Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω
  let ρ := chartPushedSurfaceMeasure (m := m) (Ω := Ω) i
  let ν := Boundary.Geometry.SurfaceMeasure.flatSurfaceMeasure (n := m)
  let D : MeasureTheory.Lp F p ν →L[ℝ] MeasureTheory.Lp F p ρ :=
    MeasureTheory.Lp.LpToLpOfMeasureLeSMul
      (p := p) (E := F) ENNReal.coe_ne_top
      (chartPushedSurfaceMeasure_le (m := m) (Ω := Ω) i)
  let C : MeasureTheory.Lp F p ρ →ₗᵢ[ℝ]
      MeasureTheory.Lp F p (μ.restrict A) :=
    MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ (hΩ.chart i)
      (measurePreserving_chart_boundaryPatch
        (m := m) (Ω := Ω) i)
  have hD : (D g : ℝ^(m + 1) → F) =ᵐ[ρ] g :=
    MeasureTheory.Lp.coeFn_LpToLpOfMeasureLeSMul
      ENNReal.coe_ne_top
      (chartPushedSurfaceMeasure_le (m := m) (Ω := Ω) i) g
  have hC : (C (D g) : ℝ^(m + 1) → F) =ᵐ[μ.restrict A]
      fun x ↦ D g (hΩ.chart i x) := by
    simpa [C, Function.comp_def] using
      MeasureTheory.Lp.coeFn_compMeasurePreserving (D g)
        (measurePreserving_chart_boundaryPatch
          (m := m) (Ω := Ω) i)
  have hDcomp : (fun x ↦ D g (hΩ.chart i x)) =ᵐ[μ.restrict A]
      fun x ↦ g (hΩ.chart i x) := by
    exact (measurePreserving_chart_boundaryPatch
      (m := m) (Ω := Ω) i).quasiMeasurePreserving.ae hD
  have hpullback : (C (D g) : ℝ^(m + 1) → F) =ᵐ[μ.restrict A]
      fun x ↦ g (hΩ.chart i x) :=
    hC.trans hDcomp
  have hindicator :
      A.indicator (fun x ↦ C (D g) x) =ᵐ[μ]
        A.indicator (fun x ↦ g (hΩ.chart i x)) :=
    (ae_eq_restrict_iff_indicator_ae_eq
      (measurableSet_chartBoundaryPatch (m := m) (Ω := Ω) i)).mp hpullback
  have hzero :
      (MeasureTheory.Lp.extendByZeroₗᵢ (𝕜 := ℝ)
          (measurableSet_chartBoundaryPatch (m := m) (Ω := Ω) i)
          (C (D g)) : ℝ^(m + 1) → F) =ᵐ[μ]
        A.indicator (fun x ↦ C (D g) x) :=
    MeasureTheory.Lp.extendByZeroₗᵢ_apply_ae
      (measurableSet_chartBoundaryPatch (m := m) (Ω := Ω) i) (C (D g))
  simpa [chartPhysicalization, A, μ, ρ, ν, D, C] using
    hzero.trans hindicator

/-- The chart physicalization norm is controlled solely by the
surface-measure distortion of the chart. -/
theorem norm_chartPhysicalization_apply_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : Fin hΩ.N)
    (g : MeasureTheory.Lp F p
      (Boundary.Geometry.SurfaceMeasure.flatSurfaceMeasure (n := m))) :
    ‖chartPhysicalization (m := m) (Ω := Ω) p i g‖ ≤
      (chartSurfaceBound (m := m) (Ω := Ω) i : ℝ) ^
          (1 / p).toReal * ‖g‖ := by
  let D := MeasureTheory.Lp.LpToLpOfMeasureLeSMul
    (p := p) (E := F) ENNReal.coe_ne_top
    (chartPushedSurfaceMeasure_le (m := m) (Ω := Ω) i)
  calc
    ‖chartPhysicalization (m := m) (Ω := Ω) p i g‖ = ‖D g‖ := by
      simp [chartPhysicalization, D]
    _ ≤ ‖D‖ * ‖g‖ := D.le_opNorm g
    _ ≤ (chartSurfaceBound (m := m) (Ω := Ω) i : ℝ) ^
          (1 / p).toReal * ‖g‖ := by
      gcongr
      simpa using
        (MeasureTheory.Lp.norm_LpToLpOfMeasureLeSMul_le
          (p := p) (E := F) ENNReal.coe_ne_top
          (chartPushedSurfaceMeasure_le (m := m) (Ω := Ω) i))

end Trace.C1
end SobolevSpace
