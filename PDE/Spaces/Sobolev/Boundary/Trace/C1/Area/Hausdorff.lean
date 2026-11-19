/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.AtlasMeasure
import PDE.Analysis.MeasureTheory.AreaFormula.C1

/-!
# Hausdorff measure in C¹ boundary charts

The C¹ area formula identifies each chart measure with the restriction of
codimension-one Euclidean Hausdorff measure. Consequently the finite measure
assembled from any operational boundary atlas is exactly `surfaceMeasure Ω`.
The equality preserves signed Bochner integrals and is valid also for the
zero-dimensional parameter domains of one-dimensional boundaries.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace
namespace Trace.C1

open Set MeasureTheory Boundary.Geometry.SurfaceMeasure

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- A chart's parametrized area measure is Hausdorff surface measure
restricted to that chart source. -/
theorem chartBoundaryMeasure_eq_surfaceMeasure_restrict (i : Fin hΩ.N) :
    chartBoundaryMeasure (m := m) (Ω := Ω) i =
      (surfaceMeasure Ω).restrict (hΩ.chart i).source := by
  have hderiv : ∀ y ∈ chartBoundaryParameterDomain (m := m) (Ω := Ω) i,
      Function.Injective
        (fderiv ℝ (chartBoundaryParametrization (m := m) (Ω := Ω) i) y) := by
    intro y hy
    rw [fderiv_chartBoundaryParametrization]
    exact chartBoundaryTangentialDerivative_injective i hy
  have h := map_withDensity_normDet_fderiv_eq_euclideanHausdorffMeasure
    (isOpen_chartBoundaryParameterDomain (m := m) (Ω := Ω) i)
    (contDiff_chartBoundaryParametrization (m := m) (Ω := Ω) i).contDiffOn
    (chartBoundaryParametrization_injOn (m := m) (Ω := Ω) i) hderiv
  simpa only [chartBoundaryMeasure, chartBoundaryParameterMeasure, chartBoundaryJacobian,
    fderiv_chartBoundaryParametrization, finrank_euclideanSpace_fin,
    image_chartBoundaryParametrization, surfaceMeasure, Nat.add_sub_cancel,
    Measure.restrict_restrict (hΩ.chart i).open_source.measurableSet] using h

/-- The globally assembled chart measure equals Hausdorff surface measure. -/
theorem atlasBoundaryMeasure_eq_surfaceMeasure :
    atlasBoundaryMeasure (m := m) (Ω := Ω) = surfaceMeasure Ω :=
  atlasBoundaryMeasure_eq_surfaceMeasure_iff.mpr
    (fun i ↦ (chartBoundaryMeasure_eq_surfaceMeasure_restrict i).symm)

/-- Signed surface integrals on a chart are exactly the tangential
Jacobian-weighted parameter integrals. -/
theorem integral_surfaceMeasure_restrict_chartSource
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (i : Fin hΩ.N) (g : ℝ^(m + 1) → G)
    (hg : AEStronglyMeasurable g ((surfaceMeasure Ω).restrict (hΩ.chart i).source)) :
    ∫ x in (hΩ.chart i).source, g x ∂surfaceMeasure Ω =
      ∫ y in chartBoundaryParameterDomain (m := m) (Ω := Ω) i,
        chartBoundaryJacobian (m := m) (Ω := Ω) i y •
          g (chartBoundaryParametrization (m := m) (Ω := Ω) i y) := by
  rw [← chartBoundaryMeasure_eq_surfaceMeasure_restrict i] at hg ⊢
  exact integral_chartBoundaryMeasure i g hg

end Trace.C1
end SobolevSpace
