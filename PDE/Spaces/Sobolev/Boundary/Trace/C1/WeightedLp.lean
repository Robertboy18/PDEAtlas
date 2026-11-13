/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.WithDensity
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.MeasureClass

/-!
# Weighted `Lᵖ` coordinates on an operational `C¹` boundary

The intrinsic surface measure and the boundary-atlas measure are mutually
absolutely continuous. Their Radon-Nikodym densities therefore give
canonical isometric changes of coordinates between the corresponding
finite-exponent `Lᵖ` spaces.
-/

@[expose] public section

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace
namespace Trace.C1

open MeasureTheory
open scoped ENNReal

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- Intrinsic surface `Lᵖ` and boundary-atlas `Lᵖ` are canonically linearly
isometric through Radon-Nikodym density-root rescaling. -/
noncomputable def surfaceLpEquivAtlasLp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p) :
    Lp E (ENNReal.ofReal p)
        (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω) ≃ₗᵢ[ℝ]
      Lp E (ENNReal.ofReal p)
        (atlasBoundaryMeasure (m := m) (Ω := Ω)) :=
  MeasureTheory.Lp.withDensityRootLIEOfEq
    (measurable_surfaceMeasureDensity (m := m) (Ω := Ω))
    (surfaceMeasureDensity_pos_ae (m := m) (Ω := Ω))
    (surfaceMeasureDensity_lt_top_ae (m := m) (Ω := Ω))
    (atlasBoundaryMeasure_withDensity_surfaceMeasureDensity
      (m := m) (Ω := Ω)) hp

/-- A representative of `surfaceLpEquivAtlasLp` is multiplied by the
intrinsic-to-atlas density root. -/
theorem surfaceLpEquivAtlasLp_apply_ae
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p)
    (f : Lp E (ENNReal.ofReal p)
      (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω)) :
    (surfaceLpEquivAtlasLp (m := m) (Ω := Ω) p hp f :
        ℝ^(m + 1) → E) =ᵐ[
      atlasBoundaryMeasure (m := m) (Ω := Ω)]
      fun x ↦
        MeasureTheory.Lp.withDensityRoot
          (surfaceMeasureDensity (m := m) (Ω := Ω)) p x • f x :=
  MeasureTheory.Lp.withDensityRootLIEOfEq_apply_ae
    (measurable_surfaceMeasureDensity (m := m) (Ω := Ω))
    (surfaceMeasureDensity_pos_ae (m := m) (Ω := Ω))
    (surfaceMeasureDensity_lt_top_ae (m := m) (Ω := Ω))
    (atlasBoundaryMeasure_withDensity_surfaceMeasureDensity
      (m := m) (Ω := Ω)) hp f

/-- A representative of the inverse of `surfaceLpEquivAtlasLp` is multiplied
by the reciprocal intrinsic-to-atlas density root. -/
theorem surfaceLpEquivAtlasLp_symm_apply_ae
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p)
    (f : Lp E (ENNReal.ofReal p)
      (atlasBoundaryMeasure (m := m) (Ω := Ω))) :
    ((surfaceLpEquivAtlasLp (m := m) (Ω := Ω) p hp).symm f :
        ℝ^(m + 1) → E) =ᵐ[
      Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω]
      fun x ↦
        (MeasureTheory.Lp.withDensityRoot
          (surfaceMeasureDensity (m := m) (Ω := Ω)) p x)⁻¹ • f x :=
  MeasureTheory.Lp.withDensityRootLIEOfEq_symm_apply_ae
    (measurable_surfaceMeasureDensity (m := m) (Ω := Ω))
    (surfaceMeasureDensity_pos_ae (m := m) (Ω := Ω))
    (surfaceMeasureDensity_lt_top_ae (m := m) (Ω := Ω))
    (atlasBoundaryMeasure_withDensity_surfaceMeasureDensity
      (m := m) (Ω := Ω)) hp f

end Trace.C1
end SobolevSpace
