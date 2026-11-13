/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.FiniteExponentOperator
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.WeightedLp

/-!
# Finite-exponent trace in boundary-atlas coordinates

For `1 ≤ p`, the intrinsic finite-exponent trace can be expressed isometrically
using the operational boundary-atlas measure. This is the form suited to later
chartwise estimates and numerical coordinate formulas.
-/

@[expose] public section

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace
namespace Trace.C1

open MeasureTheory
open scoped ENNReal Sobolev

/-- For `1 ≤ p`, the global finite-exponent trace expressed in operational
boundary-atlas coordinates. -/
noncomputable def atlasTraceLp
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 ≤ p) :
    W^{1,ENNReal.ofReal p}(Ω) →L[ℝ]
      Lp ℝ (ENNReal.ofReal p)
        (atlasBoundaryMeasure (m := m) (Ω := Ω)) :=
  (surfaceLpEquivAtlasLp (m := m) (Ω := Ω) p (zero_lt_one.trans_le hp)).toLinearIsometry
    |>.toContinuousLinearMap.comp (traceLp (m := m) (Ω := Ω) p)

/-- Almost-everywhere representative of the finite-exponent trace in atlas
coordinates. -/
theorem atlasTraceLp_apply_ae
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 ≤ p)
    (u : W^{1,ENNReal.ofReal p}(Ω)) :
    (atlasTraceLp (m := m) (Ω := Ω) p hp u :
        ℝ^(m + 1) → ℝ) =ᵐ[
      atlasBoundaryMeasure (m := m) (Ω := Ω)]
      fun x ↦
        MeasureTheory.Lp.withDensityRoot
          (surfaceMeasureDensity (m := m) (Ω := Ω)) p x •
            traceLp (m := m) (Ω := Ω) p u x := by
  simpa [atlasTraceLp] using
    surfaceLpEquivAtlasLp_apply_ae
      (m := m) (Ω := Ω) p (zero_lt_one.trans_le hp)
      (traceLp (m := m) (Ω := Ω) p u)

/-- Passing from intrinsic surface measure to atlas coordinates preserves the
norm of every trace value. -/
@[simp]
theorem norm_atlasTraceLp
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 ≤ p)
    (u : W^{1,ENNReal.ofReal p}(Ω)) :
    ‖atlasTraceLp (m := m) (Ω := Ω) p hp u‖ =
      ‖traceLp (m := m) (Ω := Ω) p u‖ :=
  (surfaceLpEquivAtlasLp (m := m) (Ω := Ω) p (zero_lt_one.trans_le hp)).norm_map _

/-- The atlas-coordinate trace satisfies the same quantitative estimate as
the intrinsic trace. -/
theorem norm_atlasTraceLp_le
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 ≤ p)
    (u : W^{1,ENNReal.ofReal p}(Ω)) :
    ‖atlasTraceLp (m := m) (Ω := Ω) p hp u‖ ≤
      (∑ i : Fin hΩ.N,
        (chartSurfaceBound (m := m) (Ω := Ω) i : ℝ) ^
            (1 / ENNReal.ofReal p).toReal *
          p ^ (1 / p) *
          ‖Extension.C1.BoundaryPiece.flattenCLM
            (n := m + 1) (p := ENNReal.ofReal p)
            (Ω := Ω) i‖) * ‖u‖ := by
  rw [norm_atlasTraceLp]
  exact norm_traceLp_le (m := m) (Ω := Ω) p u

end Trace.C1
end SobolevSpace
