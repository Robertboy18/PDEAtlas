/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.Space
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.Compatibility

/-!
# The C¹ trace into the chartwise half-order boundary space

The physical trace and the local fractional traces give a bounded map into
the independently defined Hilbert graph of compatible boundary data. Its physical
value is the original C¹ trace, so the kernels agree.

Surjectivity comes from the localized lifting of compatible boundary data in
`Trace.C1.Fractional.Lifting`.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Trace.C1.Fractional

open MeasureTheory
open SobolevSpace.Fractional
open Boundary.Geometry.SurfaceMeasure
open scoped ENNReal Sobolev

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- The physical trace together with its fractional chart coordinates in a Hilbert product. -/
def traceData : H¹(Ω) →L[ℝ] BoundaryChartData (Ω := Ω) where
  toFun u := WithLp.toLp 2 (trace u, WithLp.toLp 2 (fun i ↦ localFractionalTrace i u))
  map_add' u v := by
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · exact map_add (trace (Ω := Ω)) u v
    · apply PiLp.ext
      intro i
      exact map_add (localFractionalTrace i) u v
  map_smul' c u := by
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · exact map_smul (trace (Ω := Ω)) c u
    · apply PiLp.ext
      intro i
      exact map_smul (localFractionalTrace i) c u
  cont := (WithLp.prod_continuous_toLp 2 _ _).comp
    ((trace (Ω := Ω)).continuous.prodMk
      ((PiLp.continuous_toLp 2 (fun _ : Fin hΩ.N ↦ H^{1 / 2}(ℝ^m; ℝ))).comp
        (continuous_pi (fun i ↦ (localFractionalTrace i).continuous))))

/-- The C¹ trace data satisfy the independently defined chart constraints. -/
theorem traceData_mem_halfOrderBoundarySubmodule (u : H¹(Ω)) :
    traceData u ∈ halfOrderBoundarySubmodule (Ω := Ω) := by
  change ContinuousLinearMap.pi (coordinateCompatibility (Ω := Ω)) (traceData u) = 0
  funext i
  change HsSpaceReal.toL2FunCLM m _ (localFractionalTrace i u) -
    localizedBoundaryCoordinates 2 i (trace u) = 0
  exact sub_eq_zero.mpr (localizedBoundaryCoordinates_trace i u).symm

/-- The bounded C¹ trace with values in the independent chartwise half-order boundary space. -/
def fractionalTrace :
    H¹(Ω) →L[ℝ] HalfOrderBoundarySpace (Ω := Ω) :=
  (traceData (Ω := Ω)).codRestrict (halfOrderBoundarySubmodule (Ω := Ω)).toSubmodule
    traceData_mem_halfOrderBoundarySubmodule

/-- The fractional trace has exactly the physical surface boundary value. -/
@[simp]
theorem boundaryValue_fractionalTrace (u : H¹(Ω)) :
    boundaryValue (fractionalTrace u) = trace u := rfl

/-- Each coordinate of the bundled fractional trace is its local half-space fractional trace. -/
@[simp]
theorem chartValue_fractionalTrace (i : Fin hΩ.N)
    (u : H¹(Ω)) :
    chartValue i (fractionalTrace u) = localFractionalTrace i u := rfl

/-- The fractional trace norm is the physical norm plus all local fractional energies. -/
theorem norm_fractionalTrace_sq (u : H¹(Ω)) :
    ‖fractionalTrace u‖ ^ 2 =
      ‖trace u‖ ^ 2 + ∑ i : Fin hΩ.N, ‖localFractionalTrace i u‖ ^ 2 := by
  simpa only [boundaryValue_fractionalTrace, chartValue_fractionalTrace] using
    norm_sq_halfOrderBoundarySpace (fractionalTrace u)

/-- The bounded fractional trace and the physical trace have the same kernel. -/
theorem ker_fractionalTrace :
    (fractionalTrace (Ω := Ω)).ker = (trace (Ω := Ω)).ker := by
  ext u
  change fractionalTrace u = 0 ↔ trace u = 0
  rw [← boundaryValue_fractionalTrace]
  exact ((boundaryValue_injective (Ω := Ω)).eq_iff'
    (map_zero (boundaryValue (Ω := Ω)))).symm

/-- Every physical trace lies in the surface image of the chartwise half-order space. -/
theorem range_trace_subset_range_boundaryValue :
    Set.range (trace (Ω := Ω)) ⊆ Set.range (boundaryValue (Ω := Ω)) := by
  rintro _ ⟨u, rfl⟩
  exact ⟨fractionalTrace u, boundaryValue_fractionalTrace u⟩

end SobolevSpace.Trace.C1.Fractional
