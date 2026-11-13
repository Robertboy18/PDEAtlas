/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.ChartTrace
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.Operator

/-!
# A bounded lifting of chartwise half-order boundary data

Each fractional coordinate has a whole-space H¹ lifting, obtained from
the Fourier lifting and the integer Bessel–graph equivalence. The prepared chart
operator transports this lifting into the domain. For compatible chart data its
trace is exactly `ψᵢ g`; summing the finitely many local liftings therefore recovers
`g`. This identifies the range of the physical trace with the independent
chartwise fractional model.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1.Fractional

open MeasureTheory Set
open SobolevSpace.Fractional SobolevSpace.Fractional.Trace
open Boundary.Geometry.SurfaceMeasure
open Extension.C1.BoundaryPiece
open scoped ENNReal Sobolev

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- The whole-space Fourier lifting has the prescribed physical flat trace. -/
theorem flatTrace_restrict_wholeSpaceLifting (v : H^{1 / 2}(ℝ^m; ℝ)) :
    flatTrace (n := m) (GraphSpace.restrictCLM
      (HalfSpace.measurableSet_upper (n := m + 1)) (subset_univ _)
        (HalfSpace.Fractional.h1GraphEquiv (m + 1) (wholeSpaceLiftingRealCLM m v))) =
      liftLp 2 (HsSpaceReal.toL2FunCLM m (by norm_num : (0 : ℝ) ≤ 1 / 2) v) := by
  change liftLp 2 (HalfSpace.trace m (GraphSpace.restrictCLM
    (HalfSpace.measurableSet_upper (n := m + 1)) (subset_univ _)
      (HalfSpace.Fractional.h1GraphEquiv (m + 1) (wholeSpaceLiftingRealCLM m v)))) = _
  rw [HalfSpace.Fractional.trace_restrict_toWkpSpace,
    wholeSpaceTraceRealCLM_wholeSpaceLiftingRealCLM]

/-- Lift a real half-order coordinate through one prepared H¹ chart operator. -/
def localLifting (i : Fin hΩ.N) : H^{1 / 2}(ℝ^m; ℝ) →L[ℝ] H¹(Ω) :=
  (chartTransport i).comp
    ((HalfSpace.Fractional.h1GraphEquiv (m + 1)).toContinuousLinearMap.comp
      (wholeSpaceLiftingRealCLM m))

/-- The physical trace of a local lifting is its cutoff flat datum transported to the patch. -/
theorem trace_localLifting (i : Fin hΩ.N) (v : H^{1 / 2}(ℝ^m; ℝ)) :
    trace (localLifting i v) =
      chartPhysicalization 2 i (flatTargetCutoff i
        (liftLp 2 (HsSpaceReal.toL2FunCLM m (by norm_num : (0 : ℝ) ≤ 1 / 2) v))) := by
  change trace (chartTransport i
    (HalfSpace.Fractional.h1GraphEquiv (m + 1) (wholeSpaceLiftingRealCLM m v))) = _
  rw [trace_chartTransport, flatTrace_restrict_wholeSpaceLifting]

/-- A compatible coordinate lifts to exactly its single partition contribution on the surface. -/
theorem trace_localLifting_chartValue (i : Fin hΩ.N)
    (g : HalfOrderBoundarySpace (Ω := Ω)) :
    trace (localLifting i (chartValue i g)) = boundaryCutoff 2 i (boundaryValue g) := by
  rw [trace_localLifting, physical_chartValue,
    flatTargetCutoff_lift_localizedBoundaryCoordinates,
    chartPhysicalization_lift_localizedBoundaryCoordinates]

/-- The finite sum of local H¹ liftings of compatible fractional boundary data. -/
def lifting : HalfOrderBoundarySpace (Ω := Ω) →L[ℝ] H¹(Ω) :=
  ∑ i : Fin hΩ.N, (localLifting i).comp (chartValue i)

/-- The bounded lifting acts by the finite chart sum used in its construction. -/
theorem lifting_apply (g : HalfOrderBoundarySpace (Ω := Ω)) :
    lifting g = ∑ i : Fin hΩ.N, localLifting i (chartValue i g) := by
  simp [lifting]

/-- The assembled lifting has exactly the prescribed physical surface trace. -/
theorem trace_lifting (g : HalfOrderBoundarySpace (Ω := Ω)) :
    trace (lifting g) = boundaryValue g := by
  rw [lifting_apply, map_sum]
  simp_rw [trace_localLifting_chartValue]
  exact sum_boundaryCutoff 2 (boundaryValue g)

/-- The constructed H¹ lifting is a right inverse of the independent fractional trace. -/
theorem fractionalTrace_lifting (g : HalfOrderBoundarySpace (Ω := Ω)) :
    fractionalTrace (lifting g) = g := by
  apply boundaryValue_injective
  rw [boundaryValue_fractionalTrace, trace_lifting]

/-- Every compatible half-order boundary datum is the trace of an H¹ function. -/
theorem fractionalTrace_surjective :
    Function.Surjective (fractionalTrace (Ω := Ω)) :=
  fun g ↦ ⟨lifting g, fractionalTrace_lifting g⟩

/-- The physical range of the original C¹ trace is precisely the chartwise fractional range. -/
theorem range_trace_eq_range_boundaryValue :
    Set.range (trace (Ω := Ω)) = Set.range (boundaryValue (Ω := Ω)) := by
  apply Set.Subset.antisymm range_trace_subset_range_boundaryValue
  rintro _ ⟨g, rfl⟩
  exact ⟨lifting g, trace_lifting g⟩

/-- Surface data are H¹ traces exactly when all partitioned coordinates have real Bessel order ½. -/
theorem mem_range_trace_iff (g : Lp ℝ 2 (surfaceMeasure Ω)) :
    g ∈ Set.range (trace (Ω := Ω)) ↔
      ∀ i : Fin hΩ.N, localizedBoundaryCoordinates 2 i g ∈
        Set.range (HsSpaceReal.toL2FunCLM m (by norm_num : (0 : ℝ) ≤ 1 / 2)) := by
  rw [range_trace_eq_range_boundaryValue]
  exact mem_range_boundaryValue_iff g

/-- Local lifting retains the exact Fourier factor and the two constructed transport norms. -/
theorem norm_localLifting_le (i : Fin hΩ.N) (v : H^{1 / 2}(ℝ^m; ℝ)) :
    ‖localLifting i v‖ ≤
      (‖preparedChartCLM (p := 2) i‖ *
        ‖(HalfSpace.Fractional.h1GraphEquiv (m + 1)).toContinuousLinearMap‖ *
          (Real.sqrt Real.pi)⁻¹) * ‖v‖ := by
  let I := (HalfSpace.Fractional.h1GraphEquiv (m + 1)).toContinuousLinearMap
  calc
    ‖localLifting i v‖ ≤
        ‖preparedChartCLM (p := 2) i‖ * ‖I (wholeSpaceLiftingRealCLM m v)‖ :=
      norm_chartTransport_le i _
    _ ≤ ‖preparedChartCLM (p := 2) i‖ *
        (‖I‖ * ‖wholeSpaceLiftingRealCLM m v‖) :=
      mul_le_mul_of_nonneg_left (I.le_opNorm _)
        (norm_nonneg (preparedChartCLM (p := 2) i))
    _ = _ := by
      rw [norm_wholeSpaceLiftingRealCLM]
      simp only [I, mul_assoc]

/-- The reconstruction is bounded by the finite sum of the local lifting estimates. -/
theorem norm_lifting_le (g : HalfOrderBoundarySpace (Ω := Ω)) :
    ‖lifting g‖ ≤ ∑ i : Fin hΩ.N,
      (‖preparedChartCLM (p := 2) i‖ *
        ‖(HalfSpace.Fractional.h1GraphEquiv (m + 1)).toContinuousLinearMap‖ *
          (Real.sqrt Real.pi)⁻¹) * ‖chartValue i g‖ := by
  rw [lifting_apply]
  exact (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun i _ ↦ norm_localLifting_le i (chartValue i g))

end SobolevSpace.Trace.C1.Fractional
