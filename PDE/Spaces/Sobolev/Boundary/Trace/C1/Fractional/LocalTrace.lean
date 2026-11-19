/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Operator
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.FiniteExponentOperator
import PDE.Spaces.Sobolev.Boundary.Trace.C1.ZeroTrace.Localization

/-!
# Fractional traces in C¹ boundary charts

Flattening a partition piece and taking its half-space trace gives an element of the
real Bessel space `H^{1/2}(ℝ^m)`. Its physical representative is exactly the
localized trace used in the C¹ surface trace construction.

The local fractional traces reconstruct the physical trace and have the same common
kernel. Thus they depend only on the boundary value. This is a regularity statement
for the curved trace range; the boundary fractional space itself is defined in
`Trace.C1.Fractional.Space`.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Trace.C1.Fractional

open MeasureTheory
open SobolevSpace.Fractional
open Boundary.Geometry.SurfaceMeasure
open Extension.C1.BoundaryPiece
open scoped ENNReal Sobolev

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- Fractional trace of a localized field in one boundary chart. -/
def localFractionalTrace (i : Fin hΩ.N) :
    H¹(Ω) →L[ℝ] H^{1 / 2}(ℝ^m; ℝ) :=
  (HalfSpace.Fractional.fractionalTrace m).comp (flattenCLM (p := 2) i)

/-- The physical representative of a chart's fractional trace is the flat trace. -/
theorem physical_localFractionalTrace (i : Fin hΩ.N)
    (u : H¹(Ω)) :
    liftLp (n := m) 2
        (HsSpaceReal.toL2FunCLM m (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (localFractionalTrace i u)) = localFlatTrace i u := by
  change liftLp (n := m) 2
    (HsSpaceReal.toL2FunCLM m _ (HalfSpace.Fractional.fractionalTrace m
      (flattenCLM (p := 2) i u))) = _
  rw [HalfSpace.Fractional.physical_fractionalTrace]
  rfl

/-- Each local fractional trace is bounded by the flat trace and chart-flattening norms. -/
theorem norm_localFractionalTrace_le (i : Fin hΩ.N)
    (u : H¹(Ω)) :
    ‖localFractionalTrace i u‖ ≤
      (‖HalfSpace.Fractional.fractionalTrace m‖ * ‖flattenCLM (p := 2) i‖) * ‖u‖ := by
  calc
    ‖localFractionalTrace i u‖ ≤
        ‖HalfSpace.Fractional.fractionalTrace m‖ * ‖flattenCLM (p := 2) i u‖ :=
      (HalfSpace.Fractional.fractionalTrace m).le_opNorm _
    _ ≤ ‖HalfSpace.Fractional.fractionalTrace m‖ *
        (‖flattenCLM (p := 2) i‖ * ‖u‖) :=
      mul_le_mul_of_nonneg_left ((flattenCLM (p := 2) i).le_opNorm u)
        (norm_nonneg (HalfSpace.Fractional.fractionalTrace m))
    _ = _ := (mul_assoc _ _ _).symm

/-- Returning all local fractional traces to physical coordinates reconstructs the trace. -/
theorem trace_eq_sum_physical_localFractionalTrace
    (u : H¹(Ω)) :
    trace u = ∑ i : Fin hΩ.N, chartPhysicalization (2 : ℝ≥0∞) i
      (liftLp (n := m) 2
        (HsSpaceReal.toL2FunCLM m (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (localFractionalTrace i u))) := by
  simp only [physical_localFractionalTrace, trace, sum_apply,
    localPhysicalTrace, ContinuousLinearMap.comp_apply]

/-- The real-exponent and Hilbert localized flat traces agree under exponent transport. -/
theorem localFlatTraceLp_two (i : Fin hΩ.N)
    (u : W^{1,ENNReal.ofReal (2 : ℝ)}(Ω)) :
    Lp.congrExponent (ENNReal.ofReal_ofNat 2) (flatSurfaceMeasure (n := m))
        (localFlatTraceLp 2 i u) = localFlatTrace i (domainW1pTwoEquivH1 u) := by
  let e := Lp.congrExponent (E := ℝ) (ENNReal.ofReal_ofNat 2)
    (flatSurfaceMeasure (n := m))
  let lhs := e.toContinuousLinearMap.comp (localFlatTraceLp (Ω := Ω) 2 i)
  let rhs := (localFlatTrace (Ω := Ω) i).comp
    (domainW1pTwoEquivH1 (Ω := Ω)).toContinuousLinearMap
  have heq : (lhs : _ → _) ∘
      globalTestFunctionToDomainW1pLinear (ENNReal.ofReal (2 : ℝ)) =
      (rhs : _ → _) ∘
        globalTestFunctionToDomainW1pLinear (ENNReal.ofReal (2 : ℝ)) := by
    funext φ
    change e (localFlatTraceLp 2 i
      (globalTestFunctionToDomainW1pLinear (ENNReal.ofReal (2 : ℝ)) φ)) =
      localFlatTrace i (domainW1pTwoEquivH1
        (globalTestFunctionToDomainW1pLinear (ENNReal.ofReal (2 : ℝ)) φ))
    rw [domainW1pTwoEquivH1_globalTestFunction]
    apply Lp.ext
    rw [show (e _ : ℝ^(m + 1) → ℝ) = _ from Lp.coeFn_congrExponent _ _ _]
    exact (localFlatTraceLp_classical_apply_ae 2 i φ).trans
      (localFlatTrace_classical_apply_ae i φ).symm
  exact congrFun
    ((denseRange_globalTestFunctionToDomainW1pLinear
      (m := m) (Ω := Ω) (ENNReal.ofReal (2 : ℝ)) (by norm_num)).equalizer
        lhs.continuous rhs.continuous heq) u

/-- A vanishing physical boundary value gives zero fractional trace in each chart. -/
theorem localFractionalTrace_eq_zero_of_trace_eq_zero (i : Fin hΩ.N)
    (u : H¹(Ω)) (hu : trace u = 0) :
    localFractionalTrace i u = 0 := by
  have hflat : localFlatTrace i u = 0 := by
    obtain ⟨v, rfl⟩ := (domainW1pTwoEquivH1 (Ω := Ω)).surjective u
    have hv : traceLp 2 v = 0 := by
      apply (boundaryLpTwoEquivL2 (Ω := Ω)).injective
      rw [map_zero, boundaryLpTwoEquivL2_traceLp]
      exact hu
    rw [← localFlatTraceLp_two (Ω := Ω), localFlatTraceLp_eq_zero_of_traceLp_eq_zero 2 i v hv,
      map_zero]
  apply HsSpaceReal.toL2FunCLM_injective (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply (liftLp (n := m) 2).injective
  rw [physical_localFractionalTrace, hflat, map_zero, map_zero]

/-- The common kernel of the local fractional traces is the physical trace kernel. -/
theorem trace_eq_zero_iff_localFractionalTrace_eq_zero
    (u : H¹(Ω)) :
    trace u = 0 ↔ ∀ i : Fin hΩ.N, localFractionalTrace i u = 0 := by
  refine ⟨fun hu i ↦ localFractionalTrace_eq_zero_of_trace_eq_zero i u hu, ?_⟩
  intro hu
  rw [trace_eq_sum_physical_localFractionalTrace]
  simp only [hu, map_zero, Finset.sum_const_zero]

/-- Two fields have the same physical trace exactly when all fractional chart traces agree. -/
theorem trace_eq_iff_localFractionalTrace_eq
    (u v : H¹(Ω)) :
    trace u = trace v ↔
      ∀ i : Fin hΩ.N, localFractionalTrace i u = localFractionalTrace i v := by
  simpa only [map_sub, sub_eq_zero] using
    (trace_eq_zero_iff_localFractionalTrace_eq_zero (u - v))

end SobolevSpace.Trace.C1.Fractional
