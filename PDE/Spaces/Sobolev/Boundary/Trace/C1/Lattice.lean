/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.PositivePart
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.ContinuousRepresentative
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.ZeroTrace
public import PDE.Spaces.Sobolev.Calculus.Composition.PositivePart.Domain

/-!
# Positive parts and the geometric trace

The finite-exponent trace commutes with positive parts. Smooth ambient
restrictions are dense, their positive parts have continuous representatives,
and both operations are strongly continuous. Combining this identity with
the trace-kernel theorem constructs zero-boundary positive parts from
signed or ordered boundary traces.
-/

open PDE (iteratedPartialDeriv)

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1

open MeasureTheory Set GraphSpace Boundary Approximation.UpToBoundary
open Boundary.Geometry.SurfaceMeasure
open scoped ENNReal Topology Sobolev

variable {m : ℕ} {Ω : Set ℝ^(m + 1)} [H : C1ExtensionAtlas (m + 1) Ω]

/-- Density and continuous-representative agreement determine trace truncation. -/
private theorem trace_posPart_of_continuous_representatives
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : W^{1,p}(Ω) →L[ℝ] Lp ℝ p (surfaceMeasure Ω))
    (hT : ∀ (U : W^{1,p}(Ω)) {f : ℝ^(m + 1) → ℝ},
      ContinuousOn f (closure Ω) →
      baseRepresentative U =ᵐ[domainMeasure (m + 1) Ω] f →
      (T U : ℝ^(m + 1) → ℝ) =ᵐ[surfaceMeasure Ω] f)
    (U : W^{1,p}(Ω)) :
    T (lipschitzCompositionOn H.isOpen Lp.lipschitzWith_pos_part U) = Lp.posPart (T U) := by
  have heq := (denseRange_globalTestFunctionToDomainW1pLinear
    (Ω := Ω) p hp).equalizer
    ((T).continuous.comp
      (continuous_lipschitzCompositionOn_posPart hp))
    (Lp.continuous_posPart.comp (T).continuous) ?_
  · exact congrFun heq U
  funext φ
  apply Lp.ext
  have hbase : baseRepresentative
      (globalTestFunctionToDomainW1pLinear (Ω := Ω) p φ)
        =ᵐ[domainMeasure (m + 1) Ω] φ.1.toFun := by
    rw [globalTestFunctionToDomainW1pLinear_eq_mk]
    simpa only [baseRepresentative, baseIndex_toList, iteratedPartialDeriv] using
      mkWkpSpaceOnOfContDiff_apply_ae (Ω := Ω) φ.1.toFun φ.1.contDiff
        φ.1.hasCompactSupport (baseIndex (m + 1) 1)
  have hpos := lipschitzCompositionOn_base_ae H.isOpen Lp.lipschitzWith_pos_part
    (globalTestFunctionToDomainW1pLinear (Ω := Ω) p φ)
  have hleft := hT
    (lipschitzCompositionOn H.isOpen Lp.lipschitzWith_pos_part
      (globalTestFunctionToDomainW1pLinear (Ω := Ω) p φ))
    (φ.1.contDiff.continuous.max continuous_const).continuousOn
    (hpos.trans (hbase.fun_comp (fun s : ℝ ↦ max s 0)))
  have hright := hT (globalTestFunctionToDomainW1pLinear (Ω := Ω) p φ)
    φ.1.contDiff.continuous.continuousOn hbase
  exact hleft.trans ((Lp.coeFn_posPart _).trans
    (hright.fun_comp (fun s : ℝ ↦ max s 0))).symm

/-- Positive parts commute with the finite-exponent geometric trace. -/
theorem traceLp_posPart (P : InwardPartition Ω)
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (U : W^{1,ENNReal.ofReal p}(Ω)) :
    traceLp p (lipschitzCompositionOn H.isOpen Lp.lipschitzWith_pos_part U) =
      Lp.posPart (traceLp p U) :=
  trace_posPart_of_continuous_representatives ENNReal.ofReal_ne_top (traceLp p)
    (traceLp_eq_ae_of_continuousOn P p) U

/-- Positive parts commute with the Hilbert trace. -/
theorem trace_posPart (P : InwardPartition Ω) (U : H¹(Ω)) :
    trace (lipschitzCompositionOn H.isOpen Lp.lipschitzWith_pos_part U) = Lp.posPart (trace U) :=
  trace_posPart_of_continuous_representatives (by norm_num) trace
    (trace_eq_ae_of_continuousOn P) U

/-- A nonpositive geometric trace makes the positive part a `W¹ᵖ₀` element. -/
theorem posPart_mem_Wkp0_iff_traceLp_nonpos (P : InwardPartition Ω)
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (U : W^{1,ENNReal.ofReal p}(Ω)) :
    lipschitzCompositionOn H.isOpen Lp.lipschitzWith_pos_part U ∈
      (wkp0SubmoduleOn (n := m + 1) (k := 1) (p := ENNReal.ofReal p)
        (Ω := Ω)).toSubmodule ↔
      ∀ᵐ x ∂surfaceMeasure Ω, (traceLp p U : ℝ^(m + 1) → ℝ) x ≤ 0 := by
  rw [← traceLp_eq_zero_iff_mem_Wkp0 p, traceLp_posPart P, Lp.posPart_eq_zero_iff]

/-- Ordered boundary traces give the zero-boundary positive part of their difference. -/
theorem posPart_sub_mem_Wkp0_iff_traceLp_le (P : InwardPartition Ω)
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (U V : W^{1,ENNReal.ofReal p}(Ω)) :
    lipschitzCompositionOn H.isOpen Lp.lipschitzWith_pos_part (U - V) ∈
      (wkp0SubmoduleOn (n := m + 1) (k := 1) (p := ENNReal.ofReal p)
        (Ω := Ω)).toSubmodule ↔
      ∀ᵐ x ∂surfaceMeasure Ω, (traceLp p U : ℝ^(m + 1) → ℝ) x ≤
        (traceLp p V : ℝ^(m + 1) → ℝ) x := by
  rw [← traceLp_eq_zero_iff_mem_Wkp0 p, traceLp_posPart P, map_sub,
    Lp.posPart_sub_eq_zero_iff]

/-- A nonpositive H¹ trace gives an H¹₀ positive part, and conversely. -/
theorem posPart_mem_H10_iff_trace_nonpos (P : InwardPartition Ω)
    (U : H¹(Ω)) :
    lipschitzCompositionOn H.isOpen Lp.lipschitzWith_pos_part U ∈
      (h10SubmoduleOn (n := m + 1) (Ω := Ω)).toSubmodule ↔
      ∀ᵐ x ∂surfaceMeasure Ω, (trace U : ℝ^(m + 1) → ℝ) x ≤ 0 := by
  rw [← trace_eq_zero_iff_mem_H10, trace_posPart P, Lp.posPart_eq_zero_iff]

/-- Ordered H¹ traces are equivalent to zero-boundary truncation of the difference. -/
theorem posPart_sub_mem_H10_iff_trace_le (P : InwardPartition Ω)
    (U V : H¹(Ω)) :
    lipschitzCompositionOn H.isOpen Lp.lipschitzWith_pos_part (U - V) ∈
      (h10SubmoduleOn (n := m + 1) (Ω := Ω)).toSubmodule ↔
      ∀ᵐ x ∂surfaceMeasure Ω, (trace U : ℝ^(m + 1) → ℝ) x ≤
        (trace V : ℝ^(m + 1) → ℝ) x := by
  rw [← trace_eq_zero_iff_mem_H10, trace_posPart P, map_sub, Lp.posPart_sub_eq_zero_iff]

end SobolevSpace.Trace.C1
