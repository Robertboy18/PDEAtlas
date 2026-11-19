/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.FiniteExponent.ChartTransport
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.FiniteExponentOperator
import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.C1.Scalar

/-!
# Finite-exponent trace under chart transport

The physical trace of a transported field is the transported flat trace with its
auxiliary target cutoff. Agreement for ambient smooth data follows from the C¹
representative law; finite-exponent Sobolev density then gives the operator identity.
-/

open PDE (iteratedPartialDeriv)

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1.Fractional.FiniteExponent

open MeasureTheory Set
open Boundary.Geometry.SurfaceMeasure
open Boundary.C1ExtensionAtlas.DerivedCutoffs Extension.C1.BoundaryPiece
open scoped ENNReal Sobolev Topology

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
variable (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]

/-- The scalar finite-exponent trace is literal restriction of every ambient C¹ base
representative. No support condition on that representative is required. -/
theorem traceLp_apply_ae_of_contDiff (u : W^{1,ENNReal.ofReal p}(Ω))
    {f : ℝ^(m + 1) → ℝ} (hf : ContDiff ℝ 1 f)
    (hu : GraphSpace.baseRepresentative u =ᵐ[domainMeasure (m + 1) Ω] f) :
    (traceLp p u : ℝ^(m + 1) → ℝ) =ᵐ[surfaceMeasure Ω] f := by
  let V : TopologicalSpace.Opens ℝ^(m + 1) := ⟨Ω, hΩ.isOpen⟩
  let U := (VectorValued.scalarEquiv (Ω := V)).symm u
  have hU : (U.val (GraphSpace.baseIndex (m + 1) 1) : ℝ^(m + 1) → ℝ)
      =ᵐ[domainMeasure (m + 1) V] f := hu
  have htrace := VectorValued.Trace.C1.traceLp_coeFn_ae
    (ENNReal.one_le_ofReal.mp (Fact.out : 1 ≤ ENNReal.ofReal p)) U hf hU
  rw [VectorValued.Trace.C1.traceLp_eq_scalar_traceLp] at htrace
  exact htrace

private theorem traceLp_chartTransport_testFunction (i : Fin hΩ.N)
    (φ : HalfSpace.GlobalTestFunction m) :
    traceLp p (chartTransport (ENNReal.ofReal p) i
      (GraphSpace.testFunctionToWkpLinear (k := 1) (p := ENNReal.ofReal p) φ)) =
      chartPhysicalization (ENNReal.ofReal p) i (flatTargetCutoff (ENNReal.ofReal p) i
        (flatTraceLp m p (GraphSpace.restrictCLM
          (HalfSpace.measurableSet_upper (n := m + 1)) (subset_univ _)
            (GraphSpace.testFunctionToWkpLinear (k := 1) (p := ENNReal.ofReal p) φ)))) := by
  have hφ : GraphSpace.baseRepresentative
      (GraphSpace.testFunctionToWkpLinear (k := 1) (p := ENNReal.ofReal p) φ)
      =ᵐ[domainMeasure (m + 1) univ] φ.1.toFun := by
    simpa only [GraphSpace.testFunctionToWkpLinear_apply, GraphSpace.testFunctionToWkp,
      GraphSpace.baseRepresentative, GraphSpace.baseIndex_toList, iteratedPartialDeriv] using
      (GraphSpace.mkWkpSpaceOnOfContDiff_apply_ae
        (n := m + 1) (k := 1) (p := ENNReal.ofReal p) (Ω := univ)
        (f := φ.1.toFun) φ.1.contDiff φ.1.hasCompactSupport
        (GraphSpace.baseIndex (m + 1) 1))
  have htrace := traceLp_apply_ae_of_contDiff p
    (chartTransport (ENNReal.ofReal p) i
      (GraphSpace.testFunctionToWkpLinear (k := 1) (p := ENNReal.ofReal p) φ))
    (chartTransportRepresentative_contDiff i (φ.1.contDiff.of_le (by simp)))
    (chartTransport_base_apply_ae (ENNReal.ofReal p) i _ hφ)
  let v := flatTraceLp m p (GraphSpace.restrictCLM
    (HalfSpace.measurableSet_upper (n := m + 1)) (subset_univ _)
      (GraphSpace.testFunctionToWkpLinear (k := 1) (p := ENNReal.ofReal p) φ))
  have hv : (v : ℝ^(m + 1) → ℝ) =ᵐ[flatSurfaceMeasure (n := m)] φ.1.toFun := by
    change (flatTraceLp m p (HalfSpace.globalTestFunctionToUpperW1pLinear m p φ) :
      ℝ^(m + 1) → ℝ) =ᵐ[flatSurfaceMeasure (n := m)] φ.1.toFun
    rw [← HalfSpace.CompactSupport.toUpperW1p_ofGlobalTestFunction p φ]
    exact flatTraceLp_c1_apply_ae p
      (HalfSpace.CompactSupport.ofGlobalTestFunction φ)
  have hcut : (flatTargetCutoff (ENNReal.ofReal p) i v : ℝ^(m + 1) → ℝ)
      =ᵐ[flatSurfaceMeasure (n := m)]
        fun y ↦ (targetSupportCutoff (Ω := Ω) i).toFun y * φ.1.toFun y := by
    filter_upwards [flatTargetCutoff_apply_ae (ENNReal.ofReal p) i v, hv] with y hy hφy
    exact hy.trans (congrArg ((targetSupportCutoff (Ω := Ω) i).toFun y * ·) hφy)
  have hphysical := chartPhysicalization_apply_ae_of_ae (ENNReal.ofReal p) i hcut
  have hfrontier : ∀ᵐ x ∂surfaceMeasure Ω, x ∈ frontier Ω :=
    ae_restrict_mem isClosed_frontier.measurableSet
  apply Lp.ext
  filter_upwards [htrace, hphysical, hfrontier] with x hx hp hxFrontier
  rw [hx, hp]
  exact chartTransportRepresentative_eq_on_frontier i φ.1.toFun hxFrontier

/-- Prepared chart transport commutes with the physical traces of arbitrary whole-space W¹ᵖ data. -/
theorem traceLp_chartTransport (i : Fin hΩ.N)
    (u : W^{1,ENNReal.ofReal p}((univ : Set (ℝ^(m + 1))))) :
    traceLp p (chartTransport (ENNReal.ofReal p) i u) =
      chartPhysicalization (ENNReal.ofReal p) i (flatTargetCutoff (ENNReal.ofReal p) i
        (flatTraceLp m p (GraphSpace.restrictCLM
          (HalfSpace.measurableSet_upper (n := m + 1)) (subset_univ _) u))) := by
  let A := (traceLp (Ω := Ω) p).comp (chartTransport (ENNReal.ofReal p) i)
  let B := (chartPhysicalization (ENNReal.ofReal p) i).comp
    ((flatTargetCutoff (ENNReal.ofReal p) i).comp
    ((flatTraceLp m p).comp (GraphSpace.restrictCLM
      (HalfSpace.measurableSet_upper (n := m + 1)) (subset_univ _))))
  have hdense : DenseRange (GraphSpace.testFunctionToWkpLinear (k := 1) (p := ENNReal.ofReal p)
      (n := m + 1) (Ω := univ)) := by
    intro U
    rw [mem_closure_iff_seq_limit]
    obtain ⟨f, hf, hcs, hlim⟩ := GraphSpace.globalApproximation_WkpSpace
      (Approximation.standardMollifier (m + 1)) ENNReal.ofReal_ne_top 1 U
    let φ : ℕ → HalfSpace.GlobalTestFunction m := fun j ↦
      ⟨_root_.TestFunction.mk (f j) (hf j) (hcs j) (subset_univ _), subset_univ _⟩
    refine ⟨fun j ↦ GraphSpace.testFunctionToWkpLinear (k := 1) (p := ENNReal.ofReal p) (φ j),
      fun j ↦ ⟨φ j, rfl⟩, ?_⟩
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact hlim
  have hcore (φ : HalfSpace.GlobalTestFunction m) :
      A (GraphSpace.testFunctionToWkpLinear (k := 1) (p := ENNReal.ofReal p) φ) =
        B (GraphSpace.testFunctionToWkpLinear (k := 1) (p := ENNReal.ofReal p) φ) :=
    traceLp_chartTransport_testFunction p i φ
  exact congrFun (hdense.equalizer A.continuous B.continuous (funext hcore)) u

end SobolevSpace.Trace.C1.Fractional.FiniteExponent
