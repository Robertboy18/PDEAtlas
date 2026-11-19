/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.Cutoff
import PDE.Spaces.Sobolev.Approximation.Density.Global

/-!
# Trace commutes with prepared chart transport

Transport first multiplies by the auxiliary target cutoff, pulls back through
the chart, and restricts to the domain. Its physical trace is the corresponding
cutoff of the flat trace, transported to the boundary patch. The identity follows
on smooth inputs from the classical trace formulas, then on all whole-space H¹
inputs by density and continuity.
-/

open PDE (iteratedPartialDeriv)

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1.Fractional

open MeasureTheory Set
open Boundary.Geometry.SurfaceMeasure
open Boundary.C1ExtensionAtlas.DerivedCutoffs
open Extension.C1.BoundaryPiece
open scoped ENNReal Sobolev Topology

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- Whole-space representatives are transported by the prepared chart map almost everywhere. -/
theorem chartTransport_base_apply_ae (i : Fin hΩ.N)
    (u : H¹((univ : Set (ℝ^(m + 1))))) {f : ℝ^(m + 1) → ℝ}
    (hu : GraphSpace.baseRepresentative u =ᵐ[domainMeasure (m + 1) univ] f) :
    GraphSpace.baseRepresentative (chartTransport i u) =ᵐ[domainMeasure (m + 1) Ω]
      chartTransportRepresentative i f := by
  let uT : H¹((hΩ.chart i).target) :=
    GraphSpace.restrictCLM (hΩ.chart i).open_target.measurableSet (subset_univ _) u
  have huT : GraphSpace.baseRepresentative uT
      =ᵐ[domainMeasure (m + 1) (hΩ.chart i).target] f :=
    (GraphSpace.restrictCLM_apply_ae (hΩ.chart i).open_target.measurableSet
      (subset_univ _) u (GraphSpace.baseIndex (m + 1) 1)).trans
        (hu.filter_mono (ae_mono (GraphSpace.domainMeasure_le (subset_univ _))))
  have hp := preparedChartCLM_base_apply_ae i uT huT
  exact (GraphSpace.restrictCLM_apply_ae hΩ.isOpen.measurableSet (subset_univ _)
    (preparedChartCLM (p := 2) i uT) (GraphSpace.baseIndex (m + 1) 1)).trans
      (hp.filter_mono (ae_mono (GraphSpace.domainMeasure_le (subset_univ _))))

/-- On the frontier the source cutoff leaves precisely the target-cutoff chart contribution. -/
theorem chartTransportRepresentative_eq_on_frontier
    (i : Fin hΩ.N) (f : ℝ^(m + 1) → ℝ) {x : ℝ^(m + 1)}
    (hx : x ∈ frontier Ω) :
    chartTransportRepresentative i f x =
      (chartBoundaryPatch i).indicator (fun z ↦
        (targetSupportCutoff (Ω := Ω) i).toFun (hΩ.chart i z) * f (hΩ.chart i z)) x := by
  by_cases hxSource : x ∈ (hΩ.chart i).source
  · rw [indicator_of_mem (show x ∈ chartBoundaryPatch (Ω := Ω) i from ⟨hxSource, hx⟩)]
    by_cases hη : (targetSupportCutoff (Ω := Ω) i).toFun (hΩ.chart i x) = 0
    · simp [chartTransportRepresentative, hη]
    · have hxSupport : x ∈ pullbackSupport (Ω := Ω) i :=
        ⟨hΩ.chart i x, subset_tsupport _ hη, (hΩ.chart i).left_inv hxSource⟩
      simp only [chartTransportRepresentative,
        pullbackSupportCutoff_eq_one_on_pullbackSupport i x hxSupport, one_mul]
  · have hxPatch : x ∉ chartBoundaryPatch (Ω := Ω) i := fun h ↦ hxSource h.1
    have hχ : (pullbackSupportCutoff (Ω := Ω) i).toFun x = 0 := by
      by_contra hne
      exact hxSource (tsupport_pullbackSupportCutoff_subset_source i (subset_tsupport _ hne))
    simp [chartTransportRepresentative, indicator_of_notMem hxPatch, hχ]

private theorem trace_chartTransport_testFunction (i : Fin hΩ.N)
    (φ : HalfSpace.GlobalTestFunction m) :
    trace (chartTransport i (GraphSpace.testFunctionToH1Linear φ)) =
      chartPhysicalization 2 i (flatTargetCutoff i
        (flatTrace (n := m) (GraphSpace.restrictCLM
          (HalfSpace.measurableSet_upper (n := m + 1)) (subset_univ _)
            (GraphSpace.testFunctionToH1Linear φ)))) := by
  have hφ : GraphSpace.baseRepresentative (GraphSpace.testFunctionToH1Linear φ)
      =ᵐ[domainMeasure (m + 1) univ] φ.1.toFun := by
    simpa only [GraphSpace.testFunctionToH1Linear_apply, GraphSpace.testFunctionToH1,
      GraphSpace.baseRepresentative, GraphSpace.baseIndex_toList, iteratedPartialDeriv] using
      (GraphSpace.mkWkpSpaceOnOfContDiff_apply_ae
        (n := m + 1) (k := 1) (p := (2 : ℝ≥0∞)) (Ω := univ)
        (f := φ.1.toFun) φ.1.contDiff φ.1.hasCompactSupport
        (GraphSpace.baseIndex (m + 1) 1))
  have htrace := trace_apply_ae_of_contDiff
    (chartTransport i (GraphSpace.testFunctionToH1Linear φ))
    (chartTransportRepresentative_contDiff i (φ.1.contDiff.of_le (by simp)))
    (chartTransport_base_apply_ae i _ hφ)
  let v := flatTrace (n := m) (GraphSpace.restrictCLM
    (HalfSpace.measurableSet_upper (n := m + 1)) (subset_univ _)
      (GraphSpace.testFunctionToH1Linear φ))
  have hv : (v : ℝ^(m + 1) → ℝ) =ᵐ[flatSurfaceMeasure (n := m)] φ.1.toFun := by
    change (flatTrace (HalfSpace.globalTestFunctionToUpperH1Linear m φ) :
      ℝ^(m + 1) → ℝ) =ᵐ[flatSurfaceMeasure (n := m)] φ.1.toFun
    rw [← HalfSpace.CompactSupport.toUpperH1_ofGlobalTestFunction φ]
    exact HalfSpace.CompactSupport.flatTrace_c1_apply_ae
      (HalfSpace.CompactSupport.ofGlobalTestFunction φ)
  have hcut : (flatTargetCutoff i v : ℝ^(m + 1) → ℝ)
      =ᵐ[flatSurfaceMeasure (n := m)]
        fun y ↦ (targetSupportCutoff (Ω := Ω) i).toFun y * φ.1.toFun y := by
    filter_upwards [flatTargetCutoff_apply_ae i v, hv] with y hy hφy
    exact hy.trans (congrArg ((targetSupportCutoff (Ω := Ω) i).toFun y * ·) hφy)
  have hphysical := chartPhysicalization_apply_ae_of_ae 2 i hcut
  have hfrontier : ∀ᵐ x ∂surfaceMeasure Ω, x ∈ frontier Ω :=
    ae_restrict_mem isClosed_frontier.measurableSet
  apply Lp.ext
  filter_upwards [htrace, hphysical, hfrontier] with x hx hp hxFrontier
  rw [hx, hp]
  exact chartTransportRepresentative_eq_on_frontier i φ.1.toFun hxFrontier

/-- Prepared chart transport commutes with the physical traces of arbitrary whole-space H¹ data. -/
theorem trace_chartTransport (i : Fin hΩ.N)
    (u : H¹((univ : Set (ℝ^(m + 1))))) :
    trace (chartTransport i u) =
      chartPhysicalization 2 i (flatTargetCutoff i
        (flatTrace (n := m) (GraphSpace.restrictCLM
          (HalfSpace.measurableSet_upper (n := m + 1)) (subset_univ _) u))) := by
  let A := (trace (Ω := Ω)).comp (chartTransport i)
  let B := (chartPhysicalization 2 i).comp ((flatTargetCutoff i).comp
    ((flatTrace (n := m)).comp (GraphSpace.restrictCLM
      (HalfSpace.measurableSet_upper (n := m + 1)) (subset_univ _))))
  have hdense : DenseRange (GraphSpace.testFunctionToH1Linear
      (n := m + 1) (Ω := univ)) := by
    intro U
    rw [mem_closure_iff_seq_limit]
    obtain ⟨f, hf, hcs, hlim⟩ := GraphSpace.globalApproximation_WkpSpace
      (Approximation.standardMollifier (m + 1)) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) 1 U
    let φ : ℕ → HalfSpace.GlobalTestFunction m := fun j ↦
      ⟨_root_.TestFunction.mk (f j) (hf j) (hcs j) (subset_univ _), subset_univ _⟩
    refine ⟨fun j ↦ GraphSpace.testFunctionToH1Linear (φ j), fun j ↦ ⟨φ j, rfl⟩, ?_⟩
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact hlim
  have hcore (φ : HalfSpace.GlobalTestFunction m) :
      A (GraphSpace.testFunctionToH1Linear φ) = B (GraphSpace.testFunctionToH1Linear φ) :=
    trace_chartTransport_testFunction i φ
  exact congrFun (hdense.equalizer A.continuous B.continuous (funext hcore)) u

/-- The chart transport bound uses the prepared chart norm; both restrictions are contractions. -/
theorem norm_chartTransport_le (i : Fin hΩ.N)
    (u : H¹((univ : Set (ℝ^(m + 1))))) :
    ‖chartTransport i u‖ ≤ ‖preparedChartCLM (p := 2) i‖ * ‖u‖ := by
  let uT := GraphSpace.restrictCLM (hΩ.chart i).open_target.measurableSet (subset_univ _) u
  calc
    ‖chartTransport i u‖ ≤ ‖preparedChartCLM (p := 2) i uT‖ :=
      GraphSpace.norm_restrictCLM_apply_le hΩ.isOpen.measurableSet (subset_univ _) _
    _ ≤ ‖preparedChartCLM (p := 2) i‖ * ‖uT‖ := (preparedChartCLM (p := 2) i).le_opNorm uT
    _ ≤ ‖preparedChartCLM (p := 2) i‖ * ‖u‖ :=
      mul_le_mul_of_nonneg_left
        (GraphSpace.norm_restrictCLM_apply_le
          (hΩ.chart i).open_target.measurableSet (subset_univ _) u)
        (norm_nonneg (preparedChartCLM (p := 2) i))

end SobolevSpace.Trace.C1.Fractional
