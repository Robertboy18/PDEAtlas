/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.ZeroTrace.CompactSupport
public import PDE.Spaces.Sobolev.Extension.C1.Assembly.BoundaryPiece.Assembly
import PDE.Spaces.Sobolev.Boundary.ZeroTrace.VectorValued.Trace.C1.Reconstruction
import PDE.Spaces.Sobolev.Extension.C1.Assembly.BoundaryPiece.Agreement

/-!
# Reconstructing zero-boundary fields through C¹ charts

A half-space test function pulls back, after chart localization, to a C¹ function with
compact support inside the physical domain. Its Sobolev restriction therefore belongs to
`W^{1,p}_0(Ω)`. Continuity extends this statement to the closure of the half-space test
functions. The chart need only be C¹; no smoothness of its pullback is assumed.

The support statement is not proved here: it is the case `F = ℝ` of the Banach-valued
`SobolevSpace.VectorValued.Trace.C1.chartReturn_testFunction_support`.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.Trace.C1

open MeasureTheory Set GraphSpace
open Boundary.C1ExtensionAtlas.DerivedCutoffs
open Extension.C1.BoundaryPiece
open scoped ENNReal Sobolev

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- The localized pullback of a test function supported in the upper half-space. -/
def chartTestFunctionPullback (i : Fin hΩ.N)
    (φ : TestFunctionOn (m + 1) (SobolevSpace.HalfSpace.upper (m + 1)))
    (x : ℝ^(m + 1)) : ℝ :=
  (pullbackSupportCutoff i).toFun x *
    ((targetSupportCutoff i).toFun (hΩ.chart i x) * φ.1.toFun (hΩ.chart i x))

/-- Pullback of a half-space test function has compact support in the physical domain. This is
`SobolevSpace.VectorValued.Trace.C1.chartReturn_testFunction_support` at codomain `ℝ`, applied
to the half-space test function `(targetSupportCutoff i) * φ`. -/
theorem chartTestFunctionPullback_support (i : Fin hΩ.N)
    (φ : TestFunctionOn (m + 1) (SobolevSpace.HalfSpace.upper (m + 1))) :
    HasCompactSupport (chartTestFunctionPullback i φ) ∧
      tsupport (chartTestFunctionPullback i φ) ⊆ Ω :=
  VectorValued.Trace.C1.chartReturn_testFunction_support (Ω := ⟨Ω, hΩ.isOpen⟩) (hΩ := hΩ)
    (F := ℝ) i
    ⟨fun y ↦ (targetSupportCutoff i).toFun y * φ.1.toFun y,
      (targetSupportCutoff i).contDiff.mul φ.1.contDiff, φ.1.hasCompactSupport.mul_left,
      tsupport_mul_subset_right.trans φ.2⟩

/-- On the chart source, the auxiliary source cutoff does not alter the target-localized
pullback of a test function. -/
theorem chartTestFunctionPullback_eq_on_source (i : Fin hΩ.N)
    (φ : TestFunctionOn (m + 1) (SobolevSpace.HalfSpace.upper (m + 1)))
    {x : ℝ^(m + 1)} (hx : x ∈ (hΩ.chart i).source) :
    chartTestFunctionPullback i φ x =
      (targetSupportCutoff i).toFun (hΩ.chart i x) * φ.1.toFun (hΩ.chart i x) := by
  by_cases ht : hΩ.chart i x ∈ targetCutoffSupport (Ω := Ω) i
  · have hL : x ∈ pullbackSupport (Ω := Ω) i :=
      ⟨hΩ.chart i x, ht, (hΩ.chart i).left_inv hx⟩
    simp only [chartTestFunctionPullback,
      pullbackSupportCutoff_eq_one_on_pullbackSupport i x hL, one_mul]
  · have hzero : (targetSupportCutoff i).toFun (hΩ.chart i x) = 0 :=
      image_eq_zero_of_notMem_tsupport ht
    simp only [chartTestFunctionPullback, hzero, zero_mul, mul_zero]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On the physical domain, reconstructing a half-space test function has the localized
classical pullback as its base representative. -/
theorem boundaryFromUpperCLM_testFunction_base_ae (i : Fin hΩ.N)
    (φ : TestFunctionOn (m + 1) (SobolevSpace.HalfSpace.upper (m + 1))) :
    baseRepresentative (boundaryFromUpperCLM (p := p) i (testFunctionToWkp φ)) =ᵐ[
      domainMeasure (m + 1) Ω] chartTestFunctionPullback i φ := by
  let E := Boundary.C1ExtensionAtlas.Charts.chartOnΩ (Ω := Ω) i
  let U := testFunctionToWkp (k := 1) (p := p) φ
  let W := reflectedChartTargetCLM (p := p) (Ω := Ω) i U
  have hφ : baseRepresentative U =ᵐ[
      domainMeasure (m + 1) (SobolevSpace.HalfSpace.upper (m + 1))] φ.1.toFun := by
    simpa [U, baseRepresentative, baseIndex_toList, iteratedPartialDeriv] using
      testFunctionToWkp_coordinate_ae (k := 1) (p := p) φ (baseIndex (m + 1) 1)
  have hφTarget : baseRepresentative U =ᵐ[domainMeasure (m + 1) E.target] φ.1.toFun :=
    ae_mono (Measure.restrict_mono
      (Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_subset_upper i) le_rfl) hφ
  have hreflect : baseRepresentative W =ᵐ[domainMeasure (m + 1) E.target]
      baseRepresentative U :=
    reflectedChartTargetCLM_base_agree_ae i U
  have htarget : baseRepresentative W =ᵐ[domainMeasure (m + 1) E.target] φ.1.toFun :=
    hreflect.trans hφTarget
  have hqmp : QuasiMeasurePreserving E
      (domainMeasure (m + 1) E.source) (domainMeasure (m + 1) E.target) :=
    WeakChangeOfVariables.quasiMeasurePreserving_partialHomeomorph
      (E := E)
      (by simpa [E, Boundary.C1ExtensionAtlas.Charts.chartOnΩ] using hΩ.chart_contDiff i)
      (by simpa [E, Boundary.C1ExtensionAtlas.Charts.chartOnΩ] using hΩ.chart_symm_contDiff i)
  have hcomp := (ae_restrict_iff' E.open_source.measurableSet).mp (hqmp.ae_eq_comp htarget)
  have hsource := (ae_restrict_iff' (hΩ.chart i).open_source.measurableSet).mp
    (preparedChartCLM_base_agree_ae i W)
  have hglobal : baseRepresentative (preparedChartCLM i W) =ᵐ[volume]
      preparedChartBaseRepresentative i W := by
    simpa [baseRepresentative, preparedChartCLM_apply_coe, domainMeasure] using
      preparedChartAmbient_base_apply_ae i W
  filter_upwards [ae_restrict_of_ae (s := Ω) hcomp,
    ae_restrict_of_ae (s := Ω) hsource, ae_restrict_of_ae (s := Ω) hglobal,
    ae_restrict_mem hΩ.isOpen.measurableSet] with x hxcomp hxsource hxglobal hxΩ
  change baseRepresentative (preparedChartCLM i W) x = chartTestFunctionPullback i φ x
  by_cases hx : x ∈ (hΩ.chart i).source
  · rw [hxsource hx, chartTestFunctionPullback_eq_on_source i φ hx]
    have hxE : x ∈ E.source := ⟨hx, hxΩ⟩
    exact congrArg ((targetSupportCutoff i).toFun (hΩ.chart i x) * ·) (hxcomp hxE)
  · rw [hxglobal]
    have hxL : x ∉ pullbackSupport (Ω := Ω) i :=
      fun h ↦ hx (pullbackSupport_subset_source i h)
    have hξ : (pullbackSupportCutoff i).toFun x = 0 :=
      image_eq_zero_of_notMem_tsupport fun h ↦
        hx (tsupport_pullbackSupportCutoff_subset_source i h)
    simp only [preparedChartBaseRepresentative, indicator_of_notMem hxL,
      chartTestFunctionPullback, hξ, zero_mul]

/-- The reconstructed restriction of a half-space test function belongs to `W^{1,p}_0(Ω)`. -/
theorem restrict_boundaryFromUpperCLM_testFunction_mem_Wkp0 (hp : p ≠ ∞) (i : Fin hΩ.N)
    (φ : TestFunctionOn (m + 1) (SobolevSpace.HalfSpace.upper (m + 1))) :
    restrictCLM hΩ.isOpen.measurableSet (subset_univ Ω)
      (boundaryFromUpperCLM (p := p) i (testFunctionToWkp φ)) ∈
      (wkp0SubmoduleOn (n := m + 1) (k := 1) (p := p) (Ω := Ω)).toSubmodule := by
  apply mem_Wkp0_of_compactSupport hp _ (chartTestFunctionPullback i φ)
  · exact (restrictCLM_apply_ae hΩ.isOpen.measurableSet (subset_univ Ω)
      (boundaryFromUpperCLM i (testFunctionToWkp φ)) (baseIndex (m + 1) 1)).trans
        (boundaryFromUpperCLM_testFunction_base_ae i φ)
  · exact (chartTestFunctionPullback_support i φ).1
  · exact (chartTestFunctionPullback_support i φ).2

/-- Reconstructing a half-space field in `W^{1,p}_0` through a C¹ chart and restricting
to the physical domain gives an element of `W^{1,p}_0(Ω)`. -/
theorem restrict_boundaryFromUpperCLM_mem_Wkp0 (hp : p ≠ ∞) (i : Fin hΩ.N)
    (u : W^{1,p}(SobolevSpace.HalfSpace.upper (m + 1)))
    (hu : u ∈ (wkp0SubmoduleOn (n := m + 1) (k := 1) (p := p)
      (Ω := SobolevSpace.HalfSpace.upper (m + 1))).toSubmodule) :
    restrictCLM hΩ.isOpen.measurableSet (subset_univ Ω) (boundaryFromUpperCLM i u) ∈
      (wkp0SubmoduleOn (n := m + 1) (k := 1) (p := p) (Ω := Ω)).toSubmodule := by
  let F := (restrictCLM (k := 1) (p := p) hΩ.isOpen.measurableSet (subset_univ Ω)).comp
    (boundaryFromUpperCLM (p := p) i)
  have hmap : MapsTo F
      (range (testFunctionToWkpLinear (n := m + 1) (k := 1) (p := p)
        (Ω := SobolevSpace.HalfSpace.upper (m + 1))))
      (wkp0SubmoduleOn (n := m + 1) (k := 1) (p := p) (Ω := Ω)) := by
    rintro _ ⟨φ, rfl⟩
    exact restrict_boundaryFromUpperCLM_testFunction_mem_Wkp0 hp i φ
  exact hmap.closure_left F.continuous
    (wkp0SubmoduleOn (n := m + 1) (k := 1) (p := p) (Ω := Ω)).isClosed' hu

end SobolevSpace.Trace.C1
