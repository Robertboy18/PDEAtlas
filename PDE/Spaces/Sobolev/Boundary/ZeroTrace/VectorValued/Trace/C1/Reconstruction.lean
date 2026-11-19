/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.C1.Flattening
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.VectorValued.Trace.C1.CompactSupport
public import PDE.Spaces.Sobolev.Extension.VectorValued.ZeroBoundary.Space

/-!
# Returning Banach-valued zero-boundary fields through C¹ charts

Zero extension of a half-space `W₀` class can be restricted to a chart target,
pulled back, and localized across the artificial chart edge. The auxiliary source cutoff
leaves the boundary partition factor already present in `localizedFlatten` unchanged.
All operators act on the Sobolev graphs and require only the C¹ atlas.
At finite exponent, compact interior support of returned test representatives and closure
give membership in the physical `W₀` space.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace Set
open scoped Distributions ENNReal Sobolev

namespace SobolevSpace.VectorValued.Trace.C1

open GraphSpace
open Boundary.C1ExtensionAtlas.DerivedCutoffs

variable {m : ℕ} {Ω : Opens ℝ^(m + 1)}
  [hΩ : Boundary.C1ExtensionAtlas (m + 1) (Ω : Set ℝ^(m + 1))]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Pull back a whole-space field and localize it to the physical domain using the
auxiliary source cutoff. Restriction and relative multiplication handle the chart edge. -/
def chartReturnWholeSpace (i : Fin hΩ.N) :
    W^{1,p}(ℝ^(m + 1); F) →L[ℝ] W^{1,p}(Ω; F) :=
  (interMultiplier (Ω := Ω)
    (V := ⟨(hΩ.chart i).source, (hΩ.chart i).open_source⟩)
    (pullbackSupportCutoff i) (tsupport_pullbackSupportCutoff_subset_source i)).comp
    ((VectorValued.restrictCLM (show
      (⟨(hΩ.chart i).source, (hΩ.chart i).open_source⟩ ⊓ Ω : Opens ℝ^(m + 1)) ≤
        ⟨(hΩ.chart i).source, (hΩ.chart i).open_source⟩ from inf_le_left)).comp
      ((WeakChangeOfVariables.pullbackCLM (k := 1)
        (hΩ.chart_contDiff i) (hΩ.chart_symm_contDiff i) (hΩ.chart_target_bounded i)).comp
        (VectorValued.restrictCLM (show
          (⟨(hΩ.chart i).target, (hΩ.chart i).open_target⟩ : Opens ℝ^(m + 1)) ≤ ⊤
          from le_top))))

private theorem chartReturnWholeSpace_base_ae (i : Fin hΩ.N)
    (U : W^{1,p}(ℝ^(m + 1); F)) {f : ℝ^(m + 1) → F}
    (hU : (U.val (baseIndex (m + 1) 1) : ℝ^(m + 1) → F)
      =ᵐ[domainMeasure (m + 1) univ] f) :
    ((chartReturnWholeSpace i U).val (baseIndex (m + 1) 1) : ℝ^(m + 1) → F)
      =ᵐ[domainMeasure (m + 1) Ω]
        fun x ↦ (pullbackSupportCutoff i).toFun x • f (hΩ.chart i x) := by
  let S : Opens ℝ^(m + 1) := ⟨(hΩ.chart i).source, (hΩ.chart i).open_source⟩
  let T : Opens ℝ^(m + 1) := ⟨(hΩ.chart i).target, (hΩ.chart i).open_target⟩
  let R := VectorValued.restrictCLM (show T ≤ ⊤ from le_top) U
  let P := WeakChangeOfVariables.pullbackCLM (k := 1)
    (hΩ.chart_contDiff i) (hΩ.chart_symm_contDiff i) (hΩ.chart_target_bounded i) R
  have hR := VectorValued.restrictCLM_apply_ae (show T ≤ ⊤ from le_top)
    U (baseIndex (m + 1) 1)
  have hT := ae_mono (Measure.restrict_mono
    (subset_univ (hΩ.chart i).target) le_rfl) hU
  have hcomp := (SobolevSpace.WeakChangeOfVariables.quasiMeasurePreserving_partialHomeomorph
    (hΩ.chart_contDiff i) (hΩ.chart_symm_contDiff i)).ae_eq_comp (hR.trans hT)
  have hP := WeakChangeOfVariables.pullbackCLM_base_ae (k := 1)
    (hΩ.chart_contDiff i) (hΩ.chart_symm_contDiff i) (hΩ.chart_target_bounded i) R
  have hS := VectorValued.restrictCLM_apply_ae
    (show S ⊓ Ω ≤ S from inf_le_left) P (baseIndex (m + 1) 1)
  exact interMultiplier_base_ae (Ω := Ω) (V := S)
    (pullbackSupportCutoff i) (tsupport_pullbackSupportCutoff_subset_source i) _
    (hS.trans (ae_mono (Measure.restrict_mono
      (inter_subset_left : (S : Set ℝ^(m + 1)) ∩ Ω ⊆ S) le_rfl) (hP.trans hcomp)))

/-- Return a half-space zero-boundary class through one C¹ chart. The auxiliary
source cutoff extends across the artificial chart edge without inserting a partition factor. -/
def chartReturn (i : Fin hΩ.N) :
    W₀^{1,p}(⟨ℝ^(m + 1)₊, HalfSpace.isOpen_upper (m + 1)⟩; F) →L[ℝ]
      W^{1,p}(Ω; F) :=
  (chartReturnWholeSpace (p := p) (F := F) i).comp
    (zeroExtension (k := 1) (p := p)
      (Ω := ⟨ℝ^(m + 1)₊, HalfSpace.isOpen_upper (m + 1)⟩) (F := F)).toContinuousLinearMap

/-- The returned base is the chart composition multiplied by the auxiliary source cutoff.
The representative is only required to agree almost everywhere on the half-space. -/
theorem chartReturn_base_ae (i : Fin hΩ.N)
    (U : W₀^{1,p}(⟨ℝ^(m + 1)₊, HalfSpace.isOpen_upper (m + 1)⟩; F))
    {f : ℝ^(m + 1) → F}
    (hU : (U.val.val (baseIndex (m + 1) 1) : ℝ^(m + 1) → F)
      =ᵐ[domainMeasure (m + 1) ℝ^(m + 1)₊] f) :
    ((chartReturn i U).val (baseIndex (m + 1) 1) : ℝ^(m + 1) → F)
      =ᵐ[domainMeasure (m + 1) Ω]
        fun x ↦ (pullbackSupportCutoff i).toFun x • f (hΩ.chart i x) := by
  have hzero := zeroExtension_coordinate_ae U (baseIndex (m + 1) 1)
  simp only [domainMeasure, Opens.coe_top, Measure.restrict_univ] at hzero
  have hind := (ae_eq_restrict_iff_indicator_ae_eq
    (HalfSpace.isOpen_upper (m + 1)).measurableSet).mp hU
  have hf : ((zeroExtension U).val (baseIndex (m + 1) 1) : ℝ^(m + 1) → F)
      =ᵐ[domainMeasure (m + 1) univ] (ℝ^(m + 1)₊).indicator f := by
    simpa only [domainMeasure, Opens.coe_top, Measure.restrict_univ] using hzero.trans hind
  have hbase := chartReturnWholeSpace_base_ae i (zeroExtension U) hf
  filter_upwards [hbase, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
  change (chartReturnWholeSpace i (zeroExtension U)).val (baseIndex (m + 1) 1) x = _
  rw [hx]
  by_cases hxS : x ∈ (hΩ.chart i).source
  · rw [indicator_of_mem ((hΩ.chart_mem_iff_upper i x hxS).mp hxΩ)]
  · have hξ : (pullbackSupportCutoff i).toFun x = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun h ↦ hxS (tsupport_pullbackSupportCutoff_subset_source i h))
    simp only [hξ, zero_smul]

/-- A returned half-space test function has its C¹ chart pullback as base representative. -/
theorem chartReturn_testFunction_base_ae (i : Fin hΩ.N)
    (φ : 𝓓(⟨ℝ^(m + 1)₊, HalfSpace.isOpen_upper (m + 1)⟩, F)) :
    ((chartReturn i (testFunctionToWkp0 (k := 1) (p := p) φ)).val
      (baseIndex (m + 1) 1) : ℝ^(m + 1) → F)
      =ᵐ[domainMeasure (m + 1) Ω]
        fun x ↦ (pullbackSupportCutoff i).toFun x • φ (hΩ.chart i x) :=
  chartReturn_base_ae i _ (testFunctionToWkp_base_ae φ)

omit [Fact (1 ≤ p)] [CompleteSpace F] in
/-- The auxiliary source cutoff makes the returned test representative compactly
supported inside the physical domain. The chart pullback need not be smooth. -/
theorem chartReturn_testFunction_support (i : Fin hΩ.N)
    (φ : 𝓓(⟨ℝ^(m + 1)₊, HalfSpace.isOpen_upper (m + 1)⟩, F)) :
    HasCompactSupport (fun x ↦ (pullbackSupportCutoff i).toFun x • φ (hΩ.chart i x)) ∧
      tsupport (fun x ↦ (pullbackSupportCutoff i).toFun x • φ (hΩ.chart i x)) ⊆ Ω := by
  let ξ := pullbackSupportCutoff (Ω := (Ω : Set ℝ^(m + 1))) i
  let K := tsupport ξ.toFun ∩ (hΩ.chart i) ⁻¹' tsupport (φ : ℝ^(m + 1) → F)
  have hclosed : IsClosed K := (isClosed_tsupport _).inter
    ((isClosed_tsupport _).preimage (hΩ.chart_contDiff i).continuous)
  have hs : tsupport (fun x ↦ ξ.toFun x • φ (hΩ.chart i x)) ⊆ K := by
    apply closure_minimal _ hclosed
    intro x hx
    refine ⟨subset_tsupport _ ?_, subset_tsupport _ ?_⟩
    · intro hzero
      exact hx (by simp only [hzero, zero_smul])
    · intro hzero
      exact hx (by simp only [hzero, smul_zero])
  refine ⟨ξ.hasCompactSupport.smul_right, ?_⟩
  intro x hx
  have hxK := hs hx
  exact (hΩ.chart_mem_iff_upper i x
    (tsupport_pullbackSupportCutoff_subset_source i hxK.1)).mpr
      (φ.tsupport_subset hxK.2)

/-- Returning an interior half-space test function gives a physical zero-boundary
field, using compact interior support rather than smoothness of the chart pullback. -/
theorem chartReturn_testFunction_mem_Wkp0 (hp : p ≠ ∞) (i : Fin hΩ.N)
    (φ : 𝓓(⟨ℝ^(m + 1)₊, HalfSpace.isOpen_upper (m + 1)⟩, F)) :
    chartReturn i (testFunctionToWkp0 (k := 1) (p := p) φ) ∈
      (wkp0SubmoduleOn (k := 1) (p := p) (Ω := Ω) (F := F)).toSubmodule :=
  mem_Wkp0_of_compactSupport hp _ _ (chartReturn_testFunction_base_ae i φ)
    (chartReturn_testFunction_support i φ).1 (chartReturn_testFunction_support i φ).2

/-- Chart return preserves zero-boundary membership at every finite exponent
at least one. Density is used only in the supported-test closure on the half-space. -/
theorem chartReturn_mem_Wkp0 (hp : p ≠ ∞) (i : Fin hΩ.N)
    (U : W₀^{1,p}(⟨ℝ^(m + 1)₊, HalfSpace.isOpen_upper (m + 1)⟩; F)) :
    chartReturn i U ∈
      (wkp0SubmoduleOn (k := 1) (p := p) (Ω := Ω) (F := F)).toSubmodule := by
  have hclosed : IsClosed
      {V : W₀^{1,p}(⟨ℝ^(m + 1)₊, HalfSpace.isOpen_upper (m + 1)⟩; F) |
        chartReturn i V ∈
          (wkp0SubmoduleOn (k := 1) (p := p) (Ω := Ω) (F := F)).toSubmodule} :=
    (wkp0SubmoduleOn (k := 1) (p := p) (Ω := Ω) (F := F)).isClosed'.preimage
      (chartReturn i).continuous
  refine closure_minimal ?_ hclosed
    (denseRange_testFunctionToWkp0Linear (k := 1) (p := p)
      (Ω := ⟨ℝ^(m + 1)₊, HalfSpace.isOpen_upper (m + 1)⟩) (F := F) U)
  rintro _ ⟨φ, rfl⟩
  exact chartReturn_testFunction_mem_Wkp0 hp i φ

/-- Returning a localized flat piece reconstructs exactly one physical boundary partition
factor. The flat piece must belong to the supported-test closure. -/
theorem chartReturn_localizedFlatten (i : Fin hΩ.N) (U : W^{1,p}(Ω; F))
    (hflat : localizedFlatten i U ∈
      (wkp0SubmoduleOn (k := 1) (p := p)
        (Ω := ⟨ℝ^(m + 1)₊, HalfSpace.isOpen_upper (m + 1)⟩) (F := F)).toSubmodule) :
    chartReturn i ⟨localizedFlatten i U, hflat⟩ =
      compactSmoothMultiplierCLM (hΩ.boundaryCutoff i).toFun
        (hΩ.boundaryCutoff i).contDiff (hΩ.boundaryCutoff i).hasCompactSupport U := by
  apply WkpSpaceOn.ext_of_base_ae
  have hreturn := chartReturn_base_ae i ⟨localizedFlatten i U, hflat⟩
    (localizedFlatten_base_ae i U Filter.EventuallyEq.rfl)
  have hmultiplier := compactSmoothMultiplierCLM_base_ae (hΩ.boundaryCutoff i).toFun
    (hΩ.boundaryCutoff i).contDiff (hΩ.boundaryCutoff i).hasCompactSupport U
  filter_upwards [hreturn, hmultiplier] with x hxreturn hxmultiplier
  rw [hxreturn, hxmultiplier]
  by_cases hxS : x ∈ (hΩ.chart i).source
  · rw [flattenedClassicalPiece_chart_apply i _ hxS]
    by_cases hψ : (hΩ.boundaryCutoff i).toFun x = 0
    · simp only [hψ, zero_smul, smul_zero]
    · have hη := targetSupportCutoff_eq_one_on_boundarySupportInTarget i
        (hΩ.chart i x) ⟨x, subset_tsupport _ hψ, rfl⟩
      have htarget : hΩ.chart i x ∈ targetCutoffSupport (Ω := (Ω : Set ℝ^(m + 1))) i :=
        subset_tsupport _ (by
          change (targetSupportCutoff i).toFun (hΩ.chart i x) ≠ 0
          rw [hη]
          exact one_ne_zero)
      have hξ := pullbackSupportCutoff_eq_one_on_pullbackSupport i x
        ⟨hΩ.chart i x, htarget, (hΩ.chart i).left_inv hxS⟩
      rw [hξ, one_smul]
  · have hξ : (pullbackSupportCutoff i).toFun x = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun h ↦ hxS (tsupport_pullbackSupportCutoff_subset_source i h))
    have hψ : (hΩ.boundaryCutoff i).toFun x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hxS (hΩ.boundaryCutoff_support i h))
    simp only [hξ, hψ, zero_smul]

/-- A localized flattening in the half-space test-function closure reconstructs
the corresponding physical boundary partition piece in the physical closure. -/
theorem compactSmoothMultiplierCLM_boundary_mem_Wkp0_of_localizedFlatten
    (hp : p ≠ ∞) (i : Fin hΩ.N) (U : W^{1,p}(Ω; F))
    (hflat : localizedFlatten i U ∈
      (wkp0SubmoduleOn (k := 1) (p := p)
        (Ω := ⟨ℝ^(m + 1)₊, HalfSpace.isOpen_upper (m + 1)⟩) (F := F)).toSubmodule) :
    compactSmoothMultiplierCLM (hΩ.boundaryCutoff i).toFun
        (hΩ.boundaryCutoff i).contDiff (hΩ.boundaryCutoff i).hasCompactSupport U ∈
      (wkp0SubmoduleOn (k := 1) (p := p) (Ω := Ω) (F := F)).toSubmodule := by
  rw [← chartReturn_localizedFlatten i U hflat]
  exact chartReturn_mem_Wkp0 hp i _

end SobolevSpace.VectorValued.Trace.C1
