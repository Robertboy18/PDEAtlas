/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.C1.Naturality
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.VectorValued.Trace.HalfSpaceConverse
import PDE.Spaces.Sobolev.Boundary.Trace.C1.MeasureClass

/-!
# Localization of a vanishing Banach-valued physical trace

Each physical chart contribution is the boundary cutoff times the surface trace.
A vanishing physical trace therefore gives zero trace in each flattened chart. The
transfer to flat surface measure uses the trace's support in the chart target and
absolute continuity of the chart reference measure with respect to physical surface
measure. The half-space converse then gives membership in `W₀^{1,p}`.

The codomain is any real Banach space. Finite exponents include one, the boundary
dimension may be zero, and the domain may be empty.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued.Trace.C1

open GraphSpace Boundary.Geometry.SurfaceMeasure
open Boundary.C1ExtensionAtlas.DerivedCutoffs
open SobolevSpace.Trace.C1 (chartPhysicalization_apply_ae chartBoundaryPatch
  chartBoundaryReferenceMeasure_absolutelyContinuous_surfaceMeasure
  chartBoundaryParameterDomain chartBoundaryParametrization
  contDiff_chartBoundaryParametrization isOpen_chartBoundaryParameterDomain
  image_chartBoundaryParametrization)

variable {m : ℕ} {Ω : Opens ℝ^(m + 1)}
  [hΩ : Boundary.C1ExtensionAtlas (m + 1) (Ω : Set ℝ^(m + 1))]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

/-- The physical trace of a chart piece is its boundary cutoff times the global trace. -/
theorem localPhysicalTrace_eq_cutoff_smul_ae (hp : 1 ≤ p) (i : Fin hΩ.N)
    (U : W^{1,ENNReal.ofReal p}(Ω; F)) :
    (localPhysicalTrace p hp i U : ℝ^(m + 1) → F) =ᵐ[surfaceMeasure (Ω : Set ℝ^(m + 1))]
      fun x ↦ (hΩ.boundaryCutoff i).toFun x • traceLp p hp U x := by
  let ψ := hΩ.boundaryCutoff i
  have hψ : MemLp ψ.toFun ∞ (surfaceMeasure (Ω : Set ℝ^(m + 1))) :=
    ψ.contDiff.continuous.memLp_top_of_hasCompactSupport ψ.hasCompactSupport _
  let M : Lp F (ENNReal.ofReal p) (surfaceMeasure (Ω : Set ℝ^(m + 1))) →L[ℝ]
      Lp F (ENNReal.ofReal p) (surfaceMeasure (Ω : Set ℝ^(m + 1))) :=
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).holderL
      (surfaceMeasure (Ω : Set ℝ^(m + 1))) ∞ (ENNReal.ofReal p) (ENNReal.ofReal p)
      (hψ.toLp ψ.toFun)
  have hM (g : Lp F (ENNReal.ofReal p) (surfaceMeasure (Ω : Set ℝ^(m + 1)))) :
      (M g : ℝ^(m + 1) → F) =ᵐ[surfaceMeasure (Ω : Set ℝ^(m + 1))]
        fun x ↦ ψ.toFun x • g x := by
    filter_upwards [(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).coeFn_holder
      (r := ENNReal.ofReal p) (hψ.toLp ψ.toFun) g, hψ.coeFn_toLp] with x hx hψx
    change M g x = (hψ.toLp ψ.toFun) x • g x at hx
    rw [hψx] at hx
    exact hx
  have heq (V : W^{1,ENNReal.ofReal p}(Ω; F)) :
      localPhysicalTrace p hp i V = M (traceLp p hp V) := by
    refine (dense_compact_smooth ENNReal.ofReal_ne_top).induction ?_
      (isClosed_eq (localPhysicalTrace p hp i).continuous
        (M.continuous.comp (traceLp p hp).continuous)) V
    rintro V ⟨f, hf, _, hbase⟩
    have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
    have hlocal :
        (localPhysicalTrace p hp i V : ℝ^(m + 1) → F)
          =ᵐ[surfaceMeasure (Ω : Set ℝ^(m + 1))]
            fun x ↦ (hΩ.boundaryCutoff i).toFun x • f x := by
      rw [localPhysicalTrace_c1 hp i V hf1 hbase]
      exact chartPhysicalization_flattenedClassicalPiece (ENNReal.ofReal p) i hf1
    apply Lp.ext
    filter_upwards [hlocal, hM (traceLp p hp V), traceLp_coeFn_ae hp V hf1 hbase]
      with x hx hy hz
    rw [hx, hy, hz]
  rw [heq]
  exact hM _

/-- Zero global physical trace forces every physical chart contribution to vanish. -/
theorem localPhysicalTrace_eq_zero_of_traceLp_eq_zero (hp : 1 ≤ p) (i : Fin hΩ.N)
    (U : W^{1,ENNReal.ofReal p}(Ω; F)) (hU : traceLp p hp U = 0) :
    localPhysicalTrace p hp i U = 0 := by
  apply Lp.ext
  filter_upwards [localPhysicalTrace_eq_cutoff_smul_ae hp i U,
    Lp.coeFn_zero F (ENNReal.ofReal p) (surfaceMeasure (Ω : Set ℝ^(m + 1)))]
    with x hx hz
  rw [hU, hz, Pi.zero_apply, smul_zero] at hx
  exact hx.trans hz.symm

/-- The flattened trace is zero off the target of its boundary chart. -/
theorem localFlatTrace_eq_zero_off_target (hp : 1 ≤ p) (i : Fin hΩ.N)
    (U : W^{1,ENNReal.ofReal p}(Ω; F)) :
    (liftLp (ENNReal.ofReal p)
      (HalfSpace.traceLp m p hp (localizedFlatten i U)) : ℝ^(m + 1) → F)
        =ᵐ[(flatSurfaceMeasure (n := m)).restrict (hΩ.chart i).targetᶜ] 0 := by
  let G : W^{1,ENNReal.ofReal p}(Ω; F) →L[ℝ]
      Lp F (ENNReal.ofReal p) (flatSurfaceMeasure (n := m)) :=
    (liftLp (ENNReal.ofReal p)).toContinuousLinearMap.comp
      ((HalfSpace.traceLp m p hp).comp (localizedFlatten i))
  let R : Lp F (ENNReal.ofReal p) (flatSurfaceMeasure (n := m)) →L[ℝ]
      Lp F (ENNReal.ofReal p)
        ((flatSurfaceMeasure (n := m)).restrict (hΩ.chart i).targetᶜ) :=
    Lp.restrictionCLMOfLE Measure.restrict_le_self
  have heq (V : W^{1,ENNReal.ofReal p}(Ω; F)) : R (G V) = 0 := by
    refine (dense_compact_smooth ENNReal.ofReal_ne_top).induction ?_
      (isClosed_eq (R.continuous.comp G.continuous) continuous_const) V
    rintro V ⟨f, hf, _, hbase⟩
    have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
    have hflat : (G V : ℝ^(m + 1) → F) =ᵐ[flatSurfaceMeasure (n := m)]
        flattenedClassicalPiece i f := by
      change (liftLp (ENNReal.ofReal p)
        (HalfSpace.traceLp m p hp (localizedFlatten i V)) : ℝ^(m + 1) → F) =ᵐ[_] _
      rw [HalfSpace.traceLp_c1 hp _ (flattenedClassicalPiece_contDiff i hf1)
        (flattenedClassicalPiece_hasCompactSupport i f) (localizedFlatten_base_ae i V hbase),
        liftLp_flattenedClassicalPiece (ENNReal.ofReal p) i hf1]
      exact (flattenedClassicalPiece_memLp (ENNReal.ofReal p) i hf1).coeFn_toLp
    apply Lp.ext
    filter_upwards [Lp.restrictionCLMOfLE_apply_ae Measure.restrict_le_self (G V),
      ae_restrict_of_ae (s := (hΩ.chart i).targetᶜ) hflat,
      ae_restrict_mem (hΩ.chart i).open_target.measurableSet.compl,
      Lp.coeFn_zero F (ENNReal.ofReal p)
        ((flatSurfaceMeasure (n := m)).restrict (hΩ.chart i).targetᶜ)]
      with x hx hy hz hzero
    refine hx.trans (hy.trans (Eq.trans ?_ hzero.symm))
    have hη : (targetSupportCutoff i).toFun x = 0 :=
      image_eq_zero_of_notMem_tsupport fun h ↦
        hz (tsupport_targetSupportCutoff_subset_target i h)
    simp [flattenedClassicalPiece, hη]
  have hR := Lp.restrictionCLMOfLE_apply_ae
    (Measure.restrict_le_self (s := (hΩ.chart i).targetᶜ)) (G U)
  change (R (G U) : ℝ^(m + 1) → F) =ᵐ[_] _ at hR
  rw [heq U] at hR
  exact hR.symm.trans (Lp.coeFn_zero _ _ _)

/-- A vanishing physical trace gives zero flat trace in every localized chart.
The support statement off the chart target is needed because physicalization discards
flat data outside that target. -/
theorem localFlatTrace_eq_zero_of_traceLp_eq_zero (hp : 1 ≤ p) (i : Fin hΩ.N)
    (U : W^{1,ENNReal.ofReal p}(Ω; F)) (hU : traceLp p hp U = 0) :
    liftLp (ENNReal.ofReal p)
      (HalfSpace.traceLp m p hp (localizedFlatten i U)) = 0 := by
  let g := liftLp (ENNReal.ofReal p)
    (HalfSpace.traceLp m p hp (localizedFlatten i U))
  have hphysical :
      (chartBoundaryPatch i).indicator (fun x ↦ g (hΩ.chart i x))
        =ᵐ[surfaceMeasure (Ω : Set ℝ^(m + 1))] 0 := by
    have h := chartPhysicalization_apply_ae (ENNReal.ofReal p) i g
    change (localPhysicalTrace p hp i U : ℝ^(m + 1) → F) =ᵐ[_] _ at h
    rw [localPhysicalTrace_eq_zero_of_traceLp_eq_zero hp i U hU] at h
    exact h.symm.trans (Lp.coeFn_zero _ _ _)
  have hreference :=
    (chartBoundaryReferenceMeasure_absolutelyContinuous_surfaceMeasure i).ae_eq hphysical
  have hparameter := ae_of_ae_map
    (contDiff_chartBoundaryParametrization (m := m) (Ω := Ω) i).continuous.measurable.aemeasurable
    hreference
  have hon : ∀ᵐ y ∂(volume : Measure (ℝ^m)).restrict (chartBoundaryParameterDomain i),
      g (flatEmbedding y) = 0 := by
    filter_upwards [hparameter,
      ae_restrict_mem (isOpen_chartBoundaryParameterDomain (m := m) (Ω := Ω) i).measurableSet]
      with y hy hyD
    have hx : chartBoundaryParametrization i y ∈ chartBoundaryPatch (Ω := Ω) i := by
      change chartBoundaryParametrization i y ∈ (hΩ.chart i).source ∩ frontier (Ω : Set _)
      rw [← image_chartBoundaryParametrization i]
      exact mem_image_of_mem _ hyD
    rw [indicator_of_mem hx] at hy
    simpa only [chartBoundaryParametrization, (hΩ.chart i).right_inv hyD,
      Pi.zero_apply] using hy
  have hon' := (ae_restrict_iff'
    (isOpen_chartBoundaryParameterDomain (m := m) (Ω := Ω) i).measurableSet).mp hon
  have hoff := (ae_restrict_iff' (hΩ.chart i).open_target.measurableSet.compl).mp
    (localFlatTrace_eq_zero_off_target hp i U)
  change ∀ᵐ x ∂flatSurfaceMeasure, x ∈ (hΩ.chart i).targetᶜ → g x = 0 at hoff
  have hoffMap : ∀ᵐ x ∂Measure.map (flatEmbedding (n := m)) volume,
      x ∈ (hΩ.chart i).targetᶜ → g x = 0 := by
    simpa only [map_flatEmbedding_volume] using hoff
  have hoff' := ae_of_ae_map (isometry_flatEmbedding (n := m)).continuous.measurable.aemeasurable
    hoffMap
  have hzero : ∀ᵐ y ∂(volume : Measure (ℝ^m)), g (flatEmbedding y) = 0 := by
    filter_upwards [hon', hoff'] with y hy hz
    by_cases ht : flatEmbedding y ∈ (hΩ.chart i).target
    · exact hy ht
    · exact hz ht
  apply Lp.ext
  apply Filter.EventuallyEq.trans _ (Lp.coeFn_zero _ _ _).symm
  change ∀ᵐ x ∂flatSurfaceMeasure, g x = 0
  have hzeroMap := (ae_map_iff
    (isometry_flatEmbedding (n := m)).continuous.measurable.aemeasurable
    ((Lp.stronglyMeasurable g).measurableSet_eq_fun stronglyMeasurable_const)).mpr hzero
  simpa only [map_flatEmbedding_volume] using hzeroMap

/-- Each localized flattening of a physical trace-zero function lies in the
closure of Banach-valued test functions supported inside the half-space. -/
theorem localizedFlatten_mem_Wkp0_of_traceLp_eq_zero (hp : 1 ≤ p) (i : Fin hΩ.N)
    (U : W^{1,ENNReal.ofReal p}(Ω; F)) (hU : traceLp p hp U = 0) :
    localizedFlatten i U ∈
      (wkp0SubmoduleOn (k := 1) (p := ENNReal.ofReal p)
        (Ω := ⟨ℝ^(m + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (m + 1)⟩)
        (F := F)).toSubmodule := by
  apply HalfSpace.mem_Wkp0_of_traceLp_eq_zero hp
  apply (liftLp (ENNReal.ofReal p)).injective
  rw [map_zero]
  exact localFlatTrace_eq_zero_of_traceLp_eq_zero hp i U hU

end SobolevSpace.VectorValued.Trace.C1
