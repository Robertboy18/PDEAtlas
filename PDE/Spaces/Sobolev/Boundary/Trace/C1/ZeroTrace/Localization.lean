/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.FiniteExponentOperator
public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.ZeroTrace
import PDE.Spaces.Sobolev.Boundary.Trace.C1.MeasureClass

/-!
# Localization of a vanishing trace

The physical trace of each chart piece is the boundary cutoff times the global trace.
Consequently, a vanishing global trace gives a vanishing trace in every flattened chart.
The latter implication uses both the support of the flattened piece and the equivalence
of chart area and intrinsic surface measure; it is not an additional atlas hypothesis.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Trace.C1

open MeasureTheory Set
open scoped ENNReal Sobolev
open Boundary.Geometry.SurfaceMeasure

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
variable (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]

/-- Each physical chart contribution is the corresponding cutoff times the global trace. -/
theorem localPhysicalTraceLp_eq_cutoff_mul_ae (i : Fin hΩ.N)
    (u : W^{1,ENNReal.ofReal p}(Ω)) :
    (localPhysicalTraceLp p i u : ℝ^(m + 1) → ℝ) =ᵐ[surfaceMeasure Ω]
      fun x ↦ (hΩ.boundaryCutoff i).toFun x * traceLp p u x := by
  let ψ := hΩ.boundaryCutoff i
  have hψ : MemLp ψ.toFun ∞ (surfaceMeasure Ω) :=
    ψ.contDiff.continuous.memLp_top_of_hasCompactSupport ψ.hasCompactSupport _
  let M : Lp ℝ (ENNReal.ofReal p) (surfaceMeasure Ω) →L[ℝ]
      Lp ℝ (ENNReal.ofReal p) (surfaceMeasure Ω) :=
    (ContinuousLinearMap.mul ℝ ℝ).holderL
      (surfaceMeasure Ω) ∞ (ENNReal.ofReal p) (ENNReal.ofReal p) (hψ.toLp ψ.toFun)
  have hM (g : Lp ℝ (ENNReal.ofReal p) (surfaceMeasure Ω)) :
      (M g : ℝ^(m + 1) → ℝ) =ᵐ[surfaceMeasure Ω]
        fun x ↦ ψ.toFun x * g x := by
    filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder
      (r := ENNReal.ofReal p) (hψ.toLp ψ.toFun) g, hψ.coeFn_toLp] with x hx hψx
    change M g x = (hψ.toLp ψ.toFun) x * g x at hx
    rw [hψx] at hx
    exact hx
  have heq : localPhysicalTraceLp p i = M.comp (traceLp p) := by
    apply DFunLike.coe_injective
    apply (denseRange_globalTestFunctionToDomainW1pLinear
      (m := m) (Ω := Ω) (ENNReal.ofReal p) ENNReal.ofReal_ne_top).equalizer
      (localPhysicalTraceLp p i).continuous (M.comp (traceLp p)).continuous
    funext φ
    change localPhysicalTraceLp p i
      (globalTestFunctionToDomainW1pLinear (ENNReal.ofReal p) φ) =
      M (traceLp p (globalTestFunctionToDomainW1pLinear (ENNReal.ofReal p) φ))
    rw [traceLp_classical p φ]
    apply Lp.ext
    have hright := hM (traceLp p
      (globalTestFunctionToDomainW1pLinear (ENNReal.ofReal p) φ))
    rw [traceLp_classical p φ] at hright
    filter_upwards [localPhysicalTraceLp_classical_apply_ae p i φ, hright,
      globalTestFunctionBoundaryLpLinear_apply_ae (ENNReal.ofReal p) φ,
      ae_restrict_mem (isClosed_frontier (s := Ω)).measurableSet] with x hx hy hz hΩx
    rw [hx, hy, hz]
    by_cases hs : x ∈ (hΩ.chart i).source
    · rw [indicator_of_mem (show x ∈ chartBoundaryPatch i from ⟨hs, hΩx⟩)]
    · rw [indicator_of_notMem (show x ∉ chartBoundaryPatch i from fun h ↦ hs h.1)]
      have hzero : ψ.toFun x = 0 :=
        image_eq_zero_of_notMem_tsupport fun h ↦ hs (hΩ.boundaryCutoff_support i h)
      simp [hzero]
  rw [heq]
  exact hM _

/-- A zero global trace has zero physical contribution in every boundary chart. -/
theorem localPhysicalTraceLp_eq_zero_of_traceLp_eq_zero (i : Fin hΩ.N)
    (u : W^{1,ENNReal.ofReal p}(Ω))
    (hu : traceLp p u = 0) :
    localPhysicalTraceLp p i u = 0 := by
  apply Lp.ext
  filter_upwards [localPhysicalTraceLp_eq_cutoff_mul_ae p i u,
    Lp.coeFn_zero ℝ (ENNReal.ofReal p) (surfaceMeasure Ω)] with x hx hz
  rw [hu, hz, Pi.zero_apply, mul_zero] at hx
  change (0 : Lp ℝ (ENNReal.ofReal p) (surfaceMeasure Ω)) x = (0 : ℝ) at hz
  exact hx.trans hz.symm

/-- The flattened trace vanishes away from its chart target. -/
theorem localFlatTraceLp_eq_zero_off_target (i : Fin hΩ.N)
    (u : W^{1,ENNReal.ofReal p}(Ω)) :
    (localFlatTraceLp p i u : ℝ^(m + 1) → ℝ) =ᵐ[
      (flatSurfaceMeasure (n := m)).restrict (hΩ.chart i).targetᶜ] 0 := by
  let R : Lp ℝ (ENNReal.ofReal p) (flatSurfaceMeasure (n := m)) →L[ℝ]
      Lp ℝ (ENNReal.ofReal p)
        ((flatSurfaceMeasure (n := m)).restrict (hΩ.chart i).targetᶜ) :=
    Lp.restrictionCLMOfLE Measure.restrict_le_self
  have heq : R.comp (localFlatTraceLp p i) = 0 := by
    apply DFunLike.coe_injective
    apply (denseRange_globalTestFunctionToDomainW1pLinear
      (m := m) (Ω := Ω) (ENNReal.ofReal p) ENNReal.ofReal_ne_top).equalizer
      (R.comp (localFlatTraceLp p i)).continuous continuous_const
    funext φ
    change R (localFlatTraceLp p i
      (globalTestFunctionToDomainW1pLinear (ENNReal.ofReal p) φ)) = 0
    apply Lp.ext
    have hflat := ae_restrict_of_ae (s := (hΩ.chart i).targetᶜ)
      (localFlatTraceLp_classical_apply_ae p i φ)
    filter_upwards [Lp.restrictionCLMOfLE_apply_ae Measure.restrict_le_self
        (localFlatTraceLp p i
          (globalTestFunctionToDomainW1pLinear (ENNReal.ofReal p) φ)),
      hflat, ae_restrict_mem (hΩ.chart i).open_target.measurableSet.compl,
      Lp.coeFn_zero ℝ (ENNReal.ofReal p)
        ((flatSurfaceMeasure (n := m)).restrict (hΩ.chart i).targetᶜ)] with
      x hx hy hz hzero
    refine hx.trans (hy.trans ?_)
    refine Eq.trans ?_ hzero.symm
    have hη : (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff i).toFun x = 0 :=
      image_eq_zero_of_notMem_tsupport fun h ↦
        hz (Boundary.C1ExtensionAtlas.DerivedCutoffs.tsupport_targetSupportCutoff_subset_target i h)
    simp [flattenedClassicalPiece, hη]
  have hR := Lp.restrictionCLMOfLE_apply_ae
    (Measure.restrict_le_self (s := (hΩ.chart i).targetᶜ))
    (localFlatTraceLp p i u)
  have hRu : R (localFlatTraceLp p i u) = 0 :=
    DFunLike.congr_fun heq u
  change (R (localFlatTraceLp p i u) : ℝ^(m + 1) → ℝ) =ᵐ[_] _ at hR
  rw [hRu] at hR
  exact hR.symm.trans (Lp.coeFn_zero _ _ _)

/-- Vanishing of the geometric trace forces vanishing of every flattened trace. -/
theorem localFlatTraceLp_eq_zero_of_traceLp_eq_zero (i : Fin hΩ.N)
    (u : W^{1,ENNReal.ofReal p}(Ω))
    (hu : traceLp p u = 0) :
    localFlatTraceLp p i u = 0 := by
  let g := localFlatTraceLp p i u
  have hphysical :
      (chartBoundaryPatch i).indicator (fun x ↦ g (hΩ.chart i x)) =ᵐ[
        surfaceMeasure Ω] 0 := by
    have h := localPhysicalTraceLp_apply_ae p i u
    rw [localPhysicalTraceLp_eq_zero_of_traceLp_eq_zero p i u hu] at h
    exact h.symm.trans (Lp.coeFn_zero _ _ _)
  have hreference := (chartBoundaryReferenceMeasure_absolutelyContinuous_surfaceMeasure i).ae_eq
    hphysical
  have hparameter := ae_of_ae_map
    (contDiff_chartBoundaryParametrization (m := m) (Ω := Ω) i).continuous.measurable.aemeasurable
    hreference
  have hon : ∀ᵐ y ∂(volume : Measure (ℝ^m)).restrict (chartBoundaryParameterDomain i),
      g (flatEmbedding y) = 0 := by
    filter_upwards [hparameter,
      ae_restrict_mem (isOpen_chartBoundaryParameterDomain (m := m) (Ω := Ω) i).measurableSet]
      with y hy hyD
    have hx : chartBoundaryParametrization i y ∈ chartBoundaryPatch (Ω := Ω) i := by
      change chartBoundaryParametrization i y ∈ (hΩ.chart i).source ∩ frontier Ω
      rw [← image_chartBoundaryParametrization i]
      exact mem_image_of_mem _ hyD
    rw [indicator_of_mem hx] at hy
    simpa only [chartBoundaryParametrization, (hΩ.chart i).right_inv hyD,
      Pi.zero_apply] using hy
  have hon' := (ae_restrict_iff'
    (isOpen_chartBoundaryParameterDomain (m := m) (Ω := Ω) i).measurableSet).mp hon
  have hoff := (ae_restrict_iff' (hΩ.chart i).open_target.measurableSet.compl).mp
    (localFlatTraceLp_eq_zero_off_target p i u)
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
    (measurableSet_eq_fun (Lp.stronglyMeasurable g).measurable measurable_const)).mpr hzero
  simpa only [map_flatEmbedding_volume] using hzeroMap

/-- Each flattened chart piece of a trace-zero field belongs to the closure of the
half-space test functions. -/
theorem flattenCLM_mem_Wkp0_of_traceLp_eq_zero (i : Fin hΩ.N)
    (u : W^{1,ENNReal.ofReal p}(Ω))
    (hu : traceLp p u = 0) :
    Extension.C1.BoundaryPiece.flattenCLM (p := ENNReal.ofReal p) i u ∈
      (GraphSpace.wkp0SubmoduleOn (n := m + 1) (k := 1) (p := ENNReal.ofReal p)
        (Ω := HalfSpace.upper (m + 1))).toSubmodule := by
  apply (HalfSpace.traceLp_eq_zero_iff_mem_Wkp0 p (ENNReal.one_le_ofReal.mp Fact.out) _).mp
  apply (liftLp (ENNReal.ofReal p)).injective
  rw [map_zero]
  exact localFlatTraceLp_eq_zero_of_traceLp_eq_zero p i u hu

end SobolevSpace.Trace.C1
