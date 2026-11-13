/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.Classical
public import PDE.Spaces.Sobolev.Extension.C1.LocalPieces.ChartOperator

/-!
# Auxiliary chart transport and physical traces

The prepared H¹ chart operator uses cutoffs equal to one on the support of the
boundary partition. These are auxiliary cutoffs: the partition factor itself is
not applied during reconstruction of already localized boundary data.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1.Fractional

open MeasureTheory Set
open Boundary.Geometry.SurfaceMeasure
open Boundary.C1ExtensionAtlas.DerivedCutoffs
open Extension.C1.BoundaryPiece
open scoped ENNReal Sobolev

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- A global representative of auxiliary chart transport, supported inside the chart source. -/
def chartTransportRepresentative (i : Fin hΩ.N) (f : ℝ^(m + 1) → ℝ) :
    ℝ^(m + 1) → ℝ :=
  fun x ↦ (pullbackSupportCutoff (Ω := Ω) i).toFun x *
    (targetSupportCutoff (Ω := Ω) i).toFun (hΩ.chart i x) * f (hΩ.chart i x)

/-- The auxiliary chart representative preserves C¹ regularity. -/
theorem chartTransportRepresentative_contDiff (i : Fin hΩ.N) {f : ℝ^(m + 1) → ℝ}
    (hf : ContDiff ℝ 1 f) : ContDiff ℝ 1 (chartTransportRepresentative i f) :=
  (((pullbackSupportCutoff (Ω := Ω) i).contDiff.of_le (by simp)).mul
    (((targetSupportCutoff (Ω := Ω) i).contDiff.of_le (by simp)).comp
      (hΩ.chart_contDiff i))).mul (hf.comp (hΩ.chart_contDiff i))

/-- Auxiliary transport has compact support even if its input does not. -/
theorem chartTransportRepresentative_hasCompactSupport
    (i : Fin hΩ.N) (f : ℝ^(m + 1) → ℝ) :
    HasCompactSupport (chartTransportRepresentative i f) :=
  (pullbackSupportCutoff (Ω := Ω) i).hasCompactSupport.mul_right.mul_right

/-- Auxiliary transport is the indicator of the pullback support applied to the
target-cutoff pullback, since the source cutoff is one there. -/
theorem chartTransportRepresentative_eq_indicator
    (i : Fin hΩ.N) (f : ℝ^(m + 1) → ℝ) :
    chartTransportRepresentative i f =
      (pullbackSupport (Ω := Ω) i).indicator (fun x ↦
        (targetSupportCutoff (Ω := Ω) i).toFun (hΩ.chart i x) * f (hΩ.chart i x)) := by
  funext x
  by_cases hx : x ∈ pullbackSupport (Ω := Ω) i
  · rw [indicator_of_mem hx]
    simp [chartTransportRepresentative, pullbackSupportCutoff_eq_one_on_pullbackSupport i x hx]
  · rw [indicator_of_notMem hx]
    by_cases hχ : (pullbackSupportCutoff (Ω := Ω) i).toFun x = 0
    · simp [chartTransportRepresentative, hχ]
    · have hη : (targetSupportCutoff (Ω := Ω) i).toFun (hΩ.chart i x) = 0 := by
        by_contra hne
        have hxSource := tsupport_pullbackSupportCutoff_subset_source i (subset_tsupport _ hχ)
        exact hx ⟨hΩ.chart i x, subset_tsupport _ hne, (hΩ.chart i).left_inv hxSource⟩
      simp [chartTransportRepresentative, hη]

namespace FiniteExponent

/-- The prepared Sobolev chart map agrees with auxiliary transport of every base representative. -/
theorem preparedChartCLM_base_apply_ae (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : Fin hΩ.N)
    (u : W^{1,p}((hΩ.chart i).target))
    {f : ℝ^(m + 1) → ℝ}
    (hu : GraphSpace.baseRepresentative u =ᵐ[domainMeasure (m + 1) (hΩ.chart i).target] f) :
    GraphSpace.baseRepresentative (preparedChartCLM (p := p) i u)
      =ᵐ[domainMeasure (m + 1) univ] chartTransportRepresentative i f := by
  let L := pullbackSupport (Ω := Ω) i
  let V := targetCutoffCLM (p := p) i u
  have hV : GraphSpace.baseRepresentative V =ᵐ[domainMeasure (m + 1) (hΩ.chart i).target]
      fun y ↦ (targetSupportCutoff (Ω := Ω) i).toFun y * f y := by
    filter_upwards [GraphSpace.cutoffCLM_base_apply_ae (targetSupportCutoff i) u, hu]
      with y hy huy
    exact hy.trans (congrArg ((targetSupportCutoff (Ω := Ω) i).toFun y * ·) huy)
  have hc := (WeakChangeOfVariables.quasiMeasurePreserving_partialHomeomorph
    (E := hΩ.chart i) (hΩ.chart_contDiff i) (hΩ.chart_symm_contDiff i)).ae_eq_comp hV
  have hcL : (fun x ↦ GraphSpace.baseRepresentative V (hΩ.chart i x))
      =ᵐ[domainMeasure (m + 1) L]
        fun x ↦ (targetSupportCutoff (Ω := Ω) i).toFun (hΩ.chart i x) * f (hΩ.chart i x) :=
    hc.filter_mono (ae_mono
      (GraphSpace.domainMeasure_le (pullbackSupport_subset_source i)))
  have hL := (isCompact_pullbackSupport (Ω := Ω) i).measurableSet
  have hcomp : (fun x ↦
      (targetCutoffSupport (Ω := Ω) i).indicator (GraphSpace.baseRepresentative V)
        (hΩ.chart i x)) =ᵐ[domainMeasure (m + 1) L]
        fun x ↦ (targetSupportCutoff (Ω := Ω) i).toFun (hΩ.chart i x) * f (hΩ.chart i x) := by
    filter_upwards [hcL, ae_restrict_mem hL] with x hx hxL
    obtain ⟨y, hy, rfl⟩ := hxL
    have hyT := targetCutoffSupport_subset_target i hy
    rw [(hΩ.chart i).right_inv hyT, indicator_of_mem hy]
    simpa only [(hΩ.chart i).right_inv hyT] using hx
  have hind := (ae_eq_restrict_iff_indicator_ae_eq hL).mp hcomp
  have hp := preparedChartAmbient_base_apply_ae (p := p) i u
  rw [chartTransportRepresentative_eq_indicator]
  exact hp.trans (by
    simpa only [preparedChartBaseRepresentative, V, domainMeasure, Measure.restrict_univ]
      using hind)

end FiniteExponent

/-- The prepared H¹ chart map agrees with auxiliary transport of every base representative. -/
theorem preparedChartCLM_base_apply_ae (i : Fin hΩ.N)
    (u : H¹((hΩ.chart i).target))
    {f : ℝ^(m + 1) → ℝ}
    (hu : GraphSpace.baseRepresentative u =ᵐ[domainMeasure (m + 1) (hΩ.chart i).target] f) :
    GraphSpace.baseRepresentative (preparedChartCLM (p := 2) i u)
      =ᵐ[domainMeasure (m + 1) univ] chartTransportRepresentative i f :=
  FiniteExponent.preparedChartCLM_base_apply_ae 2 i u hu

/-- Transport a whole-space H¹ field through one auxiliary chart and restrict to the domain. -/
def chartTransport (i : Fin hΩ.N) :
    H¹(ℝ^(m + 1)) →L[ℝ] H¹(Ω) :=
  (GraphSpace.restrictCLM hΩ.isOpen.measurableSet (subset_univ _)).comp
    ((preparedChartCLM (p := 2) i).comp
      (GraphSpace.restrictCLM (hΩ.chart i).open_target.measurableSet (subset_univ _)))

/-- Multiplication by the auxiliary target cutoff on flat boundary values. -/
def flatTargetCutoff (i : Fin hΩ.N) :
    Lp ℝ 2 (flatSurfaceMeasure (n := m)) →L[ℝ] Lp ℝ 2 (flatSurfaceMeasure (n := m)) :=
  let η := targetSupportCutoff (Ω := Ω) i
  let hη := η.contDiff.continuous.memLp_top_of_hasCompactSupport
    η.hasCompactSupport (flatSurfaceMeasure (n := m))
  (ContinuousLinearMap.mul ℝ ℝ).holderL (flatSurfaceMeasure (n := m)) ∞ 2 2 (hη.toLp η.toFun)

/-- The flat auxiliary cutoff has the literal multiplication representative. -/
theorem flatTargetCutoff_apply_ae (i : Fin hΩ.N)
    (v : Lp ℝ 2 (flatSurfaceMeasure (n := m))) :
    (flatTargetCutoff i v : ℝ^(m + 1) → ℝ) =ᵐ[flatSurfaceMeasure (n := m)]
      fun y ↦ (targetSupportCutoff (Ω := Ω) i).toFun y * v y := by
  let η := targetSupportCutoff (Ω := Ω) i
  let hη := η.contDiff.continuous.memLp_top_of_hasCompactSupport
    η.hasCompactSupport (flatSurfaceMeasure (n := m))
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder
    (r := (2 : ℝ≥0∞)) (hη.toLp η.toFun) v, hη.coeFn_toLp] with y hy hηy
  exact hy.trans (congrArg (· * v y) hηy)

end SobolevSpace.Trace.C1.Fractional
