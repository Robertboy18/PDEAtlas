/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.IsUniformGroup.Order

/-!
# Integrating uniform limits on a compact envelope

Only the set of integration needs finite measure. This also covers surface
measures that are not locally finite on the ambient Euclidean space.
-/

public section

open Filter Set MeasureTheory
open scoped Topology ENNReal

/-- Uniform convergence on a compact envelope passes through integration on
any measurable subset of finite measure. This includes measures concentrated
on a surface, without a local finiteness assumption in the ambient space. -/
theorem TendstoUniformlyOn.tendsto_setIntegral_of_continuousOn
    {X E ι : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure X} {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι → X → E} {f : X → E} {K S : Set X}
    (hlim : TendstoUniformlyOn F f l K) (hF : ∀ᶠ i in l, ContinuousOn (F i) K)
    (hK : IsCompact K) (hS : MeasurableSet S) (hSK : S ⊆ K) (hμ : μ S ≠ ∞) :
    Tendsto (fun i ↦ ∫ x in S, F i x ∂μ) l (𝓝 (∫ x in S, f x ∂μ)) := by
  rcases l.eq_or_neBot with rfl | hl
  · simp
  let : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hμ
  obtain ⟨C, hC⟩ := hK.bddAbove_image (hlim.continuousOn hF.frequently).norm
  apply tendsto_integral_filter_of_dominated_convergence (fun _ ↦ C + 1)
  · exact hF.mono fun i hi ↦ hi.aestronglyMeasurable_of_subset_isCompact hK hS hSK
  · have hb := uniformContinuous_norm.comp_tendstoUniformlyOn hlim
        |>.eventually_forall_le (show C < C + 1 by simp) (by simpa [upperBounds] using hC)
    filter_upwards [hb] with i hi
    filter_upwards [ae_restrict_mem hS] with x hx
    exact hi x (hSK hx)
  · exact integrable_const _
  · filter_upwards [ae_restrict_mem hS] with x hx
    exact hlim.tendsto_at (hSK hx)
