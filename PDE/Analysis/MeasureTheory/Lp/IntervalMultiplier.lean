/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Order.ExtendFrom

/-!
# Multiplication by coefficients with finite interval traces

Finite limits at both endpoints bound a continuous coefficient on an open
interval, so multiplication preserves `Lᵖ`. A function vanishing near the left
endpoint needs only the right trace; its zero neighborhood avoids a possible
singularity on the left. Endpoint traces may differ from totalized values.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology ENNReal

namespace MeasureTheory

/-- Continuity and finite endpoint traces bound a coefficient on an open interval;
the endpoint values of its totalized definition need not equal those traces. -/
theorem exists_norm_bound_of_continuousOn_tendsto
    {a b la lb : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ioo a b))
    (ha : Tendsto f (𝓝[>] a) (𝓝 la)) (hb : Tendsto f (𝓝[<] b) (𝓝 lb)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Ioo a b, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_Icc_extendFrom_Ioo hf ha hb)
  refine ⟨max C 0, le_max_right _ _, fun x hx ↦ ?_⟩
  have h := hC x ⟨hx.1.le, hx.2.le⟩
  rw [extendFrom_extends hf x hx] at h
  exact h.trans (le_max_left _ _)

/-- A finite right trace and interior continuity suffice for multiplication in
`Lᵖ` if the input is identically zero near the left endpoint. -/
theorem MemLp.mul_of_zero_germ_of_tendsto
    {L aL : ℝ} {a q : ℝ → ℝ} {p : ℝ≥0∞}
    (hq : MemLp q p (volume.restrict (Ioo 0 L))) (hL : 0 < L)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo 0 L)))
    (hac : ContinuousOn a (Ioo 0 L)) (hal : Tendsto a (𝓝[<] L) (𝓝 aL))
    (hq0 : ∀ᶠ x in 𝓝[>] (0 : ℝ), q x = 0) :
    MemLp (fun x ↦ a x * q x) p (volume.restrict (Ioo 0 L)) := by
  obtain ⟨b, hb, hzero⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hq0
  change 0 < b at hb
  let d : ℝ := min (b / 2) (L / 2)
  have hd : 0 < d := lt_min (by linarith) (by linarith)
  have hdL : d < L := (min_le_right _ _).trans_lt (by linarith)
  have hdb : d < b := (min_le_left _ _).trans_lt (by linarith)
  have hcont : ContinuousOn a (Ioo d L) :=
    hac.mono (fun _ hx ↦ ⟨hd.trans hx.1, hx.2⟩)
  have hleft : Tendsto a (𝓝[>] d) (𝓝 (a d)) :=
    (hac.continuousAt (Ioo_mem_nhds hd hdL)).tendsto.mono_left nhdsWithin_le_nhds
  obtain ⟨C, hC, hbound⟩ := exists_norm_bound_of_continuousOn_tendsto hcont hleft hal
  apply (hq.const_mul C).of_le (ha.mul hq.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  change ‖a x * q x‖ ≤ ‖C * q x‖
  by_cases hxd : x ≤ d
  · rw [hzero ⟨hx.1, hxd.trans_lt hdb⟩, mul_zero, mul_zero]
  · rw [norm_mul, norm_mul, Real.norm_eq_abs C, abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right (hbound x ⟨lt_of_not_ge hxd, hx.2⟩) (norm_nonneg _)

/-- Multiplication by a bounded interval coefficient preserves `Lᵖ`; finite endpoint
limits can differ from the coefficient's totalized endpoint values. -/
theorem memLp_mul_of_continuousOn_tendsto
    {L a0 aL : ℝ} {a q : ℝ → ℝ} {p : ℝ≥0∞}
    (hq : MemLp q p (volume.restrict (Ioo 0 L)))
    (ham : AEStronglyMeasurable a (volume.restrict (Ioo 0 L)))
    (hac : ContinuousOn a (Ioo 0 L))
    (ha0 : Tendsto a (𝓝[>] 0) (𝓝 a0)) (haL : Tendsto a (𝓝[<] L) (𝓝 aL)) :
    MemLp (fun x ↦ a x * q x) p (volume.restrict (Ioo 0 L)) := by
  obtain ⟨C, hC, hb⟩ := exists_norm_bound_of_continuousOn_tendsto hac ha0 haL
  apply (hq.const_mul C).of_le (ham.mul hq.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  change ‖a x * q x‖ ≤ ‖C * q x‖
  rw [norm_mul, norm_mul, Real.norm_eq_abs C, abs_of_nonneg hC]
  exact mul_le_mul_of_nonneg_right (hb x hx) (norm_nonneg _)

end MeasureTheory
