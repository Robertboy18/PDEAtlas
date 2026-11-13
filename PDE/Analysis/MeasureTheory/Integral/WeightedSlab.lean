/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Weighted limits of thin slabs

Rescaling a transverse interval to `[0, 1]` gives the boundary slice of a
continuous integrand with common compact tangential support. The transverse
weight need not be integrable on the whole real line. In particular it may be
the square of a continuous cutoff derivative.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace MeasureTheory

/-- A normalized weighted interval integral converges to the value at the
endpoint times the integral of the weight. The interval is oriented, so this
statement holds along the punctured two-sided neighbourhood. -/
theorem tendsto_normalized_weighted_intervalIntegral
    {f w : ℝ → ℝ} (hf : Continuous f) (hw : Continuous w) :
    Tendsto (fun h : ℝ ↦ h⁻¹ * ∫ r in 0..h, w (r / h) * f r)
      (𝓝[≠] 0) (𝓝 ((∫ s in (0 : ℝ)..1, w s) * f 0)) := by
  have hc : Continuous (fun h : ℝ ↦ ∫ s in (0 : ℝ)..1, w s * f (h * s)) := by
    simp_rw [intervalIntegral.integral_of_le zero_le_one,
      ← integral_Icc_eq_integral_Ioc]
    apply continuous_parametric_integral_of_continuous _ isCompact_Icc
    exact (hw.comp continuous_snd).mul (hf.comp (continuous_fst.mul continuous_snd))
  have ht := hc.continuousAt.tendsto.mono_left (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  simp only [zero_mul, intervalIntegral.integral_mul_const] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hn : h ≠ 0 := hh
  have hr := intervalIntegral.integral_comp_mul_left
    (fun r : ℝ ↦ w (r / h) * f r) (a := 0) (b := 1) hn
  simpa only [mul_div_cancel_left₀ _ hn, mul_zero, mul_one, smul_eq_mul] using hr

/-- The same limit on the actual open slab `0 < r < h`, with positive thickness. -/
theorem tendsto_normalized_weighted_Ioo_integral
    {f w : ℝ → ℝ} (hf : Continuous f) (hw : Continuous w) :
    Tendsto (fun h : ℝ ↦ h⁻¹ * ∫ r in Ioo 0 h, w (r / h) * f r)
      (𝓝[>] 0) (𝓝 ((∫ s in (0 : ℝ)..1, w s) * f 0)) := by
  have ht := (tendsto_normalized_weighted_intervalIntegral hf hw).mono_left
    (nhdsWithin_mono (0 : ℝ) (by intro x hx; exact ne_of_gt hx))
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [intervalIntegral.integral_of_le (le_of_lt hh), integral_Ioc_eq_integral_Ioo]

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]

/-- A continuous family with common compact tangential support has the expected
weighted slab limit. No differentiability or geometric boundary is assumed. -/
theorem tendsto_normalized_weighted_slab_integral
    {f : X × ℝ → ℝ} {w : ℝ → ℝ} {k : Set X}
    (hf : Continuous f) (hw : Continuous w) (hk : IsCompact k)
    (hs : ∀ y r, y ∉ k → f (y, r) = 0) :
    Tendsto (fun h : ℝ ↦ h⁻¹ * ∫ r in Ioo 0 h, w (r / h) * ∫ y, f (y, r) ∂μ)
      (𝓝[>] 0) (𝓝 ((∫ s in (0 : ℝ)..1, w s) * ∫ y, f (y, 0) ∂μ)) := by
  have hc : Continuous (fun r : ℝ ↦ ∫ y, f (y, r) ∂μ) := by
    apply continuousOn_univ.mp
    apply continuousOn_integral_of_compact_support hk
    · exact (hf.comp (continuous_snd.prodMk continuous_fst)).continuousOn
    · intro r y _ hy
      exact hs y r hy
  exact tendsto_normalized_weighted_Ioo_integral hc hw

/-- Compact support in the full product supplies a common compact tangential
support, so no support set needs to be chosen by the caller. -/
theorem tendsto_normalized_weighted_slab_integral_of_hasCompactSupport
    {f : X × ℝ → ℝ} {w : ℝ → ℝ}
    (hf : Continuous f) (hw : Continuous w) (hs : HasCompactSupport f) :
    Tendsto (fun h : ℝ ↦ h⁻¹ * ∫ r in Ioo 0 h, w (r / h) * ∫ y, f (y, r) ∂μ)
      (𝓝[>] 0) (𝓝 ((∫ s in (0 : ℝ)..1, w s) * ∫ y, f (y, 0) ∂μ)) := by
  apply tendsto_normalized_weighted_slab_integral hf hw (hs.isCompact.image continuous_fst)
  intro y r hy
  by_contra hn
  exact hy ⟨(y, r), subset_tsupport f hn, rfl⟩

end MeasureTheory
