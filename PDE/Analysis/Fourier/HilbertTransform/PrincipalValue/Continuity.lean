/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.Regularity

/-!
# Continuity of the Hilbert principal value

For compactly supported Lipschitz input, subtraction of the local constant gives
a bounded kernel near zero. Its support in the integration variable is uniformly
bounded when the evaluation point ranges over a bounded neighborhood. Dominated
convergence therefore gives continuity of the principal value.
-/

@[expose] public section

namespace PDE.Analysis

open Filter MeasureTheory Set
open scoped ContDiff NNReal Topology

noncomputable section

/-- Fixed-radius cancellation is integrable for compactly supported Lipschitz input. -/
theorem integrable_hilbertRegularizedKernel_one_of_lipschitzWith {f : ℝ → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) (hsupp : HasCompactSupport f) (x : ℝ) :
    Integrable (hilbertRegularizedKernel f x 1) := by
  have hint : Integrable f :=
    memLp_one_iff_integrable.mp (hf.continuous.memLp_of_hasCompactSupport hsupp)
  apply integrable_hilbertRegularizedKernel hint zero_lt_one K.coe_nonneg
  intro t _
  simpa only [Real.norm_eq_abs, sub_sub_cancel_left, abs_neg] using hf.norm_sub_le (x - t) x

/-- Compactly supported Lipschitz input has a principal value at every
point, including integrability at every positive cutoff. -/
theorem hasHilbertPV_of_lipschitzWith_compactSupport {f : ℝ → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) (hsupp : HasCompactSupport f) (x : ℝ) :
    HasHilbertPV f x (hilbertPV f x) := by
  have hpv := hasHilbertPV_of_regularized
    (integrable_hilbertRegularizedKernel_one_of_lipschitzWith hf hsupp x)
  rw [hpv.hilbertPV_eq]
  exact hpv

/-- A bounded Lipschitz input has a uniformly bounded cancellation kernel. -/
theorem norm_hilbertRegularizedKernel_one_le {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {B : ℝ} (hB : ∀ y, ‖f y‖ ≤ B) (x t : ℝ) :
    ‖hilbertRegularizedKernel f x 1 t‖ ≤ K + B := by
  have hB0 : 0 ≤ B := (norm_nonneg (f 0)).trans (hB 0)
  have hKB : 0 ≤ (K : ℝ) + B := add_nonneg K.coe_nonneg hB0
  by_cases ht0 : t = 0
  · simp only [hilbertRegularizedKernel, ht0, div_zero, norm_zero]
    exact hKB
  have htpos : 0 < |t| := abs_pos.mpr ht0
  by_cases ht : |t| < 1
  · rw [hilbertRegularizedKernel, indicator_of_mem (s := {s : ℝ | |s| < 1}) ht,
      norm_div, Real.norm_eq_abs, Real.norm_eq_abs]
    apply (div_le_iff₀ htpos).mpr
    have h := hf.norm_sub_le (x - t) x
    simp only [Real.norm_eq_abs, sub_sub_cancel_left, abs_neg] at h
    nlinarith
  · rw [hilbertRegularizedKernel, indicator_of_notMem (s := {s : ℝ | |s| < 1}) ht,
      sub_zero, norm_div, Real.norm_eq_abs, Real.norm_eq_abs]
    apply (div_le_iff₀ htpos).mpr
    have hb := hB (x - t)
    rw [Real.norm_eq_abs] at hb
    have ht1 : 1 ≤ |t| := le_of_not_gt ht
    nlinarith [K.coe_nonneg]

/-- The cancellation kernels admit one integrable bound on a neighborhood of
each evaluation point. This bound also serves for differentiation under the integral. -/
theorem exists_integrable_bound_hilbertRegularizedKernel_one {f : ℝ → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) (hsupp : HasCompactSupport f) (x₀ : ℝ) :
    ∃ bound : ℝ → ℝ, Integrable bound ∧
      ∀ x ∈ Metric.ball x₀ 1, ∀ t, ‖hilbertRegularizedKernel f x 1 t‖ ≤ bound t := by
  obtain ⟨B, hB⟩ := hsupp.exists_bound_of_continuous hf.continuous
  obtain ⟨S, hS, hsupport⟩ := hsupp.exists_pos_le_norm
  let R : ℝ := |x₀| + S + 2
  refine ⟨{t : ℝ | |t| < R}.indicator (fun _ ↦ (K : ℝ) + B),
    integrable_hilbertLocalConstant R (K + B), ?_⟩
  intro x hx t
  by_cases ht : |t| < R
  · rw [indicator_of_mem (s := {t : ℝ | |t| < R}) ht]
    exact norm_hilbertRegularizedKernel_one_le hf hB x t
  · rw [indicator_of_notMem (s := {t : ℝ | |t| < R}) ht]
    have hx1 : |x - x₀| < 1 := by
      simpa only [Metric.mem_ball, Real.dist_eq] using hx
    have hxnorm : |x| ≤ |x - x₀| + |x₀| := by
      simpa only [sub_zero] using abs_sub_le x x₀ 0
    have htnorm : |t| ≤ |x - t| + |x| := by
      simpa only [sub_zero, abs_sub_comm t x] using abs_sub_le t x 0
    have htR : R ≤ |t| := le_of_not_gt ht
    have hfar : ¬ |t| < 1 := by
      dsimp [R] at htR
      linarith [abs_nonneg x₀]
    have hzero : f (x - t) = 0 := by
      apply hsupport
      rw [Real.norm_eq_abs]
      dsimp [R] at htR
      linarith
    simp only [hilbertRegularizedKernel,
      indicator_of_notMem (s := {s : ℝ | |s| < 1}) hfar, hzero, sub_zero, zero_div, norm_zero,
      le_refl]

/-- For fixed integration variable, the cancellation kernel is continuous in
the evaluation point whenever the input is continuous. -/
theorem continuous_hilbertRegularizedKernel_eval {f : ℝ → ℝ} (hf : Continuous f)
    (R t : ℝ) : Continuous (fun x ↦ hilbertRegularizedKernel f x R t) := by
  unfold hilbertRegularizedKernel
  by_cases ht : |t| < R
  · simp only [indicator_of_mem (s := {s : ℝ | |s| < R}) ht]
    exact ((hf.comp (continuous_id.sub continuous_const)).sub hf).div_const t
  · simp only [indicator_of_notMem (s := {s : ℝ | |s| < R}) ht, sub_zero]
    exact (hf.comp (continuous_id.sub continuous_const)).div_const t

/-- The principal value of compactly supported Lipschitz input is continuous. -/
theorem continuous_hilbertPV_of_lipschitzWith_compactSupport {f : ℝ → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) (hsupp : HasCompactSupport f) :
    Continuous (hilbertPV f) := by
  have hint (x : ℝ) := integrable_hilbertRegularizedKernel_one_of_lipschitzWith hf hsupp x
  have heq (x : ℝ) : hilbertPV f x = Real.pi⁻¹ * ∫ t, hilbertRegularizedKernel f x 1 t :=
    (hasHilbertPV_of_regularized (hint x)).hilbertPV_eq
  rw [show hilbertPV f = (fun x ↦ Real.pi⁻¹ * ∫ t, hilbertRegularizedKernel f x 1 t) from
    funext heq]
  apply continuous_iff_continuousAt.mpr
  intro x₀
  apply ContinuousAt.const_mul
  obtain ⟨bound, hbound, hdom⟩ :=
    exists_integrable_bound_hilbertRegularizedKernel_one hf hsupp x₀
  apply continuousAt_of_dominated (bound := bound)
  · exact Eventually.of_forall fun x ↦ (hint x).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds x₀ zero_lt_one] with x hx
    exact Eventually.of_forall (hdom x hx)
  · exact hbound
  · exact Eventually.of_forall fun t ↦ (continuous_hilbertRegularizedKernel_eval
      hf.continuous 1 t).continuousAt

/-- In particular, compact `C¹` input has a continuous Hilbert principal value. -/
theorem continuous_hilbertPV_of_contDiff_one_compactSupport {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hsupp : HasCompactSupport f) : Continuous (hilbertPV f) := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hsupp hf (by norm_num)
  exact continuous_hilbertPV_of_lipschitzWith_compactSupport hK hsupp

end

end PDE.Analysis
