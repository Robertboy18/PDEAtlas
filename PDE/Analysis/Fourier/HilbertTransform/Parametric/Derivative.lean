/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.PrincipalValue.Calculus

/-!
# Parameter differentiation of compact Hilbert families

A common Lipschitz bound and fixed support for the time derivatives give
one integrable cancellation-kernel bound. Differentiation under the regularized
integral then commutes the time derivative with the principal value.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped NNReal Topology

namespace PDE.Analysis

/-- Fixed support and uniform Lipschitz and value bounds give one integrable
bound for all the cancellation kernels, locally in the evaluation point. -/
theorem exists_integrable_hilbert_kernel_bound
    {ι : Type*} {q : ι → ℝ → ℝ} {K : ℝ≥0} {B L : ℝ}
    (hL : 0 ≤ L) (hq : ∀ t, LipschitzWith K (q t))
    (hB : ∀ t y, ‖q t y‖ ≤ B)
    (hs : ∀ t y, L ≤ |y| → q t y = 0) (x₀ : ℝ) :
    ∃ bound : ℝ → ℝ, Integrable bound ∧
      ∀ t x, x ∈ Metric.ball x₀ 1 → ∀ y,
        ‖hilbertRegularizedKernel (q t) x 1 y‖ ≤ bound y := by
  let R : ℝ := |x₀| + L + 2
  refine ⟨{y : ℝ | |y| < R}.indicator (fun _ ↦ (K : ℝ) + B),
    integrable_hilbertLocalConstant R (K + B), fun t x hx y ↦ ?_⟩
  by_cases hy : |y| < R
  · rw [indicator_of_mem (s := {y : ℝ | |y| < R}) hy]
    exact norm_hilbertRegularizedKernel_one_le (hq t) (hB t) x y
  · rw [indicator_of_notMem (s := {y : ℝ | |y| < R}) hy]
    have hx1 : |x - x₀| < 1 := by
      simpa only [Metric.mem_ball, Real.dist_eq] using hx
    have hxn : |x| ≤ |x - x₀| + |x₀| := by
      simpa only [sub_zero] using abs_sub_le x x₀ 0
    have hyn : |y| ≤ |x - y| + |x| := by
      simpa only [sub_zero, abs_sub_comm y x] using abs_sub_le y x 0
    have hyR : R ≤ |y| := le_of_not_gt hy
    have hfar : ¬ |y| < 1 := by
      dsimp only [R] at hyR
      linarith [abs_nonneg x₀]
    have hz : q t (x - y) = 0 := by
      apply hs
      dsimp only [R] at hyR
      linarith
    simp only [hilbertRegularizedKernel,
      indicator_of_notMem (s := {s : ℝ | |s| < 1}) hfar, hz, sub_zero, zero_div, norm_zero,
      le_refl]

/-- Pointwise time differentiation commutes with the Hilbert principal
value when the time derivatives have fixed support and uniform Lipschitz
and value bounds. No temporal Hilbert identity is an input. -/
theorem hasDerivAt_hilbertPV_of_uniform_time_bounds
    {f q : ℝ → ℝ → ℝ} {times : Set ℝ} {t : ℝ} {K : ℝ≥0} {B L : ℝ}
    (htimes : times ∈ 𝓝 t) (hL : 0 ≤ L)
    (hf : ∀ s ∈ times, ContDiff ℝ 1 (f s))
    (hc : ∀ s ∈ times, HasCompactSupport (f s))
    (hq : ∀ s ∈ times, LipschitzWith K (q s))
    (hB : ∀ s ∈ times, ∀ y, ‖q s y‖ ≤ B)
    (hs : ∀ s ∈ times, ∀ y, L ≤ |y| → q s y = 0)
    (hd : ∀ y s, s ∈ times → HasDerivAt (fun r ↦ f r y) (q s y) s) (x : ℝ) :
    HasDerivAt (fun s ↦ hilbertPV (f s) x) (hilbertPV (q t) x) t := by
  have ht := mem_of_mem_nhds htimes
  have hqc (s : ℝ) (hs' : s ∈ times) : HasCompactSupport (q s) := by
    apply HasCompactSupport.intro (K := Icc (-L) L) isCompact_Icc
    intro y hy
    exact hs s hs' y (le_of_not_ge fun hyL ↦ hy (abs_le.mp hyL))
  have hint (s : ℝ) (hs' : s ∈ times) :
      Integrable (hilbertRegularizedKernel (f s) x 1) := by
    obtain ⟨J, hJ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hc s hs')
      (hf s hs') one_ne_zero
    exact integrable_hilbertRegularizedKernel_one_of_lipschitzWith hJ (hc s hs') x
  have hqint := integrable_hilbertRegularizedKernel_one_of_lipschitzWith
    (hq t ht) (hqc t ht) x
  obtain ⟨bound, hb, hbound⟩ := exists_integrable_hilbert_kernel_bound
    (q := fun s : times ↦ q s) hL (fun s ↦ hq s s.property)
    (fun s ↦ hB s s.property) (fun s ↦ hs s s.property) x
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le htimes
    (F := fun s y ↦ hilbertRegularizedKernel (f s) x 1 y)
    (F' := fun s y ↦ hilbertRegularizedKernel (q s) x 1 y)
    ((show ∀ᶠ s in 𝓝 t, s ∈ times from htimes).mono
      fun s hs' ↦ (hint s hs').aestronglyMeasurable)
    (hint t ht) hqint.aestronglyMeasurable
    (Eventually.of_forall fun y s hs' ↦
      hbound ⟨s, hs'⟩ x (Metric.mem_ball_self zero_lt_one) y) hb
    (Eventually.of_forall fun y s hs' ↦ by
      unfold hilbertRegularizedKernel
      by_cases hy : |y| < 1
      · simp only [indicator_of_mem (s := {y : ℝ | |y| < 1}) hy]
        exact ((hd (x - y) s hs').fun_sub (hd x s hs')).div_const y
      · simp only [indicator_of_notMem (s := {y : ℝ | |y| < 1}) hy, sub_zero]
        exact (hd (x - y) s hs').div_const y)
  rw [(hasHilbertPV_of_regularized hqint).hilbertPV_eq]
  apply (hi.2.const_mul Real.pi⁻¹).congr_of_eventuallyEq
  exact (show ∀ᶠ s in 𝓝 t, s ∈ times from htimes).mono
    fun s hs' ↦ (hasHilbertPV_of_regularized (hint s hs')).hilbertPV_eq

end PDE.Analysis
