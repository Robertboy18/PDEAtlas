/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Derivative bounds for smoothing convolutions

An integrable scalar source convolved with a smooth compact kernel has every
derivative bounded by the source's L1 norm times the corresponding uniform
kernel bound. The induction uses Mathlib's convolution differentiation theorem
and the isometric currying of iterated derivatives.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ContDiff Convolution

namespace MeasureTheory

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [SFinite μ] [μ.IsAddLeftInvariant]

/-- Uniform bounds for a kernel derivative give the corresponding L1
bound for its convolution. Neither positivity of the source nor completeness
of the target is needed. -/
theorem norm_iteratedFDeriv_convolution_smul_le
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → ℝ} (hf : Integrable f μ)
    {K : E → F} (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K)
    (j : ℕ) {M : ℝ} (hM : ∀ y, ‖iteratedFDeriv ℝ j K y‖ ≤ M) (x : E) :
    ‖iteratedFDeriv ℝ j (fun z ↦ ∫ y, f y • K (z - y) ∂μ) x‖ ≤
      (∫ y, ‖f y‖ ∂μ) * M := by
  induction j generalizing F with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    have hbound : ∀ y, ‖K y‖ ≤ M := by
      simpa only [norm_iteratedFDeriv_zero] using hM
    calc
      ‖∫ y, f y • K (x - y) ∂μ‖ ≤ ∫ y, ‖f y‖ * M ∂μ := by
        apply norm_integral_le_of_norm_le (hf.norm.mul_const M)
        exact Eventually.of_forall fun y ↦ by
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)
      _ = (∫ y, ‖f y‖ ∂μ) * M := integral_mul_const M _
  | succ j ih =>
    have hD : ContDiff ℝ ∞ (fderiv ℝ K) := hK.fderiv_right (by simp)
    have heq : fderiv ℝ (fun z ↦ ∫ y, f y • K (z - y) ∂μ) =
        fun z ↦ ∫ y, f y • fderiv ℝ K (z - y) ∂μ := by
      funext z
      have hd := hc.hasFDerivAt_convolution_right
        (L := ContinuousLinearMap.lsmul ℝ ℝ) hf.locallyIntegrable
        (hK.of_le (by simp)) z
      exact hd.fderiv
    rw [← norm_iteratedFDeriv_fderiv, heq]
    exact ih hD (hc.fderiv ℝ)
      (fun y ↦ (norm_iteratedFDeriv_fderiv (𝕜 := ℝ)).trans_le (hM y))

/-- A fixed smooth compact kernel has an L1-to-uniform bound at every derivative
order. The constant is selected before the source and evaluation point. -/
theorem exists_bound_iteratedFDeriv_convolution_smul
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : E → F} (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K) (j : ℕ) :
    ∃ C > 0, ∀ f : E → ℝ, Integrable f μ → ∀ x,
      ‖iteratedFDeriv ℝ j (fun z ↦ ∫ y, f y • K (z - y) ∂μ) x‖ ≤
        C * ∫ y, ‖f y‖ ∂μ := by
  obtain ⟨M, hM⟩ := (hc.iteratedFDeriv j).exists_bound_of_continuous
    (hK.continuous_iteratedFDeriv (by simp))
  refine ⟨max M 0 + 1, by positivity, fun f hf x ↦ ?_⟩
  rw [mul_comm]
  apply norm_iteratedFDeriv_convolution_smul_le hf hK hc
  intro y
  exact (hM y).trans (by linarith [le_max_left M 0])

end MeasureTheory
