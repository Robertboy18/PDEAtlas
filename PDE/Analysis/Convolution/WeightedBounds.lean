/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convolution.DerivativeBounds
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Localized weighted convolution bounds

A continuous weight on a compact integration set can be absorbed into the
constant in a smoothing convolution estimate. Finite sums preserve the same
L1 control, with constants chosen before the source.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ContDiff Convolution

namespace MeasureTheory

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [SFinite μ] [μ.IsAddLeftInvariant]

/-- A smooth compact kernel and a continuous compactly localized weight
define an L1-to-smooth operator, with uniform bounds at every order. -/
theorem exists_bound_iteratedFDeriv_weighted_convolution
    {S : Set E} (hS : IsCompact S) {a K : E → ℝ}
    (ha : ContinuousOn a S) (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K)
    (j : ℕ) :
    ∃ C > 0, ∀ u : E → ℝ, IntegrableOn u S μ →
      ContDiff ℝ ∞ (fun z ↦ ∫ y in S, (a y * u y) * K (z - y) ∂μ) ∧
      ∀ x, ‖iteratedFDeriv ℝ j
        (fun z ↦ ∫ y in S, (a y * u y) * K (z - y) ∂μ) x‖ ≤
          C * ∫ y in S, ‖u y‖ ∂μ := by
  obtain ⟨A, hA⟩ := hS.exists_bound_of_continuousOn ha
  obtain ⟨B, hB, hbound⟩ :=
    exists_bound_iteratedFDeriv_convolution_smul (μ := μ) hK hc j
  let A' := max A 0 + 1
  have hA' : 0 < A' := by dsimp [A']; positivity
  refine ⟨B * A', mul_pos hB hA', fun u hu ↦ ?_⟩
  have hau : IntegrableOn (fun y ↦ a y * u y) S μ := hu.bdd_mul
    (ha.aestronglyMeasurable hS.measurableSet)
    ((ae_restrict_mem hS.measurableSet).mono fun y hy ↦
      (hA y hy).trans (le_max_left A 0))
  let f := S.indicator (fun y ↦ a y * u y)
  have hf : Integrable f μ := hau.integrable_indicator hS.measurableSet
  have heq : (fun z ↦ ∫ y, f y • K (z - y) ∂μ) =
      fun z ↦ ∫ y in S, (a y * u y) * K (z - y) ∂μ := by
    funext z
    rw [← integral_indicator hS.measurableSet]
    apply integral_congr_ae
    exact Eventually.of_forall fun y ↦ by
      by_cases hy : y ∈ S <;> simp [f, hy]
  have hnorm : (∫ y, ‖f y‖ ∂μ) ≤ A' * ∫ y in S, ‖u y‖ ∂μ := by
    simp only [f, norm_indicator_eq_indicator_norm]
    rw [integral_indicator hS.measurableSet, ← integral_const_mul]
    apply integral_mono_ae hau.norm (hu.norm.const_mul A')
    filter_upwards [ae_restrict_mem hS.measurableSet] with y hy
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      ((hA y hy).trans (by dsimp [A']; linarith [le_max_left A 0])) (norm_nonneg _)
  refine ⟨?_, fun x ↦ ?_⟩
  · rw [← heq]
    exact hc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
      hf.locallyIntegrable hK
  · rw [← heq]
    exact (hbound f hf x).trans
      ((mul_le_mul_of_nonneg_left hnorm hB.le).trans_eq (mul_assoc B A' _).symm)

/-- Finite sums of localized smoothing kernels have a common L1 bound. The
constant depends only on the weights, kernels, set, measure and order. -/
theorem exists_bound_iteratedFDeriv_sum_weighted_convolution
    {ι : Type*} [Fintype ι] {S : Set E} (hS : IsCompact S)
    {a K : ι → E → ℝ} (ha : ∀ i, ContinuousOn (a i) S)
    (hK : ∀ i, ContDiff ℝ ∞ (K i)) (hc : ∀ i, HasCompactSupport (K i))
    (j : ℕ) :
    ∃ C > 0, ∀ u : E → ℝ, IntegrableOn u S μ →
      ContDiff ℝ ∞ (fun z ↦ ∑ i, ∫ y in S, (a i y * u y) * K i (z - y) ∂μ) ∧
      ∀ x, ‖iteratedFDeriv ℝ j
        (fun z ↦ ∑ i, ∫ y in S, (a i y * u y) * K i (z - y) ∂μ) x‖ ≤
          C * ∫ y in S, ‖u y‖ ∂μ := by
  choose C hC hbound using fun i ↦
    exists_bound_iteratedFDeriv_weighted_convolution (μ := μ) hS (ha i) (hK i) (hc i) j
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ ↦ (hC i).le
  refine ⟨(∑ i, C i) + 1, by linarith, fun u hu ↦ ?_⟩
  have hsmooth (i : ι) := (hbound i u hu).1
  refine ⟨ContDiff.sum fun i _ ↦ hsmooth i, fun x ↦ ?_⟩
  rw [iteratedFDeriv_fun_sum_apply (fun i _ ↦
    ((hsmooth i).of_le (by simp)).contDiffAt)]
  calc
    _ ≤ ∑ i, ‖iteratedFDeriv ℝ j
        (fun z ↦ ∫ y in S, (a i y * u y) * K i (z - y) ∂μ) x‖ := norm_sum_le _ _
    _ ≤ ∑ i, C i * ∫ y in S, ‖u y‖ ∂μ :=
      Finset.sum_le_sum fun i _ ↦ (hbound i u hu).2 x
    _ = (∑ i, C i) * ∫ y in S, ‖u y‖ ∂μ := (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith)
      (integral_nonneg fun _ ↦ norm_nonneg _)

end MeasureTheory
