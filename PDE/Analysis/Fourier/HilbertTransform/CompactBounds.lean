/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.PrincipalValue.Continuity
import CAS.ExactTactic

/-!
# A uniform Hilbert bound from compact support and Lipschitz continuity

Subtracting the value at the evaluation point removes the singularity on
`|t| < 1`. There the Lipschitz constant bounds the kernel. Away from zero,
the uniform value bound applies, and compact support limits the interval of
integration. This estimate transfers a uniform spline error to its Hilbert
transform without evaluating the principal value numerically.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter
open scoped NNReal

namespace PDE.Analysis

private def compactKernelMajorant (R K B : ℝ) (t : ℝ) : ℝ :=
  (Icc (-1) 1).indicator (fun _ ↦ K) t +
    (Icc (-2 * R) (2 * R)).indicator (fun _ ↦ B) t

private theorem integrable_compactKernelMajorant (R K B : ℝ) :
    Integrable (compactKernelMajorant R K B) :=
  ((integrableOn_const (s := Icc (-1 : ℝ) 1) (C := K)
    measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc).add
    ((integrableOn_const (s := Icc (-2 * R) (2 * R)) (C := B)
      measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc)

private theorem integral_compactKernelMajorant {R : ℝ} (hR : 0 ≤ R) (K B : ℝ) :
    (∫ t, compactKernelMajorant R K B t) = 2 * K + 4 * R * B := by
  simp only [compactKernelMajorant]
  rw [integral_add
    ((integrableOn_const (s := Icc (-1 : ℝ) 1) (C := K)
      measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc)
    ((integrableOn_const (s := Icc (-2 * R) (2 * R)) (C := B)
      measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc),
    integral_indicator measurableSet_Icc, integral_indicator measurableSet_Icc]
  simp only [setIntegral_const, Real.volume_Icc, measureReal_def,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 - -1),
    ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * R - -2 * R), smul_eq_mul]
  cas

private theorem norm_kernel_le_compactMajorant
    {f : ℝ → ℝ} {K : ℝ≥0} {R B x : ℝ}
    (hf : LipschitzWith K f) (hB : ∀ y, |f y| ≤ B)
    (hs : ∀ y, R ≤ |y| → f y = 0) (hx : |x| ≤ R) (t : ℝ) :
    ‖hilbertRegularizedKernel f x 1 t‖ ≤ compactKernelMajorant R K B t := by
  have hB0 : 0 ≤ B := (abs_nonneg (f 0)).trans (hB 0)
  have hK0 : 0 ≤ (K : ℝ) := K.coe_nonneg
  by_cases ht : |t| < 1
  · have ht1 : t ∈ Icc (-1 : ℝ) 1 := abs_le.mp ht.le
    rw [compactKernelMajorant, indicator_of_mem ht1]
    have hfar : 0 ≤ (Icc (-2 * R) (2 * R)).indicator (fun _ ↦ B) t :=
      indicator_nonneg (fun _ _ ↦ hB0) t
    rw [hilbertRegularizedKernel, indicator_of_mem (s := {s : ℝ | |s| < 1}) ht,
      Real.norm_eq_abs, abs_div]
    by_cases ht0 : t = 0
    · simp only [ht0, abs_zero, div_zero]
      exact add_nonneg hK0 (indicator_nonneg (fun _ _ ↦ hB0) 0)
    · apply (div_le_iff₀ (abs_pos.mpr ht0)).mpr
      have h := hf.norm_sub_le (x - t) x
      simp only [Real.norm_eq_abs, sub_sub_cancel_left, abs_neg] at h
      nlinarith [abs_nonneg t]
  · rw [hilbertRegularizedKernel,
      indicator_of_notMem (s := {s : ℝ | |s| < 1}) ht, sub_zero,
      Real.norm_eq_abs, abs_div]
    have ht1 : 1 ≤ |t| := le_of_not_gt ht
    have htpos : 0 < |t| := by linarith
    by_cases hts : t ∈ Icc (-2 * R) (2 * R)
    · have hle : |f (x - t)| / |t| ≤ B := by
        apply (div_le_iff₀ htpos).mpr
        nlinarith [hB (x - t)]
      apply hle.trans
      rw [compactKernelMajorant, indicator_of_mem hts]
      exact le_add_of_nonneg_left (indicator_nonneg (fun _ _ ↦ hK0) t)
    · have hfar : 2 * R < |t| := lt_of_not_ge fun h ↦ hts (by
        simpa only [mem_Icc, neg_mul] using abs_le.mp h)
      have htriangle : |t| ≤ |x - t| + |x| := by
        simpa only [sub_zero, abs_sub_comm t x] using abs_sub_le t x 0
      rw [hs (x - t) (by linarith), abs_zero, zero_div]
      exact add_nonneg (indicator_nonneg (fun _ _ ↦ hK0) t)
        (indicator_nonneg (fun _ _ ↦ hB0) t)

/-- Local Lipschitz cancellation and support in `[-R,R]` bound the principal value.
The unit near-field interval contributes `2K`; the remaining support contributes `4RB`. -/
theorem abs_hilbertPV_le_of_lipschitzWith_of_support
    {f : ℝ → ℝ} {K : ℝ≥0} {R B x : ℝ}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (hB : ∀ y, |f y| ≤ B)
    (hs : ∀ y, R ≤ |y| → f y = 0) (hx : |x| ≤ R) :
    |hilbertPV f x| ≤ (2 * (K : ℝ) + 4 * R * B) / Real.pi := by
  rw [(hasHilbertPV_of_regularized
    (integrable_hilbertRegularizedKernel_one_of_lipschitzWith hf hc x)).hilbertPV_eq,
    abs_mul, abs_inv, abs_of_pos Real.pi_pos]
  have h := norm_integral_le_of_norm_le (integrable_compactKernelMajorant R K B)
    (Eventually.of_forall (norm_kernel_le_compactMajorant hf hB hs hx))
  rw [Real.norm_eq_abs, integral_compactKernelMajorant ((abs_nonneg x).trans hx)] at h
  calc
    _ ≤ Real.pi⁻¹ * (2 * (K : ℝ) + 4 * R * B) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr Real.pi_pos.le)
    _ = _ := by cas

end PDE.Analysis
