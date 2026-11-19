/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.PrincipalValue
import CAS.ExactTactic

/-!
# Positive dilation of real Hilbert principal values

The real Hilbert transform commutes with positive spatial dilation. The proof
changes variables in the truncated Lebesgue integrals, scales the cutoff by the
same factor, and then takes its limit at zero.
-/

@[expose] public section

namespace PDE.Analysis

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-- The Jacobian cancels the scaling of the Hilbert kernel. -/
theorem hilbertKernel_dilate (c a t : ℝ) (hc : c ≠ 0) :
    a / t = c * (a / (c * t)) := by
  cas using hc

/-- Scaling the kernel and its symmetric cutoff gives the same integrand with
the change-of-variables Jacobian included. -/
theorem indicator_hilbertKernel_dilate (f : ℝ → ℝ) {c : ℝ} (hc : 0 < c)
    (x ε t : ℝ) :
    {s : ℝ | ε < |s|}.indicator (fun s ↦ f (c * (x - s)) / s) t =
      c * {s : ℝ | c * ε < |s|}.indicator (fun s ↦ f (c * x - s) / s) (c * t) := by
  simp only [indicator, mem_ofPred_eq, abs_mul, abs_of_pos hc,
    mul_lt_mul_iff_right₀ hc]
  split_ifs
  · rw [mul_sub]
    exact hilbertKernel_dilate c _ t hc.ne'
  · exact (mul_zero c).symm

/-- Positive dilation scales the truncation radius by the same factor. -/
theorem hilbertTruncation_dilate (f : ℝ → ℝ) {c : ℝ} (hc : 0 < c) (x ε : ℝ) :
    hilbertTruncation (fun y ↦ f (c * y)) x ε =
      hilbertTruncation f (c * x) (c * ε) := by
  unfold hilbertTruncation
  rw [← integral_indicator (measurableSet_hilbertCutoff ε),
    ← integral_indicator (measurableSet_hilbertCutoff (c * ε))]
  simp_rw [indicator_hilbertKernel_dilate f hc x ε]
  rw [integral_const_mul, Measure.integral_comp_mul_left]
  simp only [abs_inv, abs_of_pos hc, smul_eq_mul]
  rw [← mul_assoc c, mul_inv_cancel₀ hc.ne', one_mul]

/-- The real principal-value Hilbert transform commutes with positive dilation. -/
theorem HasHilbertPV.dilate {f : ℝ → ℝ} {c x h : ℝ}
    (hf : HasHilbertPV f (c * x) h) (hc : 0 < c) :
    HasHilbertPV (fun y ↦ f (c * y)) x h := by
  constructor
  · intro ε hε
    have hint := (hf.1 (c * ε) (mul_pos hc hε)).integrable_indicator
      (measurableSet_hilbertCutoff (c * ε))
    have hcomp := (integrable_comp_mul_left_iff _ hc.ne').mpr hint
    rw [← integrable_indicator_iff (measurableSet_hilbertCutoff ε)]
    exact (hcomp.const_mul c).congr
      (ae_of_all _ fun t ↦ (indicator_hilbertKernel_dilate f hc x ε t).symm)
  · have hcutoff : Tendsto (fun ε : ℝ ↦ c * ε) (𝓝[>] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · have hid : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
          tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
        simpa only [mul_zero] using hid.const_mul c
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        exact mul_pos hc hε
    convert hf.2.comp hcutoff using 1
    exact funext fun ε ↦ hilbertTruncation_dilate f hc x ε

/-- The operator form of positive dilation, with convergence explicitly supplied. -/
theorem hilbertPV_dilate {f : ℝ → ℝ} {c x h : ℝ}
    (hf : HasHilbertPV f (c * x) h) (hc : 0 < c) :
    hilbertPV (fun y ↦ f (c * y)) x = hilbertPV f (c * x) := by
  rw [hf.hilbertPV_eq, (hf.dilate hc).hilbertPV_eq]

end

end PDE.Analysis
