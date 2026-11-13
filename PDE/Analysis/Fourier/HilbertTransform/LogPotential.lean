/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.EndpointMoments
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import CAS.ExactTactic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Logarithmic potentials and the real Hilbert transform

The real logarithm is locally integrable, so its convolution with compactly supported
input is defined everywhere. The logarithmic primitive of the Hilbert principal value is
built from three facts that need no Lipschitz theory: the symmetric-difference
form of the principal value, logarithmic integration by parts on the half-line for `C¹`
input, and the identification of the velocity and its mean for odd input once the
potential is known to be a primitive. The symmetric difference cancels the logarithmic
boundary term at zero, which avoids interchanging an unregularized singular double
integral.
-/

@[expose] public section

namespace PDE.Analysis

open Filter MeasureTheory Set
open scoped Convolution Topology

noncomputable section

/-- The real logarithm, totalized at zero, is locally integrable on the whole line. -/
theorem locallyIntegrable_real_log : LocallyIntegrable Real.log (volume : Measure ℝ) := by
  intro x
  refine ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp
    intervalIntegral.intervalIntegrable_log'

/-- First-order vanishing cancels the logarithmic boundary singularity. -/
theorem tendsto_mul_log_zero_of_hasDerivAt {g : ℝ → ℝ} {d : ℝ}
    (hg : HasDerivAt g d 0) (hzero : g 0 = 0) :
    Tendsto (fun t ↦ g t * Real.log t) (𝓝[>] 0) (𝓝 0) := by
  have hratio : Tendsto (fun t ↦ g t / t) (𝓝[>] 0) (𝓝 d) := by
    simpa only [zero_add, hzero, sub_zero, smul_eq_mul, div_eq_inv_mul] using
      hg.tendsto_slope_zero_right
  have hlog : Tendsto (fun t ↦ t * Real.log t) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Real.continuous_mul_log.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have h := hratio.mul hlog
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ne_of_gt ht
  cas using ht0

/-- Logarithmic integration by parts on the positive half-line. Compact support
removes the boundary at infinity, and first-order vanishing removes the boundary at zero. -/
theorem integral_Ioi_div_eq_neg_deriv_mul_log {g : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) (hcompact : HasCompactSupport g) (hzero : g 0 = 0) :
    (∫ t in Ioi 0, g t / t) = -∫ t in Ioi 0, deriv g t * Real.log t := by
  have hgint : Integrable g := hg.continuous.integrable_of_hasCompactSupport hcompact
  have hdiv := integrable_div_id_of_differentiableAt_zero hgint hzero
    hg.differentiable_one.differentiableAt
  have hlog : Integrable (fun t ↦ deriv g t * Real.log t) := by
    simpa only [smul_eq_mul] using
      locallyIntegrable_real_log.integrable_smul_left_of_hasCompactSupport
        (hg.continuous_deriv le_rfl) hcompact.deriv
  have hboundary : Tendsto (g * Real.log) atTop (𝓝 0) :=
    (hcompact.mul_right (f' := Real.log)).is_zero_at_infty.mono_left atTop_le_cocompact
  have h := integral_Ioi_mul_deriv_eq_deriv_mul
    (u := g) (u' := deriv g) (v := Real.log) (v' := fun t ↦ 1 / t)
    (fun t _ ↦ hg.differentiable_one.differentiableAt.hasDerivAt)
    (fun t ht ↦ by
      have ht0 : t ≠ 0 := ne_of_gt ht
      cas using ht0)
    (by simpa only [Pi.mul_def, ← div_eq_mul_one_div] using hdiv.integrableOn)
    hlog.integrableOn
    (tendsto_mul_log_zero_of_hasDerivAt
      hg.differentiable_one.differentiableAt.hasDerivAt hzero)
    hboundary
  simpa only [zero_sub, sub_zero, mul_one_div] using h

/-- Local regularization folds to the odd difference in the integration variable. -/
theorem hilbertPV_eq_integral_symmetric_difference {f : ℝ → ℝ}
    (hf : Integrable f) {x : ℝ} (hdiff : DifferentiableAt ℝ f x) :
    hilbertPV f x =
      Real.pi⁻¹ * ∫ t in Ioi 0, (f (x - t) - f (x + t)) / t := by
  obtain ⟨R, _, hint⟩ :=
    exists_integrable_hilbertRegularizedKernel_of_differentiableAt hf hdiff
  rw [(hasHilbertPV_of_regularized hint).hilbertPV_eq,
    integral_eq_integral_Ioi_add_reflection hint]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only [hilbertRegularizedKernel, indicator, mem_ofPred_eq, abs_neg, sub_neg_eq_add,
    div_neg]
  split_ifs <;> ring

/-- The logarithmic moment is absolutely integrable for continuous compact input. -/
theorem integrable_log_sub_mul {f : ℝ → ℝ}
    (hf : Continuous f) (hcompact : HasCompactSupport f) (x : ℝ) :
    Integrable (fun y ↦ Real.log (x - y) * f y) := by
  have h : Integrable (fun t ↦ Real.log t * f (x - t)) :=
    (hcompact.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
      locallyIntegrable_real_log hf x).integrable
  simpa only [sub_sub_cancel] using h.comp_sub_left x

/-- An odd input fixes the logarithmic primitive's value at zero, so any primitive
with the same derivative and normalization agrees with it. -/
theorem velocity_eq_log_potential_of_hasDerivAt {f u : ℝ → ℝ}
    (hodd : Function.Odd f) (hu : ∀ x, HasDerivAt u (hilbertPV f x) x)
    (hp : ∀ x, HasDerivAt (fun z ↦ Real.pi⁻¹ * ∫ y, Real.log (z - y) * f y)
      (hilbertPV f x) x)
    (hu0 : u 0 = 0) (x : ℝ) :
    u x = Real.pi⁻¹ * ∫ y, Real.log (x - y) * f y := by
  let p : ℝ → ℝ := fun z ↦ Real.pi⁻¹ * ∫ y, Real.log (z - y) * f y
  have hdiff : ∀ z, HasDerivAt (u - p) 0 z := by
    intro z
    simpa only [sub_self] using (hu z).sub (hp z)
  have heq := is_const_of_deriv_eq_zero (fun z ↦ (hdiff z).differentiableAt)
    (fun z ↦ (hdiff z).deriv) x 0
  have hlog0 : (∫ y, Real.log (0 - y) * f y) = 0 := by
    apply integral_eq_zero_of_odd
    intro y
    simp only [zero_sub, neg_neg, Real.log_neg_eq_log, hodd y, mul_neg]
  have hp0 : p 0 = 0 := by simp only [p, hlog0, mul_zero]
  simpa only [Pi.sub_apply, hu0, hp0, sub_zero, sub_self, sub_eq_zero] using heq

/-- Odd reflection converts the endpoint logarithmic potential into its half-support
moment. Continuity and compact support ensure absolute integrability. -/
theorem neg_log_potential_div_eq_log_moment {f : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L) (hf : Continuous f) (hcompact : HasCompactSupport f)
    (hodd : Function.Odd f) (hsupport : ∀ y, L ≤ y → f y = 0) :
    -(Real.pi⁻¹ * ∫ y, Real.log (L - y) * f y) / L =
      ∫ y in Ioo 0 L, (Real.log ((L + y) / (L - y)) / (L * Real.pi)) * f y := by
  have hreflect :
      (∫ y, Real.log (L - y) * f y) =
        ∫ y in Ioi 0, (Real.log (L - y) - Real.log (L + y)) * f y := by
    rw [integral_eq_integral_Ioi_add_reflection
      (integrable_log_sub_mul hf hcompact L)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y _
    dsimp only
    rw [sub_neg_eq_add, hodd y]
    ring
  have htruncate :
      (∫ y in Ioi 0, (Real.log (L - y) - Real.log (L + y)) * f y) =
        ∫ y in Ioo 0 L, (Real.log (L - y) - Real.log (L + y)) * f y := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun _ hy ↦ hy.1)
    intro y hy
    have hyL : L ≤ y := not_lt.mp fun hyL ↦ hy.2 ⟨hy.1, hyL⟩
    simp only [hsupport y hyL, mul_zero]
  rw [hreflect, htruncate]
  calc
    _ = ∫ y in Ioo 0 L,
        -(Real.pi⁻¹ / L) * ((Real.log (L - y) - Real.log (L + y)) * f y) := by
      rw [integral_const_mul]
      ring
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro y hy
      have hminus : L - y ≠ 0 := (sub_pos.mpr hy.2).ne'
      have hplus : L + y ≠ 0 := (add_pos hL hy.1).ne'
      have hL0 := hL.ne'
      dsimp only
      rw [Real.log_div hplus hminus]
      cas using hL0

end

end PDE.Analysis
