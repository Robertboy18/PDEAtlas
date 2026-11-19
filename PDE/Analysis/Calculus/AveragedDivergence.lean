/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.HessianTrace
public import PDE.Analysis.Integration.ParametricIntervalSmooth.Local
import CAS.ExactTactic

/-!
# Divergence of a parameter average

In finite dimension the trace is a continuous linear functional on operators.
It therefore commutes with the interval integral in the derivative of an average.
This gives an upper divergence bound from pointwise bounds for the integrand.
-/

@[expose] public section

open scoped Gradient

noncomputable section

namespace PDE.Analysis

open MeasureTheory Metric
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- The trace as a continuous linear functional on continuous linear operators. -/
def continuousLinearMapTrace : (E →L[ℝ] E) →L[ℝ] ℝ :=
  ({ toFun := fun A ↦ LinearMap.trace ℝ E A.toLinearMap
     map_add' := fun A B ↦ by simp
     map_smul' := fun c A ↦ by simp } : (E →L[ℝ] E) →ₗ[ℝ] ℝ).toContinuousLinearMap

/-- A `C²` function has a uniformly bounded Hessian trace on each closed ball.
The bound is obtained from compactness, without any global Hessian bound. -/
theorem exists_trace_hessian_bound_closedBall
    {H : E → ℝ} (hH : ContDiff ℝ 2 H) (K : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p, ‖p‖ ≤ K →
      LinearMap.trace ℝ E (fderiv ℝ (∇ H) p).toLinearMap ≤ M := by
  have hcont := continuousLinearMapTrace.continuous.comp
    ((contDiff_gradient (n := 1) hH).continuous_fderiv one_ne_zero)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E) K).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max 0 M, le_max_left _ _, fun p hp ↦ ?_⟩
  exact (le_abs_self _).trans
    ((hM p (by simpa using hp)).trans (le_max_right _ _))

/-- The divergence of an average is at most a common divergence bound for
its integrand. The derivative and trace both commute with the actual integral. -/
theorem trace_fderiv_intervalIntegral_le
    {F : E × ℝ → E} (hF : ContDiff ℝ 1 F) (x : E) {C : ℝ}
    (hbound : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      LinearMap.trace ℝ E (fderiv ℝ (fun y ↦ F (y, r)) x).toLinearMap ≤ C) :
    LinearMap.trace ℝ E (fderiv ℝ (fun y ↦ ∫ r in (0 : ℝ)..1, F (y, r)) x).toLinearMap
      ≤ C := by
  let D : ℝ → E →L[ℝ] E := fun r ↦
    (fderiv ℝ F (x, r)).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hD : Continuous D :=
    ((hF.continuous_fderiv one_ne_zero).comp
      (continuous_const.prodMk continuous_id)).clm_comp continuous_const
  have hslice (r : ℝ) : fderiv ℝ (fun y ↦ F (y, r)) x = D r :=
    (((hF.differentiable one_ne_zero) (x, r)).hasFDerivAt.comp x
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) x r)).fderiv
  rw [(hasFDerivAt_intervalIntegral_of_contDiff hF 0 1 x).fderiv]
  change continuousLinearMapTrace (∫ r in (0 : ℝ)..1, D r) ≤ C
  rw [← continuousLinearMapTrace.intervalIntegral_comp_comm (hD.intervalIntegrable 0 1)]
  calc
    (∫ r in (0 : ℝ)..1, continuousLinearMapTrace (D r)) ≤ ∫ _ in (0 : ℝ)..1, C :=
      intervalIntegral.integral_mono_on (by norm_num)
        ((continuousLinearMapTrace.continuous.comp hD).intervalIntegrable 0 1)
        intervalIntegrable_const fun r hr ↦ by
          change LinearMap.trace ℝ E (D r).toLinearMap ≤ C
          rw [← hslice]
          exact hbound r hr
    _ = C := by simp

/-- Averaging the gradient of a convex Hamiltonian along segments preserves
the divergence bound obtained from its positive Hessian. -/
theorem trace_fderiv_averaged_gradient_le
    {H : E → ℝ} (hH : ContDiff ℝ 2 H) (hconv : ConvexOn ℝ Set.univ H)
    {p q : E → E} (hp : ContDiff ℝ 1 p) (hq : ContDiff ℝ 1 q)
    {x : E} {K C M : ℝ} (hC : 0 ≤ C)
    (hp_norm : ‖p x‖ ≤ K) (hq_norm : ‖q x‖ ≤ K)
    (hp_bound : ∀ v, ⟪v, fderiv ℝ p x v⟫ ≤ C * ‖v‖ ^ 2)
    (hq_bound : ∀ v, ⟪v, fderiv ℝ q x v⟫ ≤ C * ‖v‖ ^ 2)
    (hH_bound : ∀ a, ‖a‖ ≤ K →
      LinearMap.trace ℝ E (fderiv ℝ (∇ H) a).toLinearMap ≤ M) :
    LinearMap.trace ℝ E
      (fderiv ℝ (fun y ↦ ∫ r in (0 : ℝ)..1,
        ∇ H (r • p y + (1 - r) • q y)) x).toLinearMap ≤ C * M := by
  have hF : ContDiff ℝ 1 (fun z : E × ℝ ↦
      ∇ H (z.2 • p z.1 + (1 - z.2) • q z.1)) :=
    (contDiff_gradient (n := 1) hH).comp
      ((contDiff_snd.smul (hp.comp contDiff_fst)).add
        ((contDiff_const.sub contDiff_snd).smul (hq.comp contDiff_fst)))
  apply trace_fderiv_intervalIntegral_le hF x
  intro r hr
  have hr' : 0 ≤ 1 - r := sub_nonneg.mpr hr.2
  have hpq_norm : ‖r • p x + (1 - r) • q x‖ ≤ K := by
    calc
      ‖r • p x + (1 - r) • q x‖ ≤ r * ‖p x‖ + (1 - r) * ‖q x‖ := by
        simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr.1,
          abs_of_nonneg hr'] using norm_add_le (r • p x) ((1 - r) • q x)
      _ ≤ r * K + (1 - r) * K :=
        add_le_add (mul_le_mul_of_nonneg_left hp_norm hr.1)
          (mul_le_mul_of_nonneg_left hq_norm hr')
      _ = K := by cas
  have hpq : DifferentiableAt ℝ (fun y ↦ r • p y + (1 - r) • q y) x :=
    (((hp.differentiable one_ne_zero) x).const_smul r).add
      (((hq.differentiable one_ne_zero) x).const_smul (1 - r))
  apply (trace_fderiv_gradient_comp_le hH hconv hpq ?_).trans
    (mul_le_mul_of_nonneg_left (hH_bound _ hpq_norm) hC)
  intro v
  have hpr : DifferentiableAt ℝ (fun y ↦ r • p y) x :=
    ((hp.differentiable one_ne_zero) x).const_smul r
  have hqr : DifferentiableAt ℝ (fun y ↦ (1 - r) • q y) x :=
    ((hq.differentiable one_ne_zero) x).const_smul (1 - r)
  rw [fderiv_fun_add hpr hqr,
    fderiv_fun_const_smul ((hp.differentiable one_ne_zero) x),
    fderiv_fun_const_smul ((hq.differentiable one_ne_zero) x)]
  simp only [add_apply, smul_apply, inner_add_right,
    real_inner_smul_right]
  calc
    r * ⟪v, fderiv ℝ p x v⟫ + (1 - r) * ⟪v, fderiv ℝ q x v⟫ ≤
        r * (C * ‖v‖ ^ 2) + (1 - r) * (C * ‖v‖ ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left (hp_bound v) hr.1)
        (mul_le_mul_of_nonneg_left (hq_bound v) hr')
    _ = C * ‖v‖ ^ 2 := by ring

end PDE.Analysis
