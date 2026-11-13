/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.Symmetries

/-!
# Existence of real Hilbert principal values by local cancellation

Subtracting `f(x)` in a symmetric neighborhood of the singularity produces the
kernel `(f(x-t) - f(x) 1_{|t|<R}) / t`. If this kernel is integrable, its ordinary
integral divided by `π` is the Hilbert principal value. The subtracted kernel is odd, so every
symmetric truncation of it has integral zero.

For `L¹` inputs, a local Lipschitz bound at the evaluation point guarantees this
absolute integrability.
-/

@[expose] public section

namespace PDE.Analysis

open Filter MeasureTheory Set
open scoped NNReal Topology

noncomputable section

/-- The Hilbert kernel with its constant local singularity subtracted symmetrically. -/
def hilbertRegularizedKernel (f : ℝ → ℝ) (x R t : ℝ) : ℝ :=
  (f (x - t) - {s : ℝ | |s| < R}.indicator (fun _ ↦ f x) t) / t

/-- A bounded symmetric interval is measurable. -/
theorem measurableSet_hilbertLocal (R : ℝ) : MeasurableSet {t : ℝ | |t| < R} :=
  measurableSet_lt continuous_abs.measurable measurable_const

/-- Constants supported in a bounded symmetric interval are integrable. -/
theorem integrable_hilbertLocalConstant (R c : ℝ) :
    Integrable ({t : ℝ | |t| < R}.indicator (fun _ ↦ c)) := by
  have hs : {t : ℝ | |t| < R} = Ioo (-R) R := by
    ext t
    simp only [mem_ofPred_eq, mem_Ioo, abs_lt]
  rw [hs]
  exact (integrableOn_const (s := Ioo (-R) R) (C := c) measure_Ioo_lt_top.ne).integrable_indicator
    measurableSet_Ioo

/-- Dividing an integrable function by the coordinate is integrable outside a
positive cutoff. -/
theorem integrableOn_div_id_hilbertCutoff {g : ℝ → ℝ} (hg : Integrable g)
    {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t ↦ g t / t) {t : ℝ | ε < |t|} := by
  simpa only [zero_sub, neg_neg] using
    integrableOn_hilbertKernel hg.comp_neg 0 hε

/-- The subtracted local constant contributes zero to every symmetric truncation. -/
theorem integral_hilbertLocalConstant_div (R c ε : ℝ) :
    (∫ t in {t : ℝ | ε < |t|},
      {s : ℝ | |s| < R}.indicator (fun _ ↦ c) t / t) = 0 := by
  apply integral_hilbertCutoff_eq_zero_of_odd
  intro t
  simp [indicator, div_neg]

/-- An integrable regularized kernel provides integrability of the original positive
truncations. -/
theorem integrableOn_hilbertKernel_of_regularized {f : ℝ → ℝ} {x R : ℝ}
    (hf : Integrable (hilbertRegularizedKernel f x R)) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t ↦ f (x - t) / t) {t : ℝ | ε < |t|} := by
  have hc := integrableOn_div_id_hilbertCutoff
    (integrable_hilbertLocalConstant R (f x)) hε
  apply (hf.integrableOn.fun_add hc).congr_fun (hs := measurableSet_hilbertCutoff ε)
  intro t _
  simp [hilbertRegularizedKernel, sub_div]

/-- Symmetric constant subtraction preserves every positive truncated Hilbert integral. -/
theorem hilbertTruncation_eq_regularized {f : ℝ → ℝ} {x R : ℝ}
    (hf : Integrable (hilbertRegularizedKernel f x R)) {ε : ℝ} (hε : 0 < ε) :
    hilbertTruncation f x ε =
      Real.pi⁻¹ * ∫ t in {t : ℝ | ε < |t|}, hilbertRegularizedKernel f x R t := by
  have hc := integrableOn_div_id_hilbertCutoff
    (integrable_hilbertLocalConstant R (f x)) hε
  unfold hilbertTruncation
  have heq : (fun t ↦ f (x - t) / t) =
      (fun t ↦ hilbertRegularizedKernel f x R t +
        {s : ℝ | |s| < R}.indicator (fun _ ↦ f x) t / t) := by
    funext t
    simp [hilbertRegularizedKernel, sub_div]
  rw [heq, integral_add hf.integrableOn hc, integral_hilbertLocalConstant_div, add_zero]

/-- Absolute convergence after local constant cancellation gives a Hilbert
principal value, equal to the integral of the regularized kernel divided by `π`. -/
theorem hasHilbertPV_of_regularized {f : ℝ → ℝ} {x R : ℝ}
    (hf : Integrable (hilbertRegularizedKernel f x R)) :
    HasHilbertPV f x (Real.pi⁻¹ * ∫ t, hilbertRegularizedKernel f x R t) := by
  refine ⟨fun _ hε ↦ integrableOn_hilbertKernel_of_regularized hf hε, ?_⟩
  apply ((tendsto_integral_hilbertCutoff hf).const_mul Real.pi⁻¹).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hilbertTruncation_eq_regularized hf hε).symm

/-- For an `L¹` input, a local Lipschitz bound at `x` makes the regularized Hilbert
kernel integrable. Only differences from `f(x)` need to satisfy the bound. -/
theorem integrable_hilbertRegularizedKernel {f : ℝ → ℝ} (hf : Integrable f)
    {x R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hlocal : ∀ t : ℝ, |t| < R → |f (x - t) - f x| ≤ C * |t|) :
    Integrable (hilbertRegularizedKernel f x R) := by
  have hmeas : AEStronglyMeasurable (hilbertRegularizedKernel f x R) volume :=
    ((hf.comp_sub_left x).aestronglyMeasurable.sub
      (integrable_hilbertLocalConstant R (f x)).aestronglyMeasurable).div₀
        measurable_id.aestronglyMeasurable
  have hnear : IntegrableOn (hilbertRegularizedKernel f x R) {t : ℝ | |t| < R} := by
    have hconst : IntegrableOn (fun _ : ℝ ↦ C) {t : ℝ | |t| < R} :=
      (integrable_indicator_iff (measurableSet_hilbertLocal R)).mp
        (integrable_hilbertLocalConstant R C)
    apply hconst.mono' hmeas.restrict
    filter_upwards [ae_restrict_mem (measurableSet_hilbertLocal R)] with t ht
    rw [hilbertRegularizedKernel, indicator_of_mem (s := {t : ℝ | |t| < R}) ht]
    simp only [norm_div, Real.norm_eq_abs]
    by_cases ht0 : t = 0
    · simp only [ht0, abs_zero, div_zero]
      exact hC
    · exact (div_le_iff₀ (abs_pos.mpr ht0)).mpr (hlocal t ht)
  have hfar : IntegrableOn (hilbertRegularizedKernel f x R) {t : ℝ | |t| < R}ᶜ := by
    have hsub : {t : ℝ | |t| < R}ᶜ ⊆ {t : ℝ | R / 2 < |t|} := by
      intro t ht
      have ht' : R ≤ |t| := le_of_not_gt ht
      exact (half_lt_self hR).trans_le ht'
    apply ((integrableOn_hilbertKernel hf x (half_pos hR)).mono_set hsub).congr_fun
      (hs := (measurableSet_hilbertLocal R).compl)
    intro t ht
    simp [hilbertRegularizedKernel, indicator_of_notMem ht]
  simpa only [union_compl_self, integrableOn_univ] using hnear.union hfar

/-- An integrable input satisfying a local Lipschitz bound has a principal value;
the result also supplies its absolutely convergent cancellation formula. -/
theorem hasHilbertPV_of_local_lipschitz_bound {f : ℝ → ℝ} (hf : Integrable f)
    {x R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hlocal : ∀ t : ℝ, |t| < R → |f (x - t) - f x| ≤ C * |t|) :
    HasHilbertPV f x (Real.pi⁻¹ * ∫ t, hilbertRegularizedKernel f x R t) :=
  hasHilbertPV_of_regularized (integrable_hilbertRegularizedKernel hf hR hC hlocal)

/-- A local `LipschitzOnWith` hypothesis supplies the cancellation formula directly. -/
theorem hasHilbertPV_of_lipschitzOnWith {f : ℝ → ℝ} (hf : Integrable f)
    {x R : ℝ} {C : ℝ≥0} (hR : 0 < R) (hlocal : LipschitzOnWith C f (Metric.ball x R)) :
    HasHilbertPV f x (Real.pi⁻¹ * ∫ t, hilbertRegularizedKernel f x R t) := by
  apply hasHilbertPV_of_local_lipschitz_bound hf hR C.coe_nonneg
  intro t ht
  have hmem : x - t ∈ Metric.ball x R := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_sub_cancel_left, abs_neg] using ht
  simpa only [Real.norm_eq_abs, sub_sub_cancel_left, abs_neg] using
    hlocal.norm_sub_le hmem (Metric.mem_ball_self hR)

/-- Differentiability at the evaluation point gives an integrable regularized kernel
for some positive cancellation radius. -/
theorem exists_integrable_hilbertRegularizedKernel_of_differentiableAt
    {f : ℝ → ℝ} (hf : Integrable f)
    {x : ℝ} (hdiff : DifferentiableAt ℝ f x) :
    ∃ R : ℝ, 0 < R ∧ Integrable (hilbertRegularizedKernel f x R) := by
  obtain ⟨C, hC, hbound⟩ := hdiff.isBigO_sub.exists_nonneg
  obtain ⟨R, hR, hlocal⟩ := Metric.eventually_nhds_iff.mp hbound.bound
  have hcancel : ∀ t : ℝ, |t| < R → |f (x - t) - f x| ≤ C * |t| := by
    intro t ht
    have hdist : dist (x - t) x < R := by
      simpa only [Real.dist_eq, sub_sub_cancel_left, abs_neg] using ht
    simpa only [Real.norm_eq_abs, sub_sub_cancel_left, abs_neg] using hlocal hdist
  exact ⟨R, hR, integrable_hilbertRegularizedKernel hf hR hC hcancel⟩

/-- An integrable real function has a Hilbert principal value at every point
where it is differentiable. Differentiability supplies the local cancellation bound. -/
theorem hasHilbertPV_of_differentiableAt {f : ℝ → ℝ} (hf : Integrable f)
    {x : ℝ} (hdiff : DifferentiableAt ℝ f x) :
    HasHilbertPV f x (hilbertPV f x) := by
  obtain ⟨R, _, hint⟩ := exists_integrable_hilbertRegularizedKernel_of_differentiableAt hf hdiff
  have hpv := hasHilbertPV_of_regularized hint
  rw [hpv.hilbertPV_eq]
  exact hpv

/-- For an integrable input vanishing at zero, differentiability there implies
absolute integrability after division by the coordinate. -/
theorem integrable_div_id_of_differentiableAt_zero {f : ℝ → ℝ}
    (hf : Integrable f) (hzero : f 0 = 0) (hdiff : DifferentiableAt ℝ f 0) :
    Integrable (fun y ↦ f y / y) := by
  obtain ⟨R, _, hint⟩ := exists_integrable_hilbertRegularizedKernel_of_differentiableAt hf hdiff
  simpa [hilbertRegularizedKernel, hzero, div_neg] using hint.comp_neg

/-- Equation (A.1) follows from `L¹` tails, vanishing at zero, and differentiability
at zero and the evaluation point. No principal-value existence assumption is needed. -/
theorem hilbertPV_div_id_of_differentiableAt {f : ℝ → ℝ} (hf : Integrable f)
    (hzero : f 0 = 0) (hdiff0 : DifferentiableAt ℝ f 0)
    {x : ℝ} (hx : x ≠ 0) (hdiff : DifferentiableAt ℝ f x) :
    hilbertPV (fun y ↦ f y / y) x = (hilbertPV f x - hilbertPV f 0) / x :=
  hilbertPV_div_id (hasHilbertPV_of_differentiableAt hf hdiff)
    (integrable_div_id_of_differentiableAt_zero hf hzero hdiff0) hx

end

end PDE.Analysis
