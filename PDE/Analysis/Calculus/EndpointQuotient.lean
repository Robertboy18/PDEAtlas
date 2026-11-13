/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.LHopital

import CAS.ExactTactic

/-!
# One-sided quotient traces and endpoint derivatives

A finite derivative trace and continuity at the endpoint determine the one-sided
derivative there. The derivative need only be supplied eventually on the open side.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace PDE.Analysis.Calculus

/-- Quotient and rescaled weight traces determine a weighted square trace. The source filter
is arbitrary, so the same identity applies at either spatial endpoint. -/
theorem tendsto_sq_mul_weight_of_quotient
    {X : Type*} {q d W : X → ℝ} {l : Filter X} {a b : ℝ}
    (hq : Tendsto (fun x ↦ q x / d x) l (𝓝 a))
    (hW : Tendsto (fun x ↦ d x ^ 2 * W x) l (𝓝 b))
    (hd : ∀ᶠ x in l, d x ≠ 0) :
    Tendsto (fun x ↦ q x ^ 2 * W x) l (𝓝 (a ^ 2 * b)) := by
  apply ((hq.pow 2).mul hW).congr'
  filter_upwards [hd] with x hx
  simp only [div_pow, ← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero 2 hx)]

/-- A finite normalized first-derivative trace gives a quadratic quotient trace.
Differentiability is needed only eventually to the right of the origin. -/
theorem tendsto_div_sq_of_deriv_div
    {q : ℝ → ℝ} {d : ℝ}
    (hq : ∀ᶠ x in 𝓝[>] 0, DifferentiableAt ℝ q x)
    (hc : ContinuousAt q 0) (hq0 : q 0 = 0)
    (hd : Tendsto (fun x ↦ deriv q x / x) (𝓝[>] 0) (𝓝 d)) :
    Tendsto (fun x ↦ q x / x ^ 2) (𝓝[>] 0) (𝓝 (d / 2)) := by
  apply HasDerivAt.lhopital_zero_nhdsGT (hq.mono fun _ hx ↦ hx.hasDerivAt)
    (Eventually.of_forall fun x ↦ (show HasDerivAt (fun y : ℝ ↦ y ^ 2) (2 * x) x by
      cas)) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero (by norm_num) (ne_of_gt hx)
  · simpa only [hq0] using hc.tendsto.mono_left nhdsWithin_le_nhds
  · simpa using ((tendsto_id.mono_left nhdsWithin_le_nhds :
      Tendsto (fun x : ℝ ↦ x) (𝓝[>] 0) (𝓝 0)).pow 2)
  · convert hd.div_const 2 using 1
    simp only [div_div, mul_comm]

/-- A zero first jet and a differentiable first derivative at the origin give
its quadratic trace, without a C² neighborhood assumption. -/
theorem tendsto_div_sq_of_origin_jet
    {q : ℝ → ℝ} (hq : ∀ᶠ x in 𝓝[>] 0, DifferentiableAt ℝ q x)
    (hc : ContinuousAt q 0) (hd : DifferentiableAt ℝ (deriv q) 0)
    (hq0 : q 0 = 0) (hqd0 : deriv q 0 = 0) :
    Tendsto (fun x ↦ q x / x ^ 2) (𝓝[>] 0) (𝓝 (deriv (deriv q) 0 / 2)) := by
  apply tendsto_div_sq_of_deriv_div hq hc hq0
  simpa only [zero_add, hqd0, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    hd.hasDerivAt.tendsto_slope_zero_right

/-- A local zero first jet has the expected quadratic quotient trace. -/
theorem tendsto_div_sq_of_contDiffAt
    {q : ℝ → ℝ} (hq : ContDiffAt ℝ 2 q 0)
    (hq0 : q 0 = 0) (hqd0 : deriv q 0 = 0) :
    Tendsto (fun x ↦ q x / x ^ 2) (𝓝[>] 0) (𝓝 (deriv (deriv q) 0 / 2)) := by
  apply tendsto_div_sq_of_origin_jet
    (((hq.eventually (by simp)).mono fun _ hx ↦
      hx.differentiableAt two_ne_zero).filter_mono nhdsWithin_le_nhds)
    hq.continuousAt
    ((hq.derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero) hq0 hqd0

/-- A finite one-sided derivative trace and a zero endpoint value determine the
normalized endpoint quotient, without a derivative across the endpoint. -/
theorem tendsto_div_endpoint_of_derivative_trace
    {q : ℝ → ℝ} {L r : ℝ}
    (hd : ∀ᶠ x in 𝓝[<] L, HasDerivAt q (deriv q x) x)
    (hzero : Tendsto q (𝓝[<] L) (𝓝 0))
    (htrace : Tendsto (deriv q) (𝓝[<] L) (𝓝 r)) :
    Tendsto (fun x ↦ q x / (L - x)) (𝓝[<] L) (𝓝 (-r)) := by
  apply HasDerivAt.lhopital_zero_nhdsLT hd
    (Eventually.of_forall fun x ↦ (show HasDerivAt (fun y : ℝ ↦ L - y) (-1) x by
      simpa using (hasDerivAt_id x).const_sub L))
    (Eventually.of_forall fun _ ↦ by norm_num) hzero ?_ ?_
  · simpa using (tendsto_const_nhds (x := L)).sub
      (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun x : ℝ ↦ x) (𝓝[<] L) (𝓝 L))
  · simpa only [div_neg, div_one] using htrace.neg

/-- Continuity at a left endpoint and a finite right-hand derivative trace give
the derivative within the closed half-line. No derivative at the endpoint is assumed. -/
theorem hasDerivWithinAt_Ici_of_derivative_trace
    {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousWithinAt f (Ici a) a)
    (hd : ∀ᶠ x in 𝓝[>] a, HasDerivAt f (f' x) x)
    (htrace : Tendsto f' (𝓝[>] a) (𝓝 b)) :
    HasDerivWithinAt f b (Ici a) a := by
  apply hasDerivWithinAt_Ici_of_tendsto_deriv
    (s := Ici a ∩ {x | HasDerivAt f (f' x) x})
    (fun _ hx ↦ hx.2.differentiableAt.differentiableWithinAt)
    (hf.mono inter_subset_left)
    (inter_mem (mem_of_superset self_mem_nhdsWithin Ioi_subset_Ici_self) hd)
  exact htrace.congr' (hd.mono fun _ hx ↦ hx.deriv.symm)

end PDE.Analysis.Calculus
