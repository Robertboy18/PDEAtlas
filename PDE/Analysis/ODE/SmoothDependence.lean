/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.ODE.Gronwall

/-!
# Smooth dependence of autonomous ODE flows

Mathlib's Picard–Lindelöf theorem gives a local flow; here we prove that
it is differentiable in the initial state.  For an autonomous ODE

`q' = v(q)`,

the Fréchet derivative of the flow with respect to its initial state is
the solution of the first-variation equation

`J' = Dv(q) ∘ J`, `J(0) = id`.

Differentiability of solutions with respect to initial conditions is a classical theorem of
ODE theory. Evans uses it for the characteristic ODE (31) in §3.2.4: Lemma 2 applies the
inverse function theorem to `(y, s) ↦ x(y, s)`, and the proof of Theorem 2 differentiates the
solutions in the initial point `y`.

## Main results

* `norm_sub_sub_fderiv_le_of_lipschitzOn_fderiv`: a Lipschitz derivative on a
  convex set gives the quadratic Taylor remainder
  `‖v y - v x - Dv(x)(y - x)‖ ≤ K ‖y - x‖²`.
* `norm_flow_sub_sub_variation_le_of_nonneg`,
  `norm_flow_sub_sub_variation_le_of_nonpos`: the Grönwall estimate for the
  error `e(s)` in positive and negative time.
* `hasFDerivAt_flow_of_firstVariation`: if `flow` solves `q' = v(q)` with
  `flow w 0 = w` on a ball of initial states, is Lipschitz in the initial
  state, and `variation q` solves the first-variation equation along `flow q`,
  then `w ↦ flow w s` is Fréchet differentiable at `q` with derivative
  `variation q s` for every `|s| < T`.

## How it works

We use the standard Grönwall comparison for the first-variation error, with the jointly
Lipschitz Picard–Lindelöf flow, the coupled trajectory/variation ODE from
`PDE.Analysis.ODE.FirstVariation` and a second-order mean-value estimate on a compact ball.
No differentiability of the flow is assumed. The error
`e(t) = flow w t - flow q t - J(t)(w - q)` satisfies `e' = Dv(flow q t) e + R(t)` with
remainder `‖R(t)‖ ≤ K₂ ‖flow w t - flow q t‖² ≤ K₂ C² ‖w - q‖²`, where `C` is the
initial-state Lipschitz constant of the flow. Grönwall's inequality, Mathlib's
`norm_le_gronwallBound_of_norm_deriv_right_le`, gives
`‖e(s)‖ ≤ gronwallBound 0 M (K₂ C² ‖w - q‖²) |s|`, which is `O(‖w - q‖²)` and hence
`o(‖w - q‖)`, so `J(s)` is the Fréchet derivative of `w ↦ flow w s`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.2.4, Lemma 2 (local invertibility) and Theorem 2
  (local existence theorem) with its proof, pp. 105-108. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Analysis.ODE

noncomputable section

open Filter Metric Set
open scoped NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A Lipschitz derivative gives the quadratic first-order Taylor
remainder used in the smooth-dependence proof. -/
theorem norm_sub_sub_fderiv_le_of_lipschitzOn_fderiv
    (v : E → E) (S : Set E) (K : ℝ≥0)
    (hv : Differentiable ℝ v)
    (hDv : LipschitzOnWith K (fderiv ℝ v) S)
    (hS : Convex ℝ S) {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    ‖v y - v x - fderiv ℝ v x (y - x)‖ ≤
      K * ‖y - x‖ ^ 2 := by
  have hbound (z) (hz : z ∈ segment ℝ x y) : ‖fderiv ℝ v z - fderiv ℝ v x‖ ≤ K * ‖y - x‖ := by
    rw [← dist_eq_norm (fderiv ℝ v z), ← dist_eq_norm' x y]
    exact (hDv.dist_le_mul z (hS.segment_subset hx hy hz) x hx).trans
      (by gcongr; exact mem_closedBall.mp (segment_subset_closedBall_left x y hz))
  have hmv := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ ↦ ((hv z).hasFDerivAt.sub (fderiv ℝ v x).hasFDerivAt).hasFDerivWithinAt) hbound
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  convert hmv using 1
  · simp only [Pi.sub_apply, map_sub]
    congr 1
    abel
  · ring

/-- The Grönwall bound with zero initial error is homogeneous in the
forcing error. -/
theorem gronwallBound_zero_mul (M a c t : ℝ) :
    gronwallBound 0 M (a * c) t =
      c * gronwallBound 0 M a t := by
  by_cases hM : M = 0
  · simp only [hM, gronwallBound_K0, zero_add]
    ring
  · rw [gronwallBound_of_K_ne_0 hM,
      gronwallBound_of_K_ne_0 hM]
    ring

/-- Quantitative differentiability estimate for positive time.

The assumptions are precisely the outputs and local estimates of the
Picard–Lindelöf construction: the flow and first variation solve their
ODEs, the flow is Lipschitz in its initial state, and the vector field has
a quadratic Taylor remainder along the relevant trajectories. -/
theorem norm_flow_sub_sub_variation_le_of_nonneg
    (v : E → E) (flow : E → ℝ → E)
    (variation : E → ℝ → (E →L[ℝ] E))
    (q q' : E) (ρ C M K₂ s : ℝ)
    (hρ : 0 < ρ) (hs0 : 0 ≤ s)
    (hq' : q' ∈ ball q ρ)
    (hflowInitial :
      ∀ w ∈ ball q ρ, flow w 0 = w)
    (hvariationInitial :
      variation q 0 = ContinuousLinearMap.id ℝ E)
    (hflowDeriv :
      ∀ w ∈ ball q ρ, ∀ t ∈ Icc 0 s,
        HasDerivAt (flow w) (v (flow w t)) t)
    (hvariationDeriv :
      ∀ t ∈ Icc 0 s,
        HasDerivAt (variation q)
          ((fderiv ℝ v (flow q t)).comp (variation q t)) t)
    (hflowLip :
      ∀ w ∈ ball q ρ, ∀ t ∈ Icc 0 s,
        ‖flow w t - flow q t‖ ≤ C * ‖w - q‖)
    (hDvBound :
      ∀ t ∈ Icc 0 s, ‖fderiv ℝ v (flow q t)‖ ≤ M)
    (hTaylor :
      ∀ w ∈ ball q ρ, ∀ t ∈ Icc 0 s,
        ‖v (flow w t) - v (flow q t) -
            fderiv ℝ v (flow q t) (flow w t - flow q t)‖ ≤
          K₂ * ‖flow w t - flow q t‖ ^ 2)
    (hK₂ : 0 ≤ K₂) :
    ‖flow q' s - flow q s - variation q s (q' - q)‖ ≤
      gronwallBound 0 M (K₂ * C ^ 2 * ‖q' - q‖ ^ 2) s := by
  have hq : q ∈ ball q ρ := mem_ball_self hρ
  -- the error `e(t) = flow q' t - flow q t - J(t)(q' - q)` and its derivative
  let e : ℝ → E := fun t ↦ flow q' t - flow q t - variation q t (q' - q)
  have he (t) (ht : t ∈ Icc 0 s) : HasDerivAt e
      (v (flow q' t) - v (flow q t) - fderiv ℝ v (flow q t) (variation q t (q' - q))) t := by
    simpa only [ContinuousLinearMap.comp_apply, map_zero, add_zero] using
      ((hflowDeriv q' hq' t ht).fun_sub (hflowDeriv q hq t ht)).fun_sub
        ((hvariationDeriv t ht).clm_apply (hasDerivAt_const t (q' - q)))
  -- `e' = Dv(flow q t) e + R(t)` with `‖R(t)‖ ≤ K₂ C² ‖q' - q‖²`
  have hbound (t) (ht : t ∈ Ico 0 s) :
      ‖v (flow q' t) - v (flow q t) - fderiv ℝ v (flow q t) (variation q t (q' - q))‖ ≤
        M * ‖e t‖ + K₂ * C ^ 2 * ‖q' - q‖ ^ 2 := by
    have ht' := Ico_subset_Icc_self ht
    have hsplit : v (flow q' t) - v (flow q t) - fderiv ℝ v (flow q t) (variation q t (q' - q)) =
        fderiv ℝ v (flow q t) (e t) +
          (v (flow q' t) - v (flow q t) - fderiv ℝ v (flow q t) (flow q' t - flow q t)) := by
      simp only [e, map_sub]
      abel
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add ((fderiv ℝ v _).le_of_opNorm_le (hDvBound t ht') _)
      ((hTaylor q' hq' t ht').trans ?_))
    calc K₂ * ‖flow q' t - flow q t‖ ^ 2 ≤ K₂ * (C * ‖q' - q‖) ^ 2 := by
          gcongr
          exact hflowLip q' hq' t ht'
      _ = K₂ * C ^ 2 * ‖q' - q‖ ^ 2 := by ring
  simpa [e] using norm_le_gronwallBound_of_norm_deriv_right_le (δ := 0)
    (continuousOn_of_forall_continuousAt fun t ht ↦ (he t ht).continuousAt)
    (fun t ht ↦ (he t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by simp [e, hflowInitial q' hq', hflowInitial q hq, hvariationInitial]) hbound s
    ⟨hs0, le_rfl⟩

/-- The negative-time counterpart of
`norm_flow_sub_sub_variation_le_of_nonneg`, obtained by reversing time and
the vector field. -/
theorem norm_flow_sub_sub_variation_le_of_nonpos
    (v : E → E) (flow : E → ℝ → E)
    (variation : E → ℝ → (E →L[ℝ] E))
    (q q' : E) (ρ C M K₂ s : ℝ)
    (hρ : 0 < ρ) (hs0 : s ≤ 0)
    (hq' : q' ∈ ball q ρ)
    (hflowInitial :
      ∀ w ∈ ball q ρ, flow w 0 = w)
    (hvariationInitial :
      variation q 0 = ContinuousLinearMap.id ℝ E)
    (hflowDeriv :
      ∀ w ∈ ball q ρ, ∀ t ∈ Icc s 0,
        HasDerivAt (flow w) (v (flow w t)) t)
    (hvariationDeriv :
      ∀ t ∈ Icc s 0,
        HasDerivAt (variation q)
          ((fderiv ℝ v (flow q t)).comp (variation q t)) t)
    (hflowLip :
      ∀ w ∈ ball q ρ, ∀ t ∈ Icc s 0,
        ‖flow w t - flow q t‖ ≤ C * ‖w - q‖)
    (hDvBound :
      ∀ t ∈ Icc s 0, ‖fderiv ℝ v (flow q t)‖ ≤ M)
    (hTaylor :
      ∀ w ∈ ball q ρ, ∀ t ∈ Icc s 0,
        ‖v (flow w t) - v (flow q t) -
            fderiv ℝ v (flow q t) (flow w t - flow q t)‖ ≤
          K₂ * ‖flow w t - flow q t‖ ^ 2)
    (hK₂ : 0 ≤ K₂) :
    ‖flow q' s - flow q s - variation q s (q' - q)‖ ≤
      gronwallBound 0 M (K₂ * C ^ 2 * ‖q' - q‖ ^ 2) (-s) := by
  have hmem {t : ℝ} (ht : t ∈ Icc 0 (-s)) : -t ∈ Icc s 0 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hvrev (t : ℝ) : fderiv ℝ (fun x ↦ -v x) (flow q (-t)) = -fderiv ℝ v (flow q (-t)) :=
    fderiv_fun_neg
  -- the positive-time estimate for the reversed field `-v` and the reversed flow
  simpa using norm_flow_sub_sub_variation_le_of_nonneg (fun x ↦ -v x) (fun w t ↦ flow w (-t))
    (fun w t ↦ variation w (-t)) q q' ρ C M K₂ (-s) hρ (neg_nonneg.mpr hs0) hq'
    (by simpa using hflowInitial) (by simpa using hvariationInitial)
    (fun w hw t ht ↦ by
      simpa only [Function.comp_def, neg_smul, one_smul] using
        (hflowDeriv w hw (-t) (hmem ht)).scomp t (hasDerivAt_neg t))
    (fun t ht ↦ by
      simpa only [Function.comp_def, hvrev, neg_smul, one_smul, ContinuousLinearMap.neg_comp]
        using (hvariationDeriv (-t) (hmem ht)).scomp t (hasDerivAt_neg t))
    (fun w hw t ht ↦ hflowLip w hw (-t) (hmem ht))
    (fun t ht ↦ by simpa [hvrev] using hDvBound (-t) (hmem ht))
    (fun w hw t ht ↦ by
      convert hTaylor w hw (-t) (hmem ht) using 1
      rw [hvrev, ← norm_neg]
      congr 1
      simp only [map_sub, neg_apply]
      abel)
    hK₂

/-- A local flow whose first variation solves the variational ODE is
Fréchet differentiable in its initial state.

This theorem is the analytic identification step: the matrix `variation`
is not assumed to be the derivative of `flow`.  That conclusion follows
from the ODEs, local initial-state Lipschitz control, a bound on `Dv`, and
the quadratic Taylor remainder. -/
theorem hasFDerivAt_flow_of_firstVariation
    (v : E → E) (flow : E → ℝ → E)
    (variation : E → ℝ → (E →L[ℝ] E))
    (q : E) (ρ T C M K₂ : ℝ)
    (hρ : 0 < ρ) (hT : 0 < T)
    (hflowInitial :
      ∀ w ∈ ball q ρ, flow w 0 = w)
    (hvariationInitial :
      variation q 0 = ContinuousLinearMap.id ℝ E)
    (hflowDeriv :
      ∀ w ∈ ball q ρ, ∀ t ∈ Icc (-T) T,
        HasDerivAt (flow w) (v (flow w t)) t)
    (hvariationDeriv :
      ∀ t ∈ Icc (-T) T,
        HasDerivAt (variation q)
          ((fderiv ℝ v (flow q t)).comp (variation q t)) t)
    (hflowLip :
      ∀ w ∈ ball q ρ, ∀ t ∈ Icc (-T) T,
        ‖flow w t - flow q t‖ ≤ C * ‖w - q‖)
    (hDvBound :
      ∀ t ∈ Icc (-T) T, ‖fderiv ℝ v (flow q t)‖ ≤ M)
    (hTaylor :
      ∀ w ∈ ball q ρ, ∀ t ∈ Icc (-T) T,
        ‖v (flow w t) - v (flow q t) -
            fderiv ℝ v (flow q t) (flow w t - flow q t)‖ ≤
          K₂ * ‖flow w t - flow q t‖ ^ 2)
    (hK₂ : 0 ≤ K₂)
    {s : ℝ} (hs : s ∈ Ioo (-T) T) :
    HasFDerivAt (fun w ↦ flow w s) (variation q s) q := by
  rw [hasFDerivAt_iff_tendsto]
  set G := gronwallBound 0 M (K₂ * C ^ 2) |s|
  -- the Grönwall estimate in either time direction: the error is `O(‖w - q‖²)`
  have hbound (w) (hw : w ∈ ball q ρ) :
      ‖flow w s - flow q s - variation q s (w - q)‖ ≤ ‖w - q‖ ^ 2 * G := by
    rw [← gronwallBound_zero_mul]
    rcases le_total 0 s with hs0 | hs0
    · have hsub : Icc 0 s ⊆ Icc (-T) T := Icc_subset_Icc (by linarith) hs.2.le
      simpa [abs_of_nonneg hs0] using norm_flow_sub_sub_variation_le_of_nonneg v flow variation
        q w ρ C M K₂ s hρ hs0 hw hflowInitial hvariationInitial
        (fun z hz t ht ↦ hflowDeriv z hz t (hsub ht)) (fun t ht ↦ hvariationDeriv t (hsub ht))
        (fun z hz t ht ↦ hflowLip z hz t (hsub ht)) (fun t ht ↦ hDvBound t (hsub ht))
        (fun z hz t ht ↦ hTaylor z hz t (hsub ht)) hK₂
    · have hsub : Icc s 0 ⊆ Icc (-T) T := Icc_subset_Icc hs.1.le hT.le
      simpa [abs_of_nonpos hs0] using norm_flow_sub_sub_variation_le_of_nonpos v flow variation
        q w ρ C M K₂ s hρ hs0 hw hflowInitial hvariationInitial
        (fun z hz t ht ↦ hflowDeriv z hz t (hsub ht)) (fun t ht ↦ hvariationDeriv t (hsub ht))
        (fun z hz t ht ↦ hflowLip z hz t (hsub ht)) (fun t ht ↦ hDvBound t (hsub ht))
        (fun z hz t ht ↦ hTaylor z hz t (hsub ht)) hK₂
  have hupper := (tendsto_norm_sub_self q).mul_const G
  rw [zero_mul] at hupper
  refine squeeze_zero' (.of_forall fun w ↦ by positivity) ?_ hupper
  filter_upwards [ball_mem_nhds q hρ] with w hw
  calc ‖w - q‖⁻¹ * ‖flow w s - flow q s - variation q s (w - q)‖
      ≤ ‖w - q‖⁻¹ * (‖w - q‖ ^ 2 * G) := mul_le_mul_of_nonneg_left (hbound w hw) (by positivity)
    _ = ‖w - q‖ * G := by rw [sq, ← mul_assoc, ← mul_assoc, inv_mul_mul_self]

end

end PDE.Analysis.ODE
