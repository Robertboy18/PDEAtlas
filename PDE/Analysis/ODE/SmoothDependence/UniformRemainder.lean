/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.SmoothDependence

/-!
# Identifying the first variation from a uniform Taylor remainder

Uniform continuity of `Dv` on a convex set makes the nonlinear Taylor remainder
arbitrarily small relative to the displacement. A two-sided Grönwall estimate
propagates this control along a Lipschitz family of trajectories and identifies
the solution of the variational equation with the initial-state derivative.
This argument needs no second derivative of the vector field.
-/

@[expose] public section

namespace PDE.Analysis.ODE

noncomputable section

open Filter Metric Set
open scoped NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A norm differential inequality based at zero gives the same Grönwall
bound in either time direction. -/
theorem norm_le_gronwallBound_of_hasDerivAt_on_symmetric_interval
    (e e' : ℝ → E) {T : ℝ} (hT : 0 ≤ T) (δ M A : ℝ)
    (he : ∀ t ∈ Icc (-T) T, HasDerivAt e (e' t) t)
    (he0 : ‖e 0‖ ≤ δ)
    (hbound : ∀ t ∈ Icc (-T) T, ‖e' t‖ ≤ M * ‖e t‖ + A)
    {s : ℝ} (hs : s ∈ Icc (-T) T) :
    ‖e s‖ ≤ gronwallBound δ M A |s| := by
  by_cases hs0 : 0 ≤ s
  · have hsub : Icc 0 s ⊆ Icc (-T) T :=
      fun t ht ↦ ⟨(neg_nonpos.mpr hT).trans ht.1, ht.2.trans hs.2⟩
    have h := norm_le_gronwallBound_of_norm_deriv_right_le
      (δ := δ) (K := M) (ε := A) (a := 0) (b := s)
      (continuousOn_of_forall_continuousAt
        (fun t ht ↦ (he t (hsub ht)).continuousAt))
      (fun t ht ↦ (he t (hsub (Ico_subset_Icc_self ht))).hasDerivWithinAt)
      he0 (fun t ht ↦ hbound t (hsub (Ico_subset_Icc_self ht)))
      s ⟨hs0, le_rfl⟩
    simpa only [sub_zero, abs_of_nonneg hs0] using h
  · have hs0' : s ≤ 0 := le_of_not_ge hs0
    have hsub {t : ℝ} (ht : t ∈ Icc 0 (-s)) : -t ∈ Icc (-T) T := by
      constructor <;> linarith only [ht.1, ht.2, hs.1, hT]
    have hrev {t : ℝ} (ht : t ∈ Icc 0 (-s)) :
        HasDerivAt (fun τ ↦ e (-τ)) (-e' (-t)) t := by
      simpa only [Function.comp_def, neg_smul, one_smul] using
        (he (-t) (hsub ht)).scomp t (hasDerivAt_neg t)
    have h := norm_le_gronwallBound_of_norm_deriv_right_le
      (δ := δ) (K := M) (ε := A) (a := 0) (b := -s)
      (continuousOn_of_forall_continuousAt (fun _ ht ↦ (hrev ht).continuousAt))
      (fun _ ht ↦ (hrev (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (by simpa only [neg_zero] using he0)
      (fun t ht ↦ by
        simpa only [norm_neg] using hbound (-t) (hsub (Ico_subset_Icc_self ht)))
      (-s) ⟨neg_nonneg.mpr hs0', le_rfl⟩
    simpa only [neg_neg, sub_zero, abs_of_nonpos hs0'] using h

/-- A uniform bound on the nonlinear Taylor remainder bounds the difference
between two trajectories and the linearized displacement.

Unlike the quadratic estimate, this form can use a remainder obtained from
continuity of the first derivative alone. -/
theorem norm_flow_sub_sub_variation_le_of_remainder_bound
    (v : E → E) (flow : E → ℝ → E) (J : ℝ → E →L[ℝ] E)
    (q w : E) {T : ℝ} (hT : 0 ≤ T) (M A : ℝ)
    (hq0 : flow q 0 = q) (hw0 : flow w 0 = w)
    (hJ0 : J 0 = ContinuousLinearMap.id ℝ E)
    (hq : ∀ t ∈ Icc (-T) T, HasDerivAt (flow q) (v (flow q t)) t)
    (hw : ∀ t ∈ Icc (-T) T, HasDerivAt (flow w) (v (flow w t)) t)
    (hJ : ∀ t ∈ Icc (-T) T,
      HasDerivAt J ((fderiv ℝ v (flow q t)).comp (J t)) t)
    (hDv : ∀ t ∈ Icc (-T) T, ‖fderiv ℝ v (flow q t)‖ ≤ M)
    (hR : ∀ t ∈ Icc (-T) T,
      ‖v (flow w t) - v (flow q t) -
        fderiv ℝ v (flow q t) (flow w t - flow q t)‖ ≤ A)
    {s : ℝ} (hs : s ∈ Icc (-T) T) :
    ‖flow w s - flow q s - J s (w - q)‖ ≤ gronwallBound 0 M A |s| := by
  let e : ℝ → E := fun t ↦ flow w t - flow q t - J t (w - q)
  let e' : ℝ → E := fun t ↦
    v (flow w t) - v (flow q t) - fderiv ℝ v (flow q t) (J t (w - q))
  have he : ∀ t ∈ Icc (-T) T, HasDerivAt e (e' t) t := by
    intro t ht
    have happly := (hJ t ht).clm_apply (hasDerivAt_const (x := t) (c := w - q))
    have happly' : HasDerivAt (fun τ ↦ J τ (w - q))
        (fderiv ℝ v (flow q t) (J t (w - q))) t := by
      simpa only [ContinuousLinearMap.comp_apply, map_zero, add_zero] using happly
    exact ((hw t ht).sub (hq t ht)).sub happly'
  have he0 : ‖e 0‖ ≤ 0 := by
    simp only [e, hq0, hw0, hJ0, ContinuousLinearMap.id_apply, sub_self, norm_zero, le_refl]
  have hbound : ∀ t ∈ Icc (-T) T, ‖e' t‖ ≤ M * ‖e t‖ + A := by
    intro t ht
    have hsplit : e' t = fderiv ℝ v (flow q t) (e t) +
        (v (flow w t) - v (flow q t) -
          fderiv ℝ v (flow q t) (flow w t - flow q t)) := by
      dsimp only [e, e']
      simp only [map_sub]
      abel
    rw [hsplit]
    calc
      _ ≤ ‖fderiv ℝ v (flow q t) (e t)‖ +
          ‖v (flow w t) - v (flow q t) -
            fderiv ℝ v (flow q t) (flow w t - flow q t)‖ := norm_add_le _ _
      _ ≤ ‖fderiv ℝ v (flow q t)‖ * ‖e t‖ + A :=
        add_le_add ((fderiv ℝ v (flow q t)).le_opNorm _) (hR t ht)
      _ ≤ M * ‖e t‖ + A := by gcongr; exact hDv t ht
  exact norm_le_gronwallBound_of_hasDerivAt_on_symmetric_interval
    e e' hT 0 M A he he0 hbound hs

/-- Uniform continuity of `Dv` on a convex set controls the first-order Taylor
remainder uniformly in its basepoint. The conclusion needs no second derivative. -/
theorem exists_uniform_taylor_remainder
    (v : E → E) (S : Set E) (hv : Differentiable ℝ v) (hS : Convex ℝ S)
    (hDv : UniformContinuousOn (fderiv ℝ v) S) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, ∀ y ∈ S, dist y x < δ →
      ‖v y - v x - fderiv ℝ v x (y - x)‖ ≤ η * ‖y - x‖ := by
  obtain ⟨δ, hδ, hcontrol⟩ := Metric.uniformContinuousOn_iff.mp hDv η hη
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxy
  apply Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z _ ↦ (hv z).hasFDerivAt.hasFDerivWithinAt)
    (fun z hz ↦ ?_) (convex_segment x y)
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  have hzx : dist z x < δ :=
    (mem_closedBall.mp (segment_subset_closedBall_left x y hz)).trans_lt
      (by simpa only [dist_comm] using hxy)
  simpa only [dist_eq_norm] using
    (hcontrol z (hS.segment_subset hx hy hz) x hx hzx).le

/-- Identify the first variation using an arbitrarily small linear Taylor
remainder on the trajectories. This is the form needed for a `C¹` vector field:
the modulus of continuity of `Dv` replaces a bound on `D²v`. -/
theorem hasFDerivAt_flow_of_small_remainder
    (v : E → E) (flow : E → ℝ → E) (J : ℝ → E →L[ℝ] E)
    (q : E) {ρ T : ℝ} (hρ : 0 < ρ) (hT : 0 ≤ T) (M : ℝ)
    (hinitial : ∀ w ∈ ball q ρ, flow w 0 = w)
    (hflow : ∀ w ∈ ball q ρ, ∀ t ∈ Icc (-T) T,
      HasDerivAt (flow w) (v (flow w t)) t)
    (hJ0 : J 0 = ContinuousLinearMap.id ℝ E)
    (hJ : ∀ t ∈ Icc (-T) T,
      HasDerivAt J ((fderiv ℝ v (flow q t)).comp (J t)) t)
    (hDv : ∀ t ∈ Icc (-T) T, ‖fderiv ℝ v (flow q t)‖ ≤ M)
    (hR : ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧
      ∀ w ∈ ball q r, ∀ t ∈ Icc (-T) T,
        ‖v (flow w t) - v (flow q t) -
          fderiv ℝ v (flow q t) (flow w t - flow q t)‖ ≤ η * ‖w - q‖)
    {s : ℝ} (hs : s ∈ Icc (-T) T) :
    HasFDerivAt (fun w ↦ flow w s) (J s) q := by
  rw [hasFDerivAt_iff_tendsto]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let G : ℝ := gronwallBound 0 M 1 |s|
  let η : ℝ := ε / (|G| + 1)
  have hden : 0 < |G| + 1 := by positivity
  have hη : 0 < η := div_pos hε hden
  obtain ⟨r, hr, hrem⟩ := hR η hη
  filter_upwards [ball_mem_nhds q (lt_min hρ hr)] with w hw
  have hwρ : w ∈ ball q ρ :=
    mem_ball.mpr ((mem_ball.mp hw).trans_le (min_le_left _ _))
  have hwr : w ∈ ball q r :=
    mem_ball.mpr ((mem_ball.mp hw).trans_le (min_le_right _ _))
  have hb := norm_flow_sub_sub_variation_le_of_remainder_bound v flow J q w hT
    M (η * ‖w - q‖) (hinitial q (mem_ball_self hρ)) (hinitial w hwρ)
    hJ0 (hflow q (mem_ball_self hρ)) (hflow w hwρ) hJ hDv
    (fun t ht ↦ hrem w hwr t ht) hs
  have hG : gronwallBound 0 M (η * ‖w - q‖) |s| = (η * ‖w - q‖) * G := by
    simpa only [one_mul, G] using gronwallBound_zero_mul M 1 (η * ‖w - q‖) |s|
  rw [hG] at hb
  have hsmall : η * |G| < ε := by
    have hcancel : η * (|G| + 1) = ε := div_mul_cancel₀ ε hden.ne'
    nlinarith only [hcancel, hη]
  have hnonneg : 0 ≤ ‖w - q‖⁻¹ * ‖flow w s - flow q s - J s (w - q)‖ :=
    mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)
  have hlt : ‖w - q‖⁻¹ * ‖flow w s - flow q s - J s (w - q)‖ < ε := by
    by_cases hwq : w = q
    · simpa only [hwq, sub_self, map_zero, norm_zero, inv_zero, mul_zero] using hε
    · have hn : ‖w - q‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hwq)
      calc
        _ ≤ ‖w - q‖⁻¹ * ((η * ‖w - q‖) * G) :=
          mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (norm_nonneg _))
        _ = η * G := by field_simp
        _ ≤ η * |G| := mul_le_mul_of_nonneg_left (le_abs_self G) hη.le
        _ < ε := hsmall
  have habs : |‖w - q‖⁻¹ * ‖flow w s - flow q s - J s (w - q)‖| < ε := by
    rwa [abs_of_nonneg hnonneg]
  simpa only [Real.dist_eq, sub_zero, map_sub] using habs

/-- Identify a first variation from a Lipschitz trajectory family in a convex
set where `Dv` is uniformly continuous. The small Taylor remainder follows
from these hypotheses. -/
theorem hasFDerivAt_flow_of_uniformContinuous_fderiv
    (v : E → E) (S : Set E) (hv : Differentiable ℝ v) (hS : Convex ℝ S)
    (hDvcont : UniformContinuousOn (fderiv ℝ v) S)
    (flow : E → ℝ → E) (J : ℝ → E →L[ℝ] E)
    (q : E) {ρ T : ℝ} (hρ : 0 < ρ) (hT : 0 ≤ T) (M : ℝ) (C : ℝ≥0)
    (hinitial : ∀ w ∈ ball q ρ, flow w 0 = w)
    (hflow : ∀ w ∈ ball q ρ, ∀ t ∈ Icc (-T) T,
      HasDerivAt (flow w) (v (flow w t)) t)
    (hJ0 : J 0 = ContinuousLinearMap.id ℝ E)
    (hJ : ∀ t ∈ Icc (-T) T,
      HasDerivAt J ((fderiv ℝ v (flow q t)).comp (J t)) t)
    (hDv : ∀ t ∈ Icc (-T) T, ‖fderiv ℝ v (flow q t)‖ ≤ M)
    (hvalues : ∀ w ∈ ball q ρ, ∀ t ∈ Icc (-T) T, flow w t ∈ S)
    (hLip : ∀ w ∈ ball q ρ, ∀ t ∈ Icc (-T) T,
      ‖flow w t - flow q t‖ ≤ C * ‖w - q‖)
    {s : ℝ} (hs : s ∈ Icc (-T) T) :
    HasFDerivAt (fun w ↦ flow w s) (J s) q := by
  apply hasFDerivAt_flow_of_small_remainder v flow J q hρ hT M
    hinitial hflow hJ0 hJ hDv ?_ hs
  intro η hη
  let θ : ℝ := η / ((C : ℝ) + 1)
  have hden : 0 < (C : ℝ) + 1 := by positivity
  have hθ : 0 < θ := div_pos hη hden
  have hθC : θ * C ≤ η := by
    have hcancel : θ * ((C : ℝ) + 1) = η := div_mul_cancel₀ η hden.ne'
    nlinarith only [hcancel, hθ]
  obtain ⟨δ, hδ, hTaylor⟩ := exists_uniform_taylor_remainder v S hv hS hDvcont hθ
  refine ⟨min ρ (δ / ((C : ℝ) + 1)),
    lt_min hρ (div_pos hδ hden), ?_⟩
  intro w hw t ht
  have hwρ : w ∈ ball q ρ :=
    mem_ball.mpr ((mem_ball.mp hw).trans_le (min_le_left _ _))
  have hwδ : ‖w - q‖ < δ / ((C : ℝ) + 1) := by
    simpa only [dist_eq_norm] using (mem_ball.mp hw).trans_le (min_le_right _ _)
  have hdist : dist (flow w t) (flow q t) < δ := by
    rw [dist_eq_norm]
    calc
      _ ≤ C * ‖w - q‖ := hLip w hwρ t ht
      _ ≤ ((C : ℝ) + 1) * ‖w - q‖ := by
        nlinarith only [norm_nonneg (w - q)]
      _ < δ := by
        simpa only [mul_comm] using (lt_div_iff₀ hden).mp hwδ
  calc
    _ ≤ θ * ‖flow w t - flow q t‖ :=
      hTaylor _ (hvalues q (mem_ball_self hρ) t ht) _ (hvalues w hwρ t ht) hdist
    _ ≤ θ * (C * ‖w - q‖) :=
      mul_le_mul_of_nonneg_left (hLip w hwρ t ht) hθ.le
    _ ≤ η * ‖w - q‖ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hθC (norm_nonneg _)

end

end PDE.Analysis.ODE
