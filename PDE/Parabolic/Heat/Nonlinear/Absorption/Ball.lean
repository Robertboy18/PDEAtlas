/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Nonlinear.Absorption.Barrier
public import PDE.Parabolic.Heat.Nonlinear.Absorption.Comparison
import PDE.FDeriv.Calculus
import CAS.ExactTactic

/-!
# Interior-ball bounds for quadratic absorption

The singular barrier bounds a subsolution with nonpositive initial values.
Applied to the negative of a quadratic heat solution, it gives a bound
proportional to time divided by the fourth power of the boundary distance.
-/

@[expose] public noncomputable section

open Filter Set
open PDE (laplacian)
open ParabolicMaximum
open scoped Topology

namespace HeatEquation.Nonlinear

/-- A quadratic absorption subsolution with nonpositive initial values has a
weighted upper bound on each compact ball. Its lateral values are unrestricted. -/
theorem quadratic_absorption_ball_weighted_le
    {n : ℕ} {c : ℝ^n} {r T : ℝ} {v : ℝ^n → ℝ → ℝ}
    (hr : 0 < r) (hT : 0 < T)
    (hvc : ContinuousOn (fun q : ℝ^n × ℝ ↦ v q.1 q.2)
      (closedCylinder (Metric.ball c r) T))
    (hvs : ∀ x ∈ Metric.ball c r, ∀ t ∈ Ioc 0 T,
      ContDiffAt ℝ 2 (fun y ↦ v y t) x)
    (hvt : ∀ x ∈ Metric.ball c r, ∀ t ∈ Ioc 0 T, DifferentiableAt ℝ (v x) t)
    (hv : ∀ x ∈ Metric.ball c r, ∀ t ∈ Ioc 0 T,
      heatParabolicOperator v x t ≤ -(v x t) ^ 2)
    (hv0 : ∀ x ∈ Metric.closedBall c r, v x 0 ≤ 0) :
    ∀ x ∈ Metric.closedBall c r, ∀ t ∈ Icc 0 T,
      (r ^ 2 - ‖x - c‖ ^ 2) ^ 4 * v x t ≤ ((4 * (n : ℝ) + 40) * r ^ 2) ^ 2 * t := by
  let a : ℝ := (4 * (n : ℝ) + 40) * r ^ 2
  let p : ℝ^n → ℝ := fun x ↦ (r ^ 2 - ‖x - c‖ ^ 2) ^ 4
  let B : ℝ → ℝ^n → ℝ → ℝ := fun M x t ↦
    ballAbsorptionBarrier a (r ^ 2) (x - c) (t + M / a ^ 2)
  have ha : 0 < a := mul_pos (by positivity) (sq_pos_of_pos hr)
  have hq (x : ℝ^n) (hx : x ∈ Metric.ball c r) : ‖x - c‖ ^ 2 < r ^ 2 :=
    (sq_lt_sq₀ (norm_nonneg _) hr.le).mpr (by
      simpa only [Metric.mem_ball, dist_eq_norm] using hx)
  have hp (x : ℝ^n) (hx : x ∈ Metric.ball c r) : 0 < p x :=
    pow_pos (sub_pos.mpr (hq x hx)) 4
  have hc : closure (Metric.ball c r) = Metric.closedBall c r := closure_ball c hr.ne'
  have hpc : Continuous p := by dsimp only [p]; fun_prop
  have hBs (M : ℝ) (x : ℝ^n) (hx : x ∈ Metric.ball c r) (t : ℝ) :
      ContDiffAt ℝ 2 (fun y ↦ B M y t) x := by
    have h := (ballAbsorptionBarrier_contDiffAt a (r ^ 2) (t + M / a ^ 2)
      (sub_pos.mpr (hq x hx)).ne').comp x (contDiffAt_id.sub (contDiffAt_const (c := c)))
    exact h
  have hBt (M : ℝ) (x : ℝ^n) (hx : x ∈ Metric.ball c r) (t : ℝ) :
      DifferentiableAt ℝ (B M x) t :=
    (HasDerivAt.comp_add_const t (M / a ^ 2)
      (ballAbsorptionBarrier_hasDerivAt a (r ^ 2) (t + M / a ^ 2) (x - c)
        (sub_pos.mpr (hq x hx)).ne')).differentiableAt
  have hop (M : ℝ) (x : ℝ^n) (hx : x ∈ Metric.ball c r) (t : ℝ) :
      heatParabolicOperator (B M) x t =
        heatParabolicOperator (ballAbsorptionBarrier a (r ^ 2)) (x - c)
          (t + M / a ^ 2) := by
    unfold heatParabolicOperator
    dsimp only [B]
    rw [deriv_comp_add_const, PDE.laplacian_comp_sub_right _ c x
      (ballAbsorptionBarrier_contDiffAt a (r ^ 2) (t + M / a ^ 2)
        (sub_pos.mpr (hq x hx)).ne')]
  have h := weighted_quadratic_absorption_le Metric.isOpen_ball
    (Metric.nonempty_ball.mpr hr) (by rw [hc]; exact isCompact_closedBall c r) hT
    (sq_nonneg a) hpc.continuousOn hp (fun x _ ↦ by dsimp [p]; positivity) (by
      intro x hx
      have hxnorm : ‖x - c‖ = r := by
        simpa only [Metric.mem_sphere, dist_eq_norm] using
          Metric.frontier_ball_subset_sphere hx
      norm_num [p, hxnorm])
    hvc hvs hvt hv (by rwa [hc]) (B := B) (by
      intro M _hM x hx t _ht
      have hd := (sub_pos.mpr (hq x hx)).ne'
      have ha0 := ha.ne'
      dsimp only [p, B]
      unfold ballAbsorptionBarrier
      generalize r ^ 2 - ‖x - c‖ ^ 2 = s at hd ⊢
      generalize a = k at ha0 ⊢
      cas using [hd, ha0])
    (fun M _hM x hx t _ht ↦ hBs M x hx t)
    (fun M _hM x hx t _ht ↦ hBt M x hx t) (by
      intro M hM x hx t ht
      rw [hop M x hx t]
      exact ballAbsorptionBarrier_strict_supersolution (x - c)
        (add_pos ht.1 (div_pos hM (sq_pos_of_pos ha))) (hq x hx))
  intro x hx t ht
  exact h (x, t) ⟨hc.symm ▸ hx, ht⟩

/-- The center estimate has parabolic scaling `t / r^4`. Only the initial values
and regularity on the compact interior ball are used, not an original domain corner. -/
theorem quadratic_absorption_ball_center_le
    {n : ℕ} {c : ℝ^n} {r T : ℝ} {v : ℝ^n → ℝ → ℝ}
    (hr : 0 < r) (hT : 0 < T)
    (hvc : ContinuousOn (fun q : ℝ^n × ℝ ↦ v q.1 q.2)
      (closedCylinder (Metric.ball c r) T))
    (hvs : ∀ x ∈ Metric.ball c r, ∀ t ∈ Ioc 0 T,
      ContDiffAt ℝ 2 (fun y ↦ v y t) x)
    (hvt : ∀ x ∈ Metric.ball c r, ∀ t ∈ Ioc 0 T, DifferentiableAt ℝ (v x) t)
    (hv : ∀ x ∈ Metric.ball c r, ∀ t ∈ Ioc 0 T,
      heatParabolicOperator v x t ≤ -(v x t) ^ 2)
    (hv0 : ∀ x ∈ Metric.closedBall c r, v x 0 ≤ 0) {t : ℝ} (ht : t ∈ Icc 0 T) :
    v c t ≤ (4 * (n : ℝ) + 40) ^ 2 * t / r ^ 4 := by
  have h := quadratic_absorption_ball_weighted_le hr hT hvc hvs hvt hv hv0 c
    (Metric.mem_closedBall_self hr.le) t ht
  rw [sub_self, norm_zero, zero_pow two_ne_zero, sub_zero] at h
  calc
    v c t ≤ ((4 * (n : ℝ) + 40) * r ^ 2) ^ 2 * t / (r ^ 2) ^ 4 :=
      (le_div_iff₀ (pow_pos (sq_pos_of_pos hr) 4)).mpr (by simpa only [mul_comm] using h)
    _ = (4 * (n : ℝ) + 40) ^ 2 * t / r ^ 4 := by
      generalize 4 * (n : ℝ) + 40 = a
      cas using hr.ne'

/-- The signed quadratic heat equation has an initial-time lower bound
at the center of every closed ball contained in the spatial interior. Only
local initial continuity is used; no original boundary corner is included. -/
theorem neg_le_ball_bound_of_square_equation
    {n : ℕ} {Ω : Set (ℝ^n)} {T r : ℝ} {c : ℝ^n} {u : ℝ → ℝ^n → ℝ}
    (hr : 0 < r)
    (hball : Metric.closedBall c r ⊆ Ω)
    (hc : ContinuousOn u.uncurry (Icc 0 T ×ˢ Ω))
    (hs : ContDiffOn ℝ 2 u.uncurry (Ioi 0 ×ˢ Ω))
    (heq : ∀ t > 0, ∀ x ∈ Ω,
      deriv (fun s ↦ u s x) t - laplacian (u t) x = u t x ^ 2)
    (hinit : ∀ x ∈ Ω, 0 ≤ u 0 x)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    -u t c ≤ (4 * (n : ℝ) + 40) ^ 2 * t / r ^ 4 := by
  rcases (ht.1.trans ht.2).eq_or_lt with hT0 | hT
  · obtain rfl : t = 0 := le_antisymm (ht.2.trans hT0.ge) ht.1
    simpa using hinit c (hball (Metric.mem_closedBall_self hr.le))
  have hbc : closure (Metric.ball c r) = Metric.closedBall c r := closure_ball c hr.ne'
  have hmem (x : ℝ^n) (hx : x ∈ Metric.ball c r) : x ∈ Ω :=
    hball (Metric.ball_subset_closedBall hx)
  have hjoint (x : ℝ^n) (hx : x ∈ Metric.ball c r) (s : ℝ) (hs0 : 0 < s) :
      ContDiffAt ℝ 2 u.uncurry (s, x) :=
    hs.contDiffAt (Filter.mem_of_superset
      ((isOpen_Ioi.prod Metric.isOpen_ball).mem_nhds ⟨hs0, hx⟩) fun q hq ↦ ⟨hq.1, hmem q.2 hq.2⟩)
  have hspace (x : ℝ^n) (hx : x ∈ Metric.ball c r) (s : ℝ) (hs0 : 0 < s) :
      ContDiffAt ℝ 2 (u s) x :=
    (hjoint x hx s hs0).comp x (contDiffAt_const.prodMk (contDiffAt_id (x := x)))
  have htime (x : ℝ^n) (hx : x ∈ Metric.ball c r) (s : ℝ) (hs0 : 0 < s) :
      DifferentiableAt ℝ (fun q ↦ u q x) s :=
    ((hjoint x hx s hs0).comp s ((contDiffAt_id (x := s)).prodMk contDiffAt_const)).differentiableAt
      (by norm_num)
  refine quadratic_absorption_ball_center_le hr hT (v := fun x s ↦ -u s x)
    (hc.comp continuous_swap.continuousOn (fun q hq ↦ ⟨hq.2, hball (hbc ▸ hq.1)⟩)).neg
    (fun x hx s hs ↦ (hspace x hx s hs.1).neg) (fun x hx s hs ↦ (htime x hx s hs.1).neg)
    (fun x hx s hs ↦ ?_) (fun x hx ↦ neg_nonpos.mpr (hinit x (hball hx))) ht
  unfold heatParabolicOperator
  change deriv (-(fun q ↦ u q x)) s - laplacian (-(u s)) x ≤ -(-u s x) ^ 2
  rw [deriv.neg, PDE.laplacian_neg]
  nlinarith only [heq s hs.1 x (hmem x hx)]

/-- The local ball estimate gives a distance-to-boundary profile, with no
regularity assumption at the original initial/lateral corner. -/
theorem neg_le_infDist_bound_of_square_equation
    {n : ℕ} {Ω : Set (ℝ^n)} {T : ℝ} {u : ℝ → ℝ^n → ℝ}
    (hΩ : IsOpen Ω) (hne : Ωᶜ.Nonempty)
    (hc : ContinuousOn u.uncurry (Icc 0 T ×ˢ Ω))
    (hs : ContDiffOn ℝ 2 u.uncurry (Ioi 0 ×ˢ Ω))
    (heq : ∀ t > 0, ∀ x ∈ Ω,
      deriv (fun s ↦ u s x) t - laplacian (u t) x = u t x ^ 2)
    (hinit : ∀ x ∈ Ω, 0 ≤ u 0 x)
    {t : ℝ} (ht : t ∈ Icc 0 T) {x : ℝ^n} (hx : x ∈ Ω) :
    -u t x ≤ 16 * (4 * (n : ℝ) + 40) ^ 2 * t / Metric.infDist x Ωᶜ ^ 4 := by
  have hd : 0 < Metric.infDist x Ωᶜ :=
    (hΩ.isClosed_compl.notMem_iff_infDist_pos hne).mp (not_not.mpr hx)
  have hball : Metric.closedBall x (Metric.infDist x Ωᶜ / 2) ⊆ Ω :=
    (Metric.closedBall_subset_ball (half_lt_self hd)).trans Metric.ball_infDist_compl_subset
  have h := neg_le_ball_bound_of_square_equation (half_pos hd) hball
    hc hs heq hinit ht
  calc
    -u t x ≤ (4 * (n : ℝ) + 40) ^ 2 * t / (Metric.infDist x Ωᶜ / 2) ^ 4 := h
    _ = 16 * (4 * (n : ℝ) + 40) ^ 2 * t / Metric.infDist x Ωᶜ ^ 4 := by
      generalize 4 * (n : ℝ) + 40 = a
      generalize Metric.infDist x Ωᶜ = d at hd ⊢
      cas using hd.ne'

end HeatEquation.Nonlinear
