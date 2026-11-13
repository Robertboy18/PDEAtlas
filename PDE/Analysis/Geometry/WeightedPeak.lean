/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Weighted maxima inside a ball

Multiplying a continuous function by a positive power of its distance to the
unit sphere forces a positive maximum into the interior. On a sufficiently
small ball around that maximum, the original function grows by at most a
prescribed factor. The radius fraction is chosen before the function.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open Set Metric
open scoped Topology

/-- A radius fraction small enough that the boundary weight loses at most
the prescribed factor. -/
theorem exists_radius_fraction_pow_control (β : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ 1 ≤ (1 + ε) * (1 - θ) ^ β := by
  have hc : ContinuousAt (fun θ : ℝ ↦ (1 + ε) * (1 - θ) ^ β) 0 := by fun_prop
  have he : ∀ᶠ θ in 𝓝 (0 : ℝ), 1 < (1 + ε) * (1 - θ) ^ β :=
    hc (Ioi_mem_nhds (by simpa using hε))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  let θ := min (r / 2) (1 / 2)
  have hθ : 0 < θ := lt_min (half_pos hr) (by norm_num)
  have hθr : θ < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  refine ⟨θ, hθ, (min_le_right _ _).trans_lt (by norm_num), ?_⟩
  exact (hball (by simpa [Real.dist_eq, abs_of_pos hθ] using hθr)).le

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

/-- An interior weighted maximum controls the function on a ball whose radius
is proportional to the distance to the unit sphere. -/
theorem exists_weighted_peak
    {β : ℕ} (hβ : 0 < β) {θ ε : ℝ} (hθ₁ : θ < 1)
    (hε : 0 ≤ ε) (hcontrol : 1 ≤ (1 + ε) * (1 - θ) ^ β)
    {u : E → ℝ} (hu : ContinuousOn u (closedBall 0 1))
    (hnonneg : ∀ x ∈ closedBall (0 : E) 1, 0 ≤ u x)
    {x₀ : E} (hx₀ : x₀ ∈ ball (0 : E) 1) (hpos : 0 < u x₀) :
    ∃ z ∈ ball (0 : E) 1, 0 < u z ∧
      (∀ y ∈ closedBall (0 : E) 1,
        u y * (1 - ‖y‖) ^ β ≤ u z * (1 - ‖z‖) ^ β) ∧
      closedBall z (θ * (1 - ‖z‖)) ⊆ ball (0 : E) 1 ∧
      (∀ y ∈ closedBall z (θ * (1 - ‖z‖)), u y ≤ (1 + ε) * u z) := by
  let w := fun y : E ↦ u y * (1 - ‖y‖) ^ β
  have hw : ContinuousOn w (closedBall 0 1) :=
    hu.mul ((continuous_const.sub continuous_norm).pow β).continuousOn
  obtain ⟨z, hz, hmax⟩ := (isCompact_closedBall (0 : E) 1).exists_isMaxOn
    ⟨x₀, ball_subset_closedBall hx₀⟩ hw
  have hx₀norm : ‖x₀‖ < 1 := by simpa using hx₀
  have hweightpos : 0 < w z :=
    (mul_pos hpos (pow_pos (sub_pos.mpr hx₀norm) β)).trans_le
      (hmax (ball_subset_closedBall hx₀))
  have hznorm : ‖z‖ ≤ 1 := by simpa using hz
  have hzinterior : ‖z‖ < 1 := by
    by_contra hnot
    have heq : ‖z‖ = 1 := hznorm.antisymm (le_of_not_gt hnot)
    have hwzero : w z = 0 := by simp [w, heq, hβ.ne']
    exact (ne_of_gt hweightpos) hwzero
  have huz : 0 < u z := (mul_pos_iff_of_pos_right (pow_pos (sub_pos.mpr hzinterior) β)).mp
    hweightpos
  have hinside : closedBall z (θ * (1 - ‖z‖)) ⊆ ball (0 : E) 1 := by
    intro y hy
    have hyz : dist y z ≤ θ * (1 - ‖z‖) := hy
    have htri : ‖y‖ ≤ dist y z + ‖z‖ := by
      simpa only [dist_zero_right] using dist_triangle y z 0
    have hrad := mul_lt_mul_of_pos_right hθ₁ (sub_pos.mpr hzinterior)
    rw [mem_ball, dist_zero_right]
    linarith
  refine ⟨z, by simpa using hzinterior, huz, hmax, hinside, ?_⟩
  intro y hy
  have hyunit := ball_subset_closedBall (hinside hy)
  have hyz : dist y z ≤ θ * (1 - ‖z‖) := hy
  have htri : ‖y‖ ≤ dist y z + ‖z‖ := by
    simpa only [dist_zero_right] using dist_triangle y z 0
  have hdist : (1 - θ) * (1 - ‖z‖) ≤ 1 - ‖y‖ := by nlinarith
  have hdpos : 0 < 1 - ‖z‖ := sub_pos.mpr hzinterior
  have hleft : 0 ≤ (1 - θ) * (1 - ‖z‖) :=
    mul_nonneg (sub_nonneg.mpr hθ₁.le) hdpos.le
  have hpow := pow_le_pow_left₀ hleft hdist β
  have hweighted := (mul_le_mul_of_nonneg_left hpow (hnonneg y hyunit)).trans (hmax hyunit)
  rw [mul_pow, ← mul_assoc] at hweighted
  have hcancel : u y * (1 - θ) ^ β ≤ u z :=
    (mul_le_mul_iff_left₀ (pow_pos hdpos β)).mp hweighted
  have hmul := mul_le_mul_of_nonneg_left hcancel (show 0 ≤ 1 + ε by positivity)
  have hstart := mul_le_mul_of_nonneg_left hcontrol (hnonneg y hyunit)
  nlinarith

end PDE.Analysis
