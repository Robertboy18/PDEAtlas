/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Geometry.WeightedPeak
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real

/-!
# Weighted peaks with a past time interval

Folding time by `t ↦ -|t|` transfers the weighted-maximum theorem `exists_weighted_peak`
on a product ball to a cylinder ending at time zero. The fold is used only
for continuous functions, so it introduces no differentiability assumption
at the final time. The resulting local upper bound applies to a backward
cylinder around the peak and leaves the future available for propagation.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

/-- A positive value in the past cylinder yields a weighted peak no later than
time zero. A sufficiently small backward cylinder around it stays in the
spatial interior and above the initial time, and the function there exceeds
its peak value by at most the prescribed factor. -/
theorem exists_past_weighted_peak
    {β : ℕ} (hβ : 0 < β) {θ ε : ℝ} (hθ₁ : θ < 1)
    (hε : 0 ≤ ε) (hcontrol : 1 ≤ (1 + ε) * (1 - θ) ^ β)
    {u : E → ℝ → ℝ}
    (hu : ContinuousOn (Function.uncurry u) (closedBall 0 1 ×ˢ Icc (-1) 0))
    (hnonneg : ∀ p ∈ closedBall (0 : E) 1 ×ˢ Icc (-1) 0, 0 ≤ u p.1 p.2)
    {x₀ : E} {t₀ : ℝ} (hx₀ : x₀ ∈ ball (0 : E) 1)
    (ht₀ : t₀ ∈ Ioc (-1) 0) (hpos : 0 < u x₀ t₀) :
    ∃ z ∈ ball (0 : E) 1, ∃ q ∈ Ioc (-1) 0, ∃ d : ℝ,
      d = 1 - max ‖z‖ |q| ∧ 0 < d ∧ d ≤ 1 ∧ 0 < u z q ∧
      (∀ p ∈ closedBall (0 : E) 1 ×ˢ Icc (-1) 0,
        u p.1 p.2 * (1 - ‖p‖) ^ β ≤ u z q * d ^ β) ∧
      closedBall z (θ * d) ×ˢ Icc (q - θ * d) q ⊆
        ball (0 : E) 1 ×ˢ Ioc (-1) 0 ∧
      (∀ p ∈ closedBall z (θ * d) ×ˢ Icc (q - θ * d) q,
        u p.1 p.2 ≤ (1 + ε) * u z q) := by
  let F := fun p : E × ℝ ↦ (p.1, -|p.2|)
  have hF : Continuous F := continuous_fst.prodMk continuous_snd.abs.neg
  have hmap : MapsTo F (closedBall (0 : E × ℝ) 1)
      (closedBall (0 : E) 1 ×ˢ Icc (-1) 0) := fun p hp ↦ by
    rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff, Real.norm_eq_abs] at hp
    exact ⟨mem_closedBall_zero_iff.2 hp.1, by dsimp only [F]; linarith [hp.2],
      neg_nonpos.mpr (abs_nonneg p.2)⟩
  have hmapOpen : MapsTo F (ball (0 : E × ℝ) 1) (ball (0 : E) 1 ×ˢ Ioc (-1) 0) := fun p hp ↦ by
    rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff, Real.norm_eq_abs] at hp
    exact ⟨mem_ball_zero_iff.2 hp.1, by dsimp only [F]; linarith [hp.2],
      neg_nonpos.mpr (abs_nonneg p.2)⟩
  let v := fun p : E × ℝ ↦ u p.1 (-|p.2|)
  have hv : ContinuousOn v (closedBall 0 1) := hu.comp hF.continuousOn hmap
  have hvnonneg : ∀ p ∈ closedBall (0 : E × ℝ) 1, 0 ≤ v p :=
    fun p hp ↦ hnonneg (F p) (hmap hp)
  have hp₀ : (x₀, t₀) ∈ ball (0 : E × ℝ) 1 := by
    rw [mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff]
    exact ⟨by simpa only [mem_ball, dist_zero_right] using hx₀,
      by rw [Real.norm_eq_abs, abs_of_nonpos ht₀.2]; linarith only [ht₀.1]⟩
  have hv₀ : 0 < v (x₀, t₀) := by
    simpa only [v, abs_of_nonpos ht₀.2, neg_neg] using hpos
  obtain ⟨p, hp, hvp, hmax, hinside, hupper⟩ :=
    exists_weighted_peak hβ hθ₁ hε hcontrol hv hvnonneg hp₀ hv₀
  let q := -|p.2|
  let d := 1 - ‖p‖
  have hp' : ‖p‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hp
  have hd : 0 < d := sub_pos.mpr hp'
  have hd₁ : d ≤ 1 := by dsimp only [d]; linarith only [norm_nonneg p]
  have hqp : q ≤ 0 := neg_nonpos.mpr (abs_nonneg p.2)
  have hreflect (s : ℝ) (hs : s ≤ q) :
      ∃ t : ℝ, -|t| = s ∧ |t - p.2| = q - s := by
    have hs₀ : s ≤ 0 := hs.trans hqp
    rcases le_total 0 p.2 with hp₀ | hp₀
    · have hq : q = -p.2 := by simp only [q, abs_of_nonneg hp₀]
      exact ⟨-s, by rw [abs_of_nonneg (neg_nonneg.mpr hs₀), neg_neg],
        by rw [abs_of_nonneg (by linarith only [hs, hq]), hq]; ring⟩
    · have hq : q = p.2 := by simp only [q, abs_of_nonpos hp₀, neg_neg]
      exact ⟨s, by rw [abs_of_nonpos hs₀, neg_neg],
        by rw [abs_of_nonpos (by linarith only [hs, hq]), hq]; ring⟩
  have hpreimage (y : E × ℝ)
      (hy : y ∈ closedBall p.1 (θ * d) ×ˢ Icc (q - θ * d) q) :
      ∃ y' ∈ closedBall p (θ * d), F y' = y := by
    obtain ⟨t, ht, hdist⟩ := hreflect y.2 hy.2.2
    refine ⟨(y.1, t), ?_, ?_⟩
    · rw [mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq]
      exact ⟨hy.1, by rw [hdist]; linarith only [hy.2.1]⟩
    · exact Prod.ext rfl ht
  have hrange := hmapOpen hp
  refine ⟨p.1, hrange.1, q, hrange.2, d, ?_, hd, hd₁, hvp, ?_, ?_, ?_⟩
  · simp only [d, q, Prod.norm_def, Real.norm_eq_abs, abs_neg, abs_abs]
  · intro y hy
    have hyball : y ∈ closedBall (0 : E × ℝ) 1 := by
      rw [mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
      exact ⟨by simpa only [mem_closedBall, dist_zero_right] using hy.1,
        by rw [Real.norm_eq_abs, abs_of_nonpos hy.2.2]; linarith only [hy.2.1]⟩
    simpa only [v, q, d, abs_of_nonpos hy.2.2, neg_neg] using hmax y hyball
  · intro y hy
    obtain ⟨y', hy', heq⟩ := hpreimage y hy
    rw [← heq]
    exact hmapOpen (hinside hy')
  · intro y hy
    obtain ⟨y', hy', heq⟩ := hpreimage y hy
    have h := hupper y' hy'
    change u (F y').1 (F y').2 ≤ (1 + ε) * u p.1 q at h
    simpa only [heq] using h

end PDE.Analysis
