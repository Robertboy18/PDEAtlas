/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Geometry.SpaceTime.WeightedPeak
public import PDE.Parabolic.Harnack.Local.Expansion
public import PDE.Parabolic.Harnack.Local.PeakPropagation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Local Harnack comparison for jointly C² solutions

A weighted maximum in the past cylinder supplies a controlled peak. Contact
and measure growth propagate that peak to a later small ball. Polynomial
expansion reaches the final unit ball; its radius power cancels the weight
at the maximum. Every constant is chosen before the coefficients and solution.

This is the joint C², zero-potential step of the parabolic Harnack argument.
The C²,¹ theorem with a signed potential is `exists_local_comparison_of_space_time_derivatives`.
-/

@[expose] public noncomputable section

namespace ParabolicHarnack

open PDE.Analysis ParabolicMaximum Set Metric
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- A short backward parabolic cylinder fits in the window around the weighted peak. -/
private theorem backward_cylinder_subset_peak_window
    {z : ℝ^n} {q r R : ℝ} (hr : r ≤ R) (ht : r ^ 2 * (1 / 16) ≤ R) :
    closedBall z r ×ˢ Icc (q - r ^ 2 * (1 / 16)) q ⊆
      closedBall z R ×ˢ Icc (q - R) q :=
  prod_mono (closedBall_subset_closedBall hr)
    (Icc_subset_Icc (sub_le_sub_left ht q) le_rfl)

/-- A cylinder of radius and duration at most one, starting in the past unit cylinder,
lies in the region from which the final unit-ball expansion applies. -/
private theorem cylinder_subset_expansion_region
    {z : ℝ^n} {s R T : ℝ} (hz : z ∈ ball (0 : ℝ^n) 1)
    (hs : s ∈ Icc (-1 : ℝ) 0) (hR : R ≤ 1) (hT : T ≤ 1) :
    closedBall z R ×ˢ Icc s (s + T) ⊆
      closedBall (0 : ℝ^n) 2 ×ˢ Icc (-1) 1 :=
  prod_mono (closedBall_subset_closedBall' (by
    have hz₀ : dist z 0 < 1 := hz
    linarith only [hR, hz₀]))
    (Icc_subset_Icc hs.1 (by linarith only [hs.2, hT]))

/-- A uniform comparison between an earlier half-cylinder and a later unit
ball for nonnegative, jointly C² solutions of the zero-potential
equation. The coefficient bounds, rather than the solution, determine the
constant. The statement also applies in zero spatial dimension. -/
theorem exists_local_comparison_of_contDiff_two
    {α τ B : ℝ} (hα : 0 < α) (hτ : 0 ≤ τ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ) (d : ℝ^n → ℝ → ℝ^n),
        let Q := closedBall (0 : ℝ^n) 12 ×ˢ Icc (-1) 64
        (∀ v ∈ Q, (a v.1 v.2).PosSemidef) →
        (∀ v ∈ Q, ∀ w : ℝ^n,
          α * ‖w‖ ^ 2 ≤ ⟪w, (a v.1 v.2).toEuclideanLin w⟫) →
        (∀ v ∈ Q, (a v.1 v.2).trace ≤ τ) →
        (∀ v ∈ Q, ‖d v.1 v.2‖ ≤ B) →
        ∀ u : ℝ^n → ℝ → ℝ,
          (∀ v ∈ Q, ContDiffAt ℝ 2 (Function.uncurry u) v) →
          (∀ v ∈ Q, 0 ≤ u v.1 v.2) →
          (∀ v ∈ Q, matrixParabolicOperator a d (fun _ _ ↦ 0) u v.1 v.2 = 0) →
          ∀ x ∈ closedBall (0 : ℝ^n) (1 / 2), ∀ t ∈ Icc (-1 / 2) 0,
            ∀ y ∈ closedBall (0 : ℝ^n) 1, u x t ≤ C * u y 64 := by
  obtain ⟨p₀, hp₀⟩ := exists_nat_gt
    ((3 + 6 * (τ + 10 * B) + 24 * α) ^ 2 / (4 * (24 * α)))
  let p := p₀ + 1
  have hp : 0 < p := Nat.succ_pos p₀
  have hdecay :
      (3 + 6 * (τ + 10 * B) + 24 * α) ^ 2 / (4 * (24 * α)) ≤ (p : ℝ) + 3 := by
    simp only [p, Nat.cast_add, Nat.cast_one]
    linarith only [hp₀]
  obtain ⟨η, κ, D, C, hη, hκ, hκ₁, hD, hC, hprop⟩ :=
    exists_later_ball_lower_bound_of_peak (n := n) hα hτ hB
  obtain ⟨θ, hθ, hθ₁, hcontrol⟩ := exists_radius_fraction_pow_control (2 * p) hη
  let S := 17 * ((n : ℝ) + 1)
  have hS : 0 < S := by dsimp only [S]; positivity
  let ρ := min 1 (min θ (min (1 / S) (1 / (D + 1))))
  have hρ : 0 < ρ :=
    lt_min zero_lt_one (lt_min hθ (lt_min (one_div_pos.mpr hS)
      (one_div_pos.mpr (by linarith only [hD]))))
  have hρ₁ : ρ ≤ 1 := min_le_left _ _
  have hρθ : ρ ≤ θ := (min_le_right _ _).trans (min_le_left _ _)
  have hρS : ρ * S ≤ 1 :=
    (le_div_iff₀ hS).mp
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hρD : ρ * (D + 1) ≤ 1 :=
    (le_div_iff₀ (by linarith only [hD])).mp
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hD₀ : 0 < D := zero_lt_one.trans hD
  have hρsq : ρ ^ 2 * D ≤ 1 := by
    nlinarith only [mul_le_mul_of_nonneg_right (show ρ ^ 2 ≤ ρ by nlinarith only [hρ, hρ₁]) hD₀.le,
      hρD, hρ]
  let A : ℝ := 8 * 66 ^ p
  have hA : 0 < A := by dsimp only [A]; positivity
  have hden : 0 < ρ ^ (2 * p) * (1 / 2 : ℝ) ^ (2 * p) :=
    mul_pos (pow_pos hρ _) (pow_pos (by norm_num) _)
  refine ⟨C * A / (ρ ^ (2 * p) * (1 / 2 : ℝ) ^ (2 * p)),
    div_pos (mul_pos hC hA) hden, ?_⟩
  intro a d Q ha hell htrace hdrift u hreg hnonneg hsol x₀ hx₀ t₀ ht₀ y hy
  have hsmall : closedBall (0 : ℝ^n) 1 ×ˢ Icc (-1) 0 ⊆ Q :=
    prod_mono (closedBall_subset_closedBall (by norm_num))
      (Icc_subset_Icc le_rfl (by norm_num))
  have hyQ : (y, (64 : ℝ)) ∈ Q :=
    ⟨closedBall_subset_closedBall (by norm_num) hy, by norm_num, le_rfl⟩
  by_cases hpos : 0 < u x₀ t₀
  · have hx₀open : x₀ ∈ ball (0 : ℝ^n) 1 :=
      (show dist x₀ 0 ≤ (1 / 2 : ℝ) from hx₀).trans_lt (by norm_num)
    have ht₀open : t₀ ∈ Ioc (-1 : ℝ) 0 := ⟨by linarith only [ht₀.1], ht₀.2⟩
    obtain ⟨z, hz, q, hq, δ, _, hδ, hδ₁, hpeak, hmax, hinside, hupper⟩ :=
      exists_past_weighted_peak (Nat.mul_pos (by decide) hp) hθ₁ hη.le hcontrol
        (fun v hv ↦ (hreg v (hsmall hv)).continuousAt.continuousWithinAt)
        (fun v hv ↦ hnonneg v (hsmall hv)) hx₀open ht₀open hpos
    let r := ρ * δ
    have hr : 0 < r := mul_pos hρ hδ
    have hrρ : r ≤ ρ := mul_le_of_le_one_right hρ.le hδ₁
    have hr₁ : r ≤ 1 := hrρ.trans hρ₁
    have hrθ : r ≤ θ * δ := mul_le_mul_of_nonneg_right hρθ hδ.le
    have hrS : r * S ≤ 1 := (mul_le_mul_of_nonneg_right hrρ hS.le).trans hρS
    have hrD : r ^ 2 * D ≤ 1 :=
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le hrρ 2) hD₀.le).trans hρsq
    have hκrr : κ * r ≤ r := mul_le_of_le_one_left hr.le hκ₁
    have hκr : 0 < κ * r := mul_pos hκ hr
    have hshort : (κ * r) ^ 2 * (1 / 16) ≤ θ * δ := by
      have hsq : (κ * r) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hκr.le hκrr 2
      have hrsq : r ^ 2 ≤ r := by nlinarith only [hr, hr₁]
      nlinarith only [hsq, hrsq, hrθ, sq_nonneg (κ * r)]
    let s := q - (κ * r) ^ 2 * (1 / 16)
    have htop : s + (κ * r) ^ 2 * (1 / 16) = q := sub_add_cancel _ _
    have hback :
        closedBall z (κ * r) ×ˢ Icc s (s + (κ * r) ^ 2 * (1 / 16)) ⊆
          closedBall z (θ * δ) ×ˢ Icc (q - θ * δ) q := by
      simpa only [htop] using
        backward_cylinder_subset_peak_window (z := z) (q := q) (hκrr.trans hrθ) hshort
    have hzstart : (z, s) ∈ ball (0 : ℝ^n) 1 ×ˢ Ioc (-1) 0 :=
      @hinside (z, s) (@hback (z, s) ⟨mem_closedBall_self hκr.le,
        le_rfl, by dsimp only [s]; nlinarith only [sq_nonneg (κ * r)]⟩)
    have hwindow := cylinder_subset_expansion_region hz ⟨hzstart.2.1.le, hzstart.2.2⟩ hrS hrD
    have hQ : closedBall z (r * S) ×ˢ Icc s (s + r ^ 2 * D) ⊆ Q :=
      hwindow.trans (prod_mono (closedBall_subset_closedBall (by norm_num))
        (Icc_subset_Icc le_rfl (by norm_num)))
    obtain ⟨z', hz', q', hq', hball⟩ := hprop a d z s r hr hr₁
      (fun v hv ↦ ha v (hQ hv)) (fun v hv w ↦ hell v (hQ hv) w)
      (fun v hv ↦ htrace v (hQ hv)) (fun v hv ↦ hdrift v (hQ hv))
      u (fun v hv ↦ hreg v (hQ hv)) (fun v hv ↦ hnonneg v (hQ hv))
      (fun v hv ↦ hsol v (hQ hv))
      (by simpa only [htop] using hpeak)
      (fun v hv ↦ by simpa only [htop] using hupper v (hback hv))
    have hcenter : (z', q') ∈ closedBall (0 : ℝ^n) 2 ×ˢ Icc (-1 : ℝ) 1 := by
      have hrad : ((n : ℝ) + 1) * r ≤ r * S := by
        dsimp only [S]
        nlinarith only [hr, mul_nonneg hr.le (Nat.cast_nonneg (α := ℝ) n)]
      exact hwindow ⟨closedBall_subset_closedBall hrad hz',
        (le_add_of_nonneg_right (sq_nonneg r)).trans hq'.1, hq'.2⟩
    have hball' : ∀ x ∈ closedBall z' r, u z q / C ≤ u x q' := by
      simpa only [htop] using fun x hx ↦ (hball x hx).le
    have hexpand := lower_bound_at_delayed_unit_ball p hα (div_nonneg hpeak.le hC.le)
      hr hr₁ hcenter.1 hcenter.2 hdecay a d ha hell htrace hdrift u
      (fun v hv ↦ (hreg v hv).continuousAt.continuousWithinAt)
      (fun v hv ↦ (hreg v hv).comp v.1 (contDiffAt_id.prodMk contDiffAt_const))
      (fun v hv ↦ ((hreg v hv).comp v.2
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by norm_num))
      (fun v hv ↦ (hsol v hv).ge) hnonneg hball' y hy
    have hnorm : ‖(x₀, t₀)‖ ≤ (1 / 2 : ℝ) := by
      rw [Prod.norm_def, Real.norm_eq_abs]
      exact max_le (by simpa only [mem_closedBall, dist_zero_right] using hx₀)
        (abs_le.2 ⟨by linarith only [ht₀.1], by linarith only [ht₀.2]⟩)
    have hweight : (1 / 2 : ℝ) ≤ 1 - ‖(x₀, t₀)‖ := by linarith only [hnorm]
    have hweighted : u x₀ t₀ * (1 / 2 : ℝ) ^ (2 * p) ≤ u z q * δ ^ (2 * p) :=
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by norm_num) hweight (2 * p)) hpos.le).trans
          (hmax (x₀, t₀) ⟨ball_subset_closedBall hx₀open, ht₀open.1.le, ht₀open.2⟩)
    have hexpand' :
        (u z q * δ ^ (2 * p)) * ρ ^ (2 * p) / (C * A) ≤ u y 64 := by
      convert hexpand using 1
      dsimp only [A, r]
      rw [mul_pow]
      ring
    have h := (mul_le_mul_of_nonneg_right hweighted (pow_nonneg hρ.le _)).trans
      ((div_le_iff₀ (mul_pos hC hA)).mp hexpand')
    rw [div_mul_eq_mul_div, le_div_iff₀ hden]
    linarith only [h]
  · exact (le_of_not_gt hpos).trans (mul_nonneg (div_pos (mul_pos hC hA) hden).le
      (hnonneg (y, 64) hyQ))

end ParabolicHarnack
