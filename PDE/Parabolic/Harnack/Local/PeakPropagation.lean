/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Harnack.Local.MeasureGrowth
public import PDE.Parabolic.Harnack.Local.PeakMeasure
import CAS.ExactTactic

/-!
# Propagation from an almost maximal value to a later ball

The complement estimate supplies earlier superlevel mass near an almost
maximal value. A fixed contraction of the contact cylinder puts this mass
inside a coordinate box with the aspect ratio required by forward measure
iteration. The resulting later ball has the original box radius. All
contractions, time windows, and level losses precede the solution.
-/

@[expose] public noncomputable section

namespace ParabolicHarnack

open PDE.Analysis ParabolicMaximum BoxIntegral Set Metric MeasureTheory
open scoped RealInnerProductSpace ENNReal

variable {n : ℕ}

/-- A positive almost maximum in a short cylinder forces a quantitative
lower bound on a later ball of comparable radius. This intermediate local
estimate uses joint C² regularity and the zero-potential equation. -/
theorem exists_later_ball_lower_bound_of_peak
    {α τ B : ℝ} (hα : 0 < α) (hτ : 0 ≤ τ) (hB : 0 ≤ B) :
    ∃ η κ D C : ℝ, 0 < η ∧ 0 < κ ∧ κ ≤ 1 ∧ 1 < D ∧ 0 < C ∧
      ∀ (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ) (d : ℝ^n → ℝ → ℝ^n)
        (z : ℝ^n) (s r : ℝ), 0 < r → r ≤ 1 →
        let Q := closedBall z (r * (17 * ((n : ℝ) + 1))) ×ˢ Icc s (s + r ^ 2 * D)
        (∀ p ∈ Q, (a p.1 p.2).PosSemidef) →
        (∀ p ∈ Q, ∀ v : ℝ^n, α * ‖v‖ ^ 2 ≤ ⟪v, (a p.1 p.2).toEuclideanLin v⟫) →
        (∀ p ∈ Q, (a p.1 p.2).trace ≤ τ) →
        (∀ p ∈ Q, ‖d p.1 p.2‖ ≤ B) →
        ∀ u : ℝ^n → ℝ → ℝ,
          (∀ p ∈ Q, ContDiffAt ℝ 2 (Function.uncurry u) p) →
          (∀ p ∈ Q, 0 ≤ u p.1 p.2) →
          (∀ p ∈ Q, matrixParabolicOperator a d (fun _ _ ↦ 0) u p.1 p.2 = 0) →
          0 < u z (s + (κ * r) ^ 2 * (1 / 16)) →
          (∀ p ∈ closedBall z (κ * r) ×ˢ Icc s (s + (κ * r) ^ 2 * (1 / 16)),
            u p.1 p.2 ≤ (1 + η) * u z (s + (κ * r) ^ 2 * (1 / 16))) →
          ∃ z' ∈ closedBall z (((n : ℝ) + 1) * r),
            ∃ q ∈ Icc (s + r ^ 2) (s + r ^ 2 * D),
              ∀ x ∈ closedBall z' r,
                u z (s + (κ * r) ^ 2 * (1 / 16)) / C < u x q := by
  obtain ⟨ε, hε, _, hgrowth⟩ :=
    exists_later_ball_lower_bound_of_superlevel_fraction (n := n) hα hτ hB
  obtain ⟨η, D₀, ε₀, hη, hD₀, hε₀, hε₀small, hpeak⟩ :=
    exists_peak_superlevel_measure_bound (n := n) hα hB
  let κ := min 1 ε
  have hκ : 0 < κ := lt_min zero_lt_one hε
  have hκ₁ : κ ≤ 1 := min_le_left _ _
  have hκε : κ ≤ ε := min_le_right _ _
  have htime : ε₀ * κ ^ 2 ≤ ε := by nlinarith only [hκ, hκ₁, hκε, hε₀, hε₀small]
  let V := volume.real
    (closedBall (0 : ℝ^n) (1 / 2) ×ˢ Icc (1 / 64 : ℝ) (1 / 32))
  have hV : 0 < V := by
    apply ENNReal.toReal_pos
    · rw [Measure.volume_eq_prod, Measure.prod_prod]
      exact mul_ne_zero (measure_closedBall_pos volume 0 (by norm_num : (0 : ℝ) < 1 / 2)).ne'
        (by rw [Real.volume_Icc]; exact (ENNReal.ofReal_pos.mpr (by norm_num)).ne')
    · exact ((isCompact_closedBall (0 : ℝ^n) (1 / 2)).prod isCompact_Icc).measure_lt_top.ne
  let β := κ ^ (n + 2) * V / (D₀ * (2 ^ n * ε))
  have hden : 0 < D₀ * (2 ^ n * ε) := mul_pos hD₀ (mul_pos (by positivity) hε)
  have hβ : 0 < β := div_pos (mul_pos (pow_pos hκ _) hV) hden
  obtain ⟨D, C, hD, hC, hprop⟩ := hgrowth β hβ
  refine ⟨η, κ, D, 4 * C, hη, hκ, hκ₁, hD, mul_pos (by norm_num) hC, ?_⟩
  intro a d z s r hr hr₁
  dsimp only
  intro ha hell htrace hdrift u hreg hnonneg hsol hpositive hupper
  let Q := closedBall z (r * (17 * ((n : ℝ) + 1))) ×ˢ Icc s (s + r ^ 2 * D)
  let P := u z (s + (κ * r) ^ 2 * (1 / 16))
  have hκr : 0 < κ * r := mul_pos hκ hr
  have hκrr : κ * r ≤ r := mul_le_of_le_one_left hr.le hκ₁
  have hκr₁ : κ * r ≤ 1 := hκrr.trans hr₁
  have hsquare : (κ * r) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hκr.le hκrr 2
  have hclosed :
      closedBall z (κ * r) ×ˢ Icc s (s + (κ * r) ^ 2 * (1 / 16)) ⊆ Q := by
    intro p hp
    refine ⟨closedBall_subset_closedBall (hκrr.trans ?_) hp.1, hp.2.1,
      hp.2.2.trans (add_le_add le_rfl ?_)⟩
    · nlinarith only [hr, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    · nlinarith only [hsquare, sq_nonneg (κ * r), sq_nonneg r,
        mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hD.le)]
  have hopen :
      ball z (κ * r) ×ˢ Ioc s (s + (κ * r) ^ 2 * (1 / 16)) ⊆ Q :=
    (prod_mono ball_subset_closedBall Ioc_subset_Icc_self).trans hclosed
  have hm := hpeak a d z s (κ * r) hκr hκr₁
    (fun p hp ↦ ha p (hopen hp)) (fun p hp v ↦ hell p (hopen hp) v)
    (fun p hp ↦ htrace p (hopen hp)) (fun p hp ↦ hdrift p (hopen hp))
    u (fun p hp ↦ hreg p (hclosed hp)) (fun p hp ↦ hsol p (hopen hp))
    hpositive hupper
  let j : Fin (n + 1) := 0
  obtain ⟨I, hcenter, hlower, hupperI, hside⟩ :=
    exists_box_space_time_of_center j z s hr (mul_pos hε (sq_pos_of_pos hr))
  have hwidth : I.upper j - I.lower j = ε * r ^ 2 := by
    rw [hupperI, hlower]
    cas
  let S := ((fun p : ℝ^n × ℝ ↦ j.insertNth p.2 (WithLp.ofLp p.1)) ⁻¹'
      (I : Set (Fin (n + 1) → ℝ))) ∩ {p | P / 4 < u p.1 p.2}
  have hsubset :
      ((ball z (κ * r) ×ˢ Ioc s (s + (κ * r) ^ 2 * ε₀)) ∩
        {p | P / 4 < u p.1 p.2}) ⊆ S := by
    intro p hp
    refine ⟨?_, hp.2⟩
    have hbox := ball_prod_Ioc_subset_insertNth_ofLp_box I j hside
    rw [hcenter, hlower, hupperI] at hbox
    refine hbox ⟨ball_subset_ball hκrr hp.1.1, hp.1.2.1, hp.1.2.2.trans (add_le_add le_rfl ?_)⟩
    exact (mul_le_mul_of_nonneg_right htime (sq_nonneg r)).trans_eq' (by ring)
  have hfinite : volume S ≠ ∞ := by
    apply ne_top_of_le_ne_top _ (measure_mono inter_subset_left)
    rw [volume_preimage_insertNth_ofLp]
    exact (I.measure_coe_lt_top volume).ne
  have hmass : (κ * r) ^ (n + 2) * V ≤ D₀ * volume.real S :=
    hm.trans (mul_le_mul_of_nonneg_left (measureReal_mono hsubset hfinite) hD₀.le)
  have hβeq : β * (D₀ * (2 ^ n * ε)) = κ ^ (n + 2) * V :=
    div_mul_cancel₀ _ hden.ne'
  have hscaled : D₀ * (β * ((2 * r) ^ n * (ε * r ^ 2))) = (κ * r) ^ (n + 2) * V := by
    linear_combination r ^ (n + 2) * hβeq
  have hinitial : β * volume.real (I : Set (Fin (n + 1) → ℝ)) ≤
      (volume.restrict {x : Fin (n + 1) → ℝ |
        P / 4 < u (WithLp.toLp 2 (fun i ↦ x (j.succAbove i))) (x j)}).real I := by
    rw [volume_real_box_space_time_of_side I j hside hwidth,
      volume_real_restrict_box_insertNth]
    exact (mul_le_mul_iff_right₀ hD₀).mp (hscaled.le.trans hmass)
  subst hcenter hlower
  simpa only [div_div, P] using hprop I j r hr hr₁ hside hwidth a d ha hell htrace hdrift u
    (P / 4) (div_pos hpositive (by norm_num)) hreg hnonneg (fun p hp ↦ (hsol p hp).ge) hinitial

end ParabolicHarnack
