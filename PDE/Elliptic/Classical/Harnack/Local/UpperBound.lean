/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Geometry.WeightedPeak
public import PDE.Analysis.MeasureTheory.Covering.WeightedLevelBound
public import PDE.Elliptic.Classical.Harnack.Local.LevelDecay
public import PDE.Elliptic.Classical.Harnack.Local.PeakMeasure

/-!
# A uniform local upper bound for nonnegative solutions

Geometric decay controls how much of the unit cube can lie above each level.
A weighted maximum, on the other hand, supplies a ball of high values: apply
the contact estimate to the complement of the solution near that maximum.
Comparing the two measures bounds the weighted height and hence the solution
on the half ball. Every constant is chosen before the solution.
-/

@[expose] public section

noncomputable section

namespace EllipticHarnack

open PDE.Analysis EllipticMaximum BoxIntegral Set Metric MeasureTheory
open scoped RealInnerProductSpace ENNReal

variable {n : ℕ}

/-- A nonnegative solution with one value at most one in the unit cube has
a uniformly bounded value everywhere in the half unit ball. -/
theorem exists_local_upper_bound
    (hn : 0 < n) {α τ B : ℝ} (hα : 0 < α) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n),
        (∀ x ∈ ball (0 : ℝ^n) (16 * ((n : ℝ) + 1)), (a x).PosSemidef) →
        (∀ x ∈ ball (0 : ℝ^n) (16 * ((n : ℝ) + 1)), ∀ v : ℝ^n,
          α * ‖v‖ ^ 2 ≤ ⟪v, (a x).toEuclideanLin v⟫) →
        (∀ x ∈ ball (0 : ℝ^n) (16 * ((n : ℝ) + 1)), (a x).trace ≤ τ) →
        (∀ x ∈ ball (0 : ℝ^n) (16 * ((n : ℝ) + 1)), ‖b x‖ ≤ B) →
        ∀ u : ℝ^n → ℝ,
        (∀ x ∈ ball (0 : ℝ^n) (16 * ((n : ℝ) + 1)), ContDiffAt ℝ 2 u x) →
        (∀ x ∈ ball (0 : ℝ^n) (16 * ((n : ℝ) + 1)), 0 ≤ u x) →
        (∀ x ∈ ball (0 : ℝ^n) (16 * ((n : ℝ) + 1)),
          matrixOperator a b (fun _ ↦ 0) u x = 0) →
        ∀ x₀ : ℝ^n, WithLp.ofLp x₀ ∈ (centeredUnitBox n).Icc → u x₀ ≤ 1 →
        ∀ x ∈ closedBall (0 : ℝ^n) (1 / 2), u x ≤ C := by
  obtain ⟨M, δ, hM, hδ, hδ₁, hdecay⟩ := exists_superlevel_geometric_decay (n := n) hα hB
  have hM₁ : 1 < M := by linarith
  obtain ⟨β, hβ, hβdecay⟩ := exists_nat_weight_exponent hM₁ hδ.le hδ₁ n
  obtain ⟨ε, D, hε, hD, hpeak⟩ := exists_peak_superlevel_measure_bound (n := n) hα hB
  obtain ⟨θ, hθ, hθ₁, hcontrol⟩ := exists_radius_fraction_pow_control β hε
  let A := volume.real (closedBall (0 : ℝ^n) (1 / 2))
  have hA : 0 < A :=
    ENNReal.toReal_pos (measure_closedBall_pos volume 0 (by norm_num)).ne'
      measure_closedBall_lt_top.ne
  let c := θ ^ n * A / (D * 2 ^ n)
  obtain ⟨C, hC, hheight⟩ :=
    exists_weighted_height_bound hM₁ hδ.le hn hβdecay (show 0 < c by positivity)
  refine ⟨C * 2 ^ β, by positivity, ?_⟩
  intro a b ha hell htrace hdrift u hreg hnonneg hsol x₀ hx₀ hsmall x hx
  have hunit : closedBall (0 : ℝ^n) 1 ⊆ ball (0 : ℝ^n) (16 * ((n : ℝ) + 1)) :=
    closedBall_subset_ball (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  have hlevels := hdecay a b ha hell htrace hdrift u hreg hnonneg
    (fun y hy ↦ (hsol y hy).ge) x₀ hx₀ hsmall
  by_cases hux : 0 < u x
  · have hxunit : x ∈ ball (0 : ℝ^n) 1 := closedBall_subset_ball (by norm_num) hx
    obtain ⟨z, hz, huz, hmax, hinside, hupper⟩ := exists_weighted_peak hβ hθ₁ hε.le hcontrol
      (fun y hy ↦ (hreg y (hunit hy)).continuousAt.continuousWithinAt)
      (fun y hy ↦ hnonneg y (hunit hy)) hxunit hux
    let d := 1 - ‖z‖
    have hd : 0 < d := sub_pos.mpr (by simpa using hz)
    have hd₁ : d ≤ 1 := sub_le_self _ (norm_nonneg z)
    let r := θ * d
    have hclosed : closedBall z r ⊆ ball (0 : ℝ^n) (16 * ((n : ℝ) + 1)) :=
      fun y hy ↦ hunit (ball_subset_closedBall (hinside hy))
    have hball : ball z r ⊆ ball (0 : ℝ^n) (16 * ((n : ℝ) + 1)) :=
      fun y hy ↦ hclosed (ball_subset_closedBall hy)
    have hmass := hpeak a b z r (mul_pos hθ hd)
      ((mul_le_of_le_one_right hθ.le hd₁).trans hθ₁.le)
      (fun y hy ↦ ha y (hball hy)) (fun y hy ↦ hell y (hball hy))
      (fun y hy ↦ htrace y (hball hy)) (fun y hy ↦ hdrift y (hball hy))
      u (fun y hy ↦ (hreg y (hclosed hy)).continuousAt.continuousWithinAt)
      (fun y hy ↦ hreg y (hball hy)) (fun y hy ↦ hsol y (hball hy)) huz hupper
    have hballcube : ball (0 : ℝ^n) 1 ⊆
        WithLp.ofLp ⁻¹' (centeredUnitBox n : Set (Fin n → ℝ)) := by
      simpa only [euclideanBoxCenter_centeredUnitBox] using
        ball_euclideanBoxCenter_subset (centeredUnitBox n) (r := 1)
          (fun _ ↦ by norm_num [centeredUnitBox])
    have hradius (k : ℕ) (hk : 4 * M ^ k ≤ u z) : c * d ^ n ≤ δ ^ k := by
      let S := (centeredUnitBox n : Set (Fin n → ℝ)) ∩ {y | M ^ k < u (WithLp.toLp 2 y)}
      have hsubset : ball z r ∩ {y | u z / 4 < u y} ⊆ WithLp.ofLp ⁻¹' S := fun y hy ↦
        ⟨hballcube (hinside (ball_subset_closedBall hy.1)),
          (show M ^ k ≤ u z / 4 by linarith).trans_lt hy.2⟩
      have hfinite : volume (WithLp.ofLp ⁻¹' S : Set (ℝ^n)) ≠ ∞ := by
        rw [volume_preimage_ofLp]
        exact (measure_mono inter_subset_left |>.trans_lt
          ((centeredUnitBox n).measure_coe_lt_top volume)).ne
      have hmeasure : volume.real (ball z r ∩ {y | u z / 4 < u y}) ≤ δ ^ k * 2 ^ n := by
        calc
          _ ≤ volume.real (WithLp.ofLp ⁻¹' S : Set (ℝ^n)) := measureReal_mono hsubset hfinite
          _ = (volume.restrict {y | M ^ k < u (WithLp.toLp 2 y)}).real (centeredUnitBox n) := by
            rw [volume_real_preimage_ofLp,
              measureReal_restrict_apply (centeredUnitBox n).measurableSet_coe]
          _ ≤ δ ^ k * volume.real (centeredUnitBox n : Set (Fin n → ℝ)) := hlevels k
          _ = δ ^ k * 2 ^ n := by
            rw [volume_real_box_of_side (r := 1) _ (fun _ ↦ by norm_num [centeredUnitBox]),
              mul_one]
      have hmass' := hmass.trans (mul_le_mul_of_nonneg_left hmeasure hD.le)
      simp only [r, mul_pow] at hmass'
      dsimp only [c]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      linarith
    have hxweight : (1 / 2 : ℝ) ^ β ≤ (1 - ‖x‖) ^ β :=
      pow_le_pow_left₀ (by norm_num) (by linarith [mem_closedBall_zero_iff.1 hx]) β
    have hxbound := ((mul_le_mul_of_nonneg_left hxweight hux.le).trans
      (hmax x (ball_subset_closedBall hxunit))).trans (hheight (u z) d huz hd hd₁ hradius)
    rwa [div_pow, one_pow, mul_one_div, div_le_iff₀ (by positivity)] at hxbound
  · exact (le_of_not_gt hux).trans (by positivity)

end EllipticHarnack
