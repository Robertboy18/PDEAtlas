/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Geometry.EuclideanBox
public import PDE.Elliptic.Classical.Harnack.Local.ScaledGrowth

/-!
# A uniform low-level fraction in subcubes

The scaled contact estimate is localized to the inscribed ball of a cube.
Its volume lower bound and the cube volume have the same factor `rⁿ`;
cancelling it gives a fraction independent of the cube. Enlarged contact
balls of every subcube remain inside the fixed ambient ball.
-/

@[expose] public section

noncomputable section

namespace EllipticHarnack

open PDE.Analysis EllipticMaximum BoxIntegral Set Metric MeasureTheory
open scoped RealInnerProductSpace ENNReal

variable {n : ℕ}

/-- Every subcube has a uniform low-level fraction whenever the solution has
a small value in the concentric ball containing its dyadic parent. -/
theorem exists_cube_sublevel_fraction
    {α τ B : ℝ} (hα : 0 < α) (hB : 0 ≤ B) :
    ∃ M η : ℝ, 2 ≤ M ∧ 0 < η ∧ η ≤ 1 / 2 ∧
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
          0 ≤ matrixOperator a b (fun _ ↦ 0) u x) →
        ∀ I : Box (Fin n), I ≤ centeredUnitBox n →
        ∀ r : ℝ, 0 < r → r ≤ 1 → (∀ i, I.upper i - I.lower i = 2 * r) →
        ∀ t : ℝ, 0 < t →
        ∀ x₀ ∈ closedBall (euclideanBoxCenter I) (r * (4 * ((n : ℝ) + 1))),
          u x₀ ≤ t →
          η * volume.real (I : Set (Fin n → ℝ)) ≤
            (volume.restrict {x : Fin n → ℝ | u (WithLp.toLp 2 x) ≤ M * t}).real I := by
  let R := 8 * ((n : ℝ) + 1)
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨M, D, hM, hD, hbound⟩ :=
    exists_scaled_sublevel_measure_bound (n := n) hR zero_lt_one hα hB
  let A := volume.real (closedBall (0 : ℝ^n) (R / 2))
  have hA : 0 < A := ENNReal.toReal_pos
    (measure_closedBall_pos volume 0 (half_pos hR)).ne' measure_closedBall_lt_top.ne
  let η := min (1 / 2) (A / (D * 2 ^ n))
  have hη : 0 < η := lt_min (by norm_num) (div_pos hA (mul_pos hD (by positivity)))
  refine ⟨M, η, hM, hη, min_le_left _ _, ?_⟩
  intro a b ha hell htrace hdrift u hreg hnonneg hsuper I hI r hr hr₁ hside t ht x₀ hx₀ hsmall
  let z := euclideanBoxCenter I
  have hinside : closedBall z (r * R) ⊆ ball (0 : ℝ^n) (16 * ((n : ℝ) + 1)) :=
    closedBall_subbox_subset_ball hI hr₁
  have hinsideOpen := ball_subset_closedBall.trans hinside
  have hx₀' : x₀ ∈ closedBall z (r * (R / 2)) := by
    rw [show R / 2 = 4 * ((n : ℝ) + 1) by dsimp [R]; ring]
    exact hx₀
  have h := hbound a b z r hr hr₁
    (fun x hx ↦ ha x (hinsideOpen hx)) (fun x hx ↦ hell x (hinsideOpen hx))
    (fun x hx ↦ htrace x (hinsideOpen hx)) (fun x hx ↦ hdrift x (hinsideOpen hx))
    u (fun x hx ↦ (hreg x (hinside hx)).continuousAt.continuousWithinAt)
    (fun x hx ↦ hreg x (hinsideOpen hx)) (fun x hx ↦ hnonneg x (hinside hx))
    (fun x hx ↦ hsuper x (hinsideOpen hx)) t ht x₀ hx₀' hsmall
  simp only [mul_one] at h
  let S := (I : Set (Fin n → ℝ)) ∩ {x | u (WithLp.toLp 2 x) ≤ M * t}
  have hsubset : ball z r ∩ {x | u x ≤ M * t} ⊆
      WithLp.ofLp ⁻¹' S := by
    intro x hx
    exact ⟨ball_euclideanBoxCenter_subset I hside hx.1, by simpa using hx.2⟩
  have hvolume : volume.real (ball z r ∩ {x | u x ≤ M * t}) ≤ volume.real S := by
    rw [← volume_real_preimage_ofLp S]
    refine measureReal_mono hsubset ?_
    rw [volume_preimage_ofLp]
    exact (measure_mono inter_subset_left |>.trans_lt (I.measure_coe_lt_top volume)).ne
  have hmass : r ^ n * A ≤ D * volume.real S :=
    h.trans (mul_le_mul_of_nonneg_left hvolume hD.le)
  have hηbound : η * (D * 2 ^ n) ≤ A :=
    (le_div_iff₀ (mul_pos hD (by positivity))).mp (min_le_right _ _)
  have hscaled : D * (η * (2 * r) ^ n) ≤ r ^ n * A := by
    calc
      D * (η * (2 * r) ^ n) = r ^ n * (η * (D * 2 ^ n)) := by rw [mul_pow]; ring
      _ ≤ r ^ n * A := mul_le_mul_of_nonneg_left hηbound (pow_nonneg hr.le n)
  rw [volume_real_box_of_side I hside, measureReal_restrict_apply I.measurableSet_coe]
  exact (mul_le_mul_iff_right₀ hD).mp (hscaled.trans hmass)

end EllipticHarnack
