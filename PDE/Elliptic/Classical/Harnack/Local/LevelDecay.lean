/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Covering.LevelDecay
public import PDE.Analysis.MeasureTheory.Covering.SublevelComplement
public import PDE.Elliptic.Classical.Harnack.Local.CubeDensity

/-!
# Geometric level decay for elliptic supersolutions

A small value in the unit cube fixes the initial density bound. At any later
level, a dense child cannot have a small value in its parent: the localized
contact estimate would supply the complementary fraction inside that child.
The generic subbox iteration therefore gives geometric decay of superlevels.
-/

@[expose] public section

noncomputable section

namespace EllipticHarnack

open PDE.Analysis EllipticMaximum BoxIntegral BoxIntegral.Prepartition Set Metric MeasureTheory
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- Constants independent of the supersolution give geometric superlevel decay
in the unit cube, from a value at most one anywhere in its closure. -/
theorem exists_superlevel_geometric_decay
    {α τ B : ℝ} (hα : 0 < α) (hB : 0 ≤ B) :
    ∃ M δ : ℝ, 2 ≤ M ∧ 0 < δ ∧ δ < 1 ∧
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
        ∀ x₀ : ℝ^n, WithLp.ofLp x₀ ∈ (centeredUnitBox n).Icc → u x₀ ≤ 1 →
        ∀ k : ℕ,
          (volume.restrict {x : Fin n → ℝ | M ^ k < u (WithLp.toLp 2 x)}).real
              (centeredUnitBox n) ≤
            δ ^ k * volume.real (centeredUnitBox n : Set (Fin n → ℝ)) := by
  obtain ⟨M, η, hM, hη, hηhalf, hdensity⟩ := exists_cube_sublevel_fraction (n := n) hα hB
  let δ := 1 - η
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδ₁ : δ < 1 := by dsimp [δ]; linarith
  refine ⟨M, δ, hM, hδ, hδ₁, ?_⟩
  intro a b ha hell htrace hdrift u hreg hnonneg hsuper x₀ hx₀ hsmall
  let I := centeredUnitBox n
  let v := fun x : Fin n → ℝ ↦ u (WithLp.toLp 2 x)
  let P := fun J : Box (Fin n) ↦
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ i, J.upper i - J.lower i = 2 * r
  have hcont (J : Box (Fin n)) (hJ : J ≤ I) : ContinuousOn v J.Icc := by
    intro x hx
    have hxI := Box.le_iff_Icc.mp hJ hx
    have hnorm := norm_le_of_mem_centeredUnitBox (x := WithLp.toLp 2 x) hxI
    have hinside : WithLp.toLp 2 x ∈ ball (0 : ℝ^n) (16 * ((n : ℝ) + 1)) := by
      rw [mem_ball, dist_zero_right]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    exact ((hreg _ hinside).continuousAt.comp
      (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).continuousAt).continuousWithinAt
  have hsplit : ∀ J ≤ I, P J → ∀ Q ∈ splitCenter J, P Q := by
    rintro J _ ⟨r, hr, hr₁, hside⟩ Q hQ
    refine ⟨r / 2, half_pos hr, by linarith, ?_⟩
    intro i
    rw [upper_sub_lower_of_mem_splitCenter hQ, hside i]
    ring
  have hparent : ∀ t : ℝ, 1 ≤ t → ∀ J ≤ I, P J → ∀ Q ∈ splitCenter J,
      δ * volume.real (Q : Set (Fin n → ℝ)) < (volume.restrict {x | M * t < v x}).real Q →
        (J : Set (Fin n → ℝ)) ⊆ {x | t < v x} := by
    rintro t ht J hJ ⟨r, hr, hr₁, hside⟩ Q hQ hdense x hx
    change t < u (WithLp.toLp 2 x)
    by_contra hnot
    have hQJ : Q ≤ J := (splitCenter J).le_of_mem hQ
    have hQI := hQJ.trans hJ
    have hQside (i : Fin n) : Q.upper i - Q.lower i = 2 * (r / 2) := by
      rw [upper_sub_lower_of_mem_splitCenter hQ, hside i]
      ring
    have hxball : WithLp.toLp 2 x ∈
        closedBall (euclideanBoxCenter Q) ((r / 2) * (4 * ((n : ℝ) + 1))) := by
      rw [mem_closedBall, dist_eq_norm]
      have hgeom := norm_sub_euclideanBoxCenter_le_of_mem_parent hQJ (half_pos hr).le
        (fun i ↦ by rw [hside i]; ring)
        (x := WithLp.toLp 2 x) (Box.coe_subset_Icc hx)
      convert hgeom using 1
      ring
    have hlo := hdensity a b ha hell htrace hdrift u hreg hnonneg hsuper Q hQI
      (r / 2) (half_pos hr) (by linarith) hQside t (zero_lt_one.trans_le ht)
      (WithLp.toLp 2 x) hxball (le_of_not_gt hnot)
    have hhi := measure_restrict_superlevel_le_of_sublevel volume Q (hcont Q hQI) (M * t) η hlo
    exact (not_lt_of_ge hhi) hdense
  have hPI : P I := ⟨1, zero_lt_one, le_rfl, fun _ ↦ by norm_num [I, centeredUnitBox]⟩
  have hxball : x₀ ∈ closedBall (euclideanBoxCenter I) (1 * (4 * ((n : ℝ) + 1))) := by
    rw [euclideanBoxCenter_centeredUnitBox, mem_closedBall, dist_zero_right]
    have hnorm := norm_le_of_mem_centeredUnitBox hx₀
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hlo := hdensity a b ha hell htrace hdrift u hreg hnonneg hsuper I le_rfl 1
    zero_lt_one le_rfl (fun _ ↦ by norm_num [I, centeredUnitBox]) 1 zero_lt_one x₀ hxball hsmall
  simp only [mul_one] at hlo
  have hinitial := measure_restrict_superlevel_le_of_sublevel volume I (hcont I le_rfl) M η hlo
  exact measure_superlevel_pow_le volume I (hcont I le_rfl) (by linarith) hδ.le P hPI hsplit
    hparent hinitial

end EllipticHarnack
