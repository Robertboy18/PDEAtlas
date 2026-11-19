/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean
public import Mathlib.Analysis.BoxIntegral.Partition.Measure
public import Mathlib.Analysis.BoxIntegral.Partition.SubboxInduction
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Euclidean geometry of Mathlib boxes

Mathlib's boxes are products of coordinate intervals. Here their centers and
inscribed balls are measured in the Euclidean norm. A cube is a box with equal
side lengths, stated as an equation on the box.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open BoxIntegral Set Metric MeasureTheory

variable {n : ℕ}

/-- A coarse dimension-dependent Euclidean norm bound from coordinate bounds. -/
theorem norm_le_dim_add_one_mul_of_coord_le
    {v : ℝ^n} {r : ℝ} (hr : 0 ≤ r) (hv : ∀ i, ‖v i‖ ≤ r) :
    ‖v‖ ≤ ((n : ℝ) + 1) * r := by
  have hs : ‖v‖ ^ 2 ≤ (n : ℝ) * r ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      ∑ i : Fin n, ‖v i‖ ^ 2 ≤ ∑ _ : Fin n, r ^ 2 :=
        Finset.sum_le_sum (fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hv i) 2)
      _ = (n : ℝ) * r ^ 2 := by simp
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnr : 0 ≤ ((n : ℝ) + 1) * r := mul_nonneg (by positivity) hr
  nlinarith [sq_nonneg ((n : ℝ) * r), sq_nonneg r]

/-- The coordinate midpoint of a box, regarded as a Euclidean vector. -/
def euclideanBoxCenter (I : Box (Fin n)) : ℝ^n :=
  WithLp.toLp 2 (fun i ↦ (I.lower i + I.upper i) / 2)

/-- The coordinate midpoint lies in the closed box. -/
theorem euclideanBoxCenter_mem_Icc (I : Box (Fin n)) :
    WithLp.ofLp (euclideanBoxCenter I) ∈ I.Icc := by
  constructor <;> intro i <;>
    dsimp [euclideanBoxCenter] <;> linarith [I.lower_lt_upper i]

/-- The ball of radius half the side length lies in the half-open cube. -/
theorem ball_euclideanBoxCenter_subset
    (I : Box (Fin n)) {r : ℝ} (hside : ∀ i, I.upper i - I.lower i = 2 * r) :
    ball (euclideanBoxCenter I) r ⊆ WithLp.ofLp ⁻¹' (I : Set (Fin n → ℝ)) := by
  intro x hx i
  have hnorm : ‖x - euclideanBoxCenter I‖ < r := by simpa [dist_eq_norm] using hx
  have hcoord := (PiLp.norm_apply_le (x - euclideanBoxCenter I) i).trans_lt hnorm
  change |x i - (I.lower i + I.upper i) / 2| < r at hcoord
  have hc := abs_lt.mp hcoord
  have hs := hside i
  constructor <;> linarith

/-- A cube lies in a concentric ball with a coarse dimension-dependent radius. -/
theorem norm_sub_euclideanBoxCenter_le
    (I : Box (Fin n)) {r : ℝ} (hr : 0 ≤ r)
    (hside : ∀ i, I.upper i - I.lower i = 2 * r)
    {x : ℝ^n} (hx : WithLp.ofLp x ∈ I.Icc) :
    ‖x - euclideanBoxCenter I‖ ≤ ((n : ℝ) + 1) * r := by
  apply norm_le_dim_add_one_mul_of_coord_le hr
  intro i
  change |x i - (I.lower i + I.upper i) / 2| ≤ r
  have hs := hside i
  have hxl := hx.1 i
  have hxu := hx.2 i
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Any point in a parent cube is within four child radii per coordinate of
the center of a child contained in it. -/
theorem norm_sub_euclideanBoxCenter_le_of_mem_parent
    {I J : Box (Fin n)} (hJI : J ≤ I) {r : ℝ} (hr : 0 ≤ r)
    (hside : ∀ i, I.upper i - I.lower i = 4 * r)
    {x : ℝ^n} (hx : WithLp.ofLp x ∈ I.Icc) :
    ‖x - euclideanBoxCenter J‖ ≤ ((n : ℝ) + 1) * (4 * r) := by
  apply norm_le_dim_add_one_mul_of_coord_le (by positivity)
  intro i
  have hc := (Box.le_iff_Icc.mp hJI) (euclideanBoxCenter_mem_Icc J)
  have hcl := hc.1 i
  have hcu := hc.2 i
  have hxl := hx.1 i
  have hxu := hx.2 i
  have hs := hside i
  change |x i - euclideanBoxCenter J i| ≤ 4 * r
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Lebesgue volume of an equal-sided box. -/
theorem volume_real_box_of_side
    (I : Box (Fin n)) {r : ℝ} (hside : ∀ i, I.upper i - I.lower i = 2 * r) :
    volume.real (I : Set (Fin n → ℝ)) = (2 * r) ^ n := by
  rw [measureReal_def, I.coe_eq_pi, Real.volume_pi_Ioc_toReal I.lower_le_upper]
  simp only [hside, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Passing from coordinate functions to Euclidean space preserves volume,
including the outer measure of sets that have not been shown measurable. -/
theorem volume_preimage_ofLp (S : Set (Fin n → ℝ)) :
    volume (WithLp.ofLp ⁻¹' S : Set (ℝ^n)) = volume S := by
  calc
    volume (WithLp.ofLp ⁻¹' S : Set (ℝ^n)) =
        (volume.map (@WithLp.ofLp 2 (Fin n → ℝ))) S :=
      ((MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.map_apply S).symm
    _ = volume S := by rw [(PiLp.volume_preserving_ofLp (Fin n)).map_eq]

/-- Passing from coordinate functions to Euclidean space preserves real-valued volume. -/
theorem volume_real_preimage_ofLp (S : Set (Fin n → ℝ)) :
    volume.real (WithLp.ofLp ⁻¹' S : Set (ℝ^n)) = volume.real S := by
  simp only [measureReal_def, volume_preimage_ofLp]

/-- The coordinate cube with lower corner `-1` and upper corner `1`. -/
def centeredUnitBox (n : ℕ) : Box (Fin n) where
  lower _ := -1
  upper _ := 1
  lower_lt_upper _ := by norm_num

/-- The cube with opposite corners `-1` and `1` has Euclidean center zero. -/
theorem euclideanBoxCenter_centeredUnitBox :
    euclideanBoxCenter (centeredUnitBox n) = 0 := by
  ext i
  simp [euclideanBoxCenter, centeredUnitBox]

/-- Points in the closed centered unit cube satisfy the coarse norm bound `n + 1`. -/
theorem norm_le_of_mem_centeredUnitBox {x : ℝ^n}
    (hx : WithLp.ofLp x ∈ (centeredUnitBox n).Icc) :
    ‖x‖ ≤ (n : ℝ) + 1 := by
  have h := norm_sub_euclideanBoxCenter_le (centeredUnitBox n) zero_le_one
    (fun _ ↦ by norm_num [centeredUnitBox]) hx
  simpa only [euclideanBoxCenter_centeredUnitBox, sub_zero, mul_one] using h

/-- The enlarged balls used for subcube contact estimates stay strictly
inside one fixed ambient ball. -/
theorem closedBall_subbox_subset_ball
    {I : Box (Fin n)} (hI : I ≤ centeredUnitBox n)
    {r : ℝ} (hr : r ≤ 1) :
    closedBall (euclideanBoxCenter I) (r * (8 * ((n : ℝ) + 1))) ⊆
      ball (0 : ℝ^n) (16 * ((n : ℝ) + 1)) := by
  intro x hx
  have hc := norm_le_of_mem_centeredUnitBox
    ((Box.le_iff_Icc.mp hI) (euclideanBoxCenter_mem_Icc I))
  have hd : dist x (euclideanBoxCenter I) ≤ r * (8 * ((n : ℝ) + 1)) := hx
  have hs : ‖x‖ ≤ dist x (euclideanBoxCenter I) + ‖euclideanBoxCenter I‖ := by
    simpa only [dist_zero_right] using dist_triangle x (euclideanBoxCenter I) 0
  have hr' := mul_le_mul_of_nonneg_right hr (show 0 ≤ 8 * ((n : ℝ) + 1) by positivity)
  rw [mem_ball, dist_zero_right]
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

end PDE.Analysis
