/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# Tangent balls in a ball cap

At a point of the flat face strictly inside a ball, a sufficiently small ball
in the inward normal direction lies in the cap. This elementary construction
identifies the tangent ball's outward normal as the opposite unit direction.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Metric Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The intersection of a ball with an open affine half-space is convex. -/
theorem convex_ball_inter_inner_gt (e : E) (a r : ℝ) :
    Convex ℝ (ball (0 : E) r ∩ {x | a < ⟪x, e⟫}) :=
  (convex_ball _ _).inter (convex_halfSpace_gt
    (show IsLinearMap ℝ (fun x : E ↦ ⟪x, e⟫) from
      ⟨fun x y ↦ inner_add_left x y e, fun c x ↦ real_inner_smul_left x e c⟩) a)

/-- A flat-face point strictly inside the unit ball admits a tangent ball contained in
the upper cap; its outward unit normal at the contact point is `-e`. -/
theorem exists_ball_subset_unitBall_cap {x e : E} {a : ℝ}
    (hx : ‖x‖ < 1) (he : ‖e‖ = 1) (hplane : ⟪x, e⟫ = a) :
    ∃ R : ℝ, 0 < R ∧
      ball (x + R • e) R ⊆ ball (0 : E) 1 ∩ {y | a < ⟪y, e⟫} ∧
      ‖x - (x + R • e)‖ = R ∧ R⁻¹ • (x - (x + R • e)) = -e := by
  let R := (1 - ‖x‖) / 4
  have hR : 0 < R := by dsimp [R]; linarith
  refine ⟨R, hR, ?_, ?_, ?_⟩
  · intro y hy
    have hyd : ‖y - (x + R • e)‖ < R := by simpa [dist_eq_norm] using hy
    have hRe : ‖R • e‖ = R := by simp [norm_smul, he, abs_of_pos hR]
    have hz : ‖x + R • e‖ ≤ ‖x‖ + R := by
      simpa only [hRe] using norm_add_le x (R • e)
    have hyn : ‖y‖ < 1 := by
      have hn := norm_add_le (y - (x + R • e)) (x + R • e)
      rw [sub_add_cancel] at hn
      dsimp [R] at *
      linarith
    refine ⟨by simpa using hyn, ?_⟩
    change a < ⟪y, e⟫
    have hi := real_inner_le_norm (x + R • e - y) e
    rw [he, mul_one, norm_sub_rev] at hi
    have hee : ⟪e, e⟫ = 1 := by simp [he]
    rw [inner_sub_left, inner_add_left, real_inner_smul_left, hee, mul_one, hplane] at hi
    linarith
  · simp [norm_smul, he, abs_of_pos hR]
  · simp [smul_smul, ne_of_gt hR]

end PDE.Analysis
