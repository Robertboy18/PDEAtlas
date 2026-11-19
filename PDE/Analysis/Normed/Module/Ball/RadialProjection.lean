/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Radial projection onto a ball

The continuous map `x ↦ (R / max R ‖x‖) • x` retracts a real normed space onto the closed
ball of positive radius `R`. Outside the ball it has norm exactly `R`. The norm need not
come from an inner product, and the space may be infinite-dimensional.
-/

@[expose] public noncomputable section

open Metric

namespace PDE.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial projection onto the closed ball centered at zero. -/
def radialProjection (R : ℝ) (x : E) : E :=
  (R / max R ‖x‖) • x

/-- Radial projection onto a ball of positive radius is continuous everywhere. -/
theorem continuous_radialProjection {R : ℝ} (hR : 0 < R) :
    Continuous (radialProjection R : E → E) :=
  ((continuous_const (y := R)).div (continuous_const.max continuous_norm)
    (fun x ↦ (hR.trans_le (le_max_left R ‖x‖)).ne')).smul continuous_id

/-- The projection fixes every point of the ball, including its boundary. -/
theorem radialProjection_eq_self {R : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ ≤ R) :
    radialProjection R x = x := by
  simp [radialProjection, max_eq_left hx, div_self hR.ne']

/-- Outside the ball, radial projection is the usual normalization to radius `R`. -/
theorem radialProjection_eq_smul_of_le {R : ℝ} {x : E} (hx : R ≤ ‖x‖) :
    radialProjection R x = (R / ‖x‖) • x := by
  simp only [radialProjection, max_eq_right hx]

/-- A point outside or on the ball is projected to its sphere. -/
theorem norm_radialProjection_of_le {R : ℝ} (hR : 0 < R) {x : E} (hx : R ≤ ‖x‖) :
    ‖radialProjection R x‖ = R := by
  have hn : 0 < ‖x‖ := hR.trans_le hx
  rw [radialProjection_eq_smul_of_le hx, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos hR hn), div_mul_cancel₀ _ hn.ne']

/-- Every value of the projection lies in the closed ball. -/
theorem radialProjection_mem_closedBall {R : ℝ} (hR : 0 < R) (x : E) :
    radialProjection R x ∈ closedBall (0 : E) R := by
  rw [mem_closedBall, dist_zero_right]
  by_cases hx : ‖x‖ ≤ R
  · simpa only [radialProjection_eq_self hR hx] using hx
  · exact (norm_radialProjection_of_le hR (le_of_not_ge hx)).le

/-- Radial projection is globally 2-Lipschitz in any real normed space. The constant
does not depend on the positive radius. -/
theorem lipschitzWith_radialProjection {R : ℝ} (hR : 0 < R) :
    LipschitzWith 2 (radialProjection R : E → E) := by
  have hbound (x y : E) (hxy : max R ‖x‖ ≤ max R ‖y‖) :
      ‖radialProjection R x - radialProjection R y‖ ≤ 2 * ‖x - y‖ := by
    let A := max R ‖x‖
    let B := max R ‖y‖
    have hA : 0 < A := hR.trans_le (le_max_left _ _)
    have hB : 0 < B := hR.trans_le (le_max_left _ _)
    have hq : 0 ≤ R / B := div_nonneg hR.le hB.le
    have hq1 : R / B ≤ 1 := (div_le_one hB).2 (le_max_left _ _)
    have hd : 0 ≤ R / A - R / B :=
      sub_nonneg.2 (div_le_div_of_nonneg_left hR.le hA hxy)
    have hdiff : B - A ≤ ‖x - y‖ := by
      apply sub_le_iff_le_add.mpr
      apply max_le
      · exact (le_max_left R ‖x‖).trans (le_add_of_nonneg_left (norm_nonneg _))
      · have hn := norm_sub_norm_le y x
        rw [norm_sub_rev] at hn
        have hx := le_max_right R ‖x‖
        dsimp [A]
        linarith
    have heq : radialProjection R x - radialProjection R y =
        (R / B) • (x - y) + (R / A - R / B) • x := by
      simp only [radialProjection, A, B, smul_sub, sub_smul]
      abel
    calc
      ‖radialProjection R x - radialProjection R y‖
        ≤ (R / B) * ‖x - y‖ + (R / A - R / B) * ‖x‖ := by
          rw [heq]
          simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hq,
            abs_of_nonneg hd] using norm_add_le ((R / B) • (x - y))
              ((R / A - R / B) • x)
      _ ≤ (R / B) * ‖x - y‖ + (R / A - R / B) * A := by
        gcongr
        exact le_max_right _ _
      _ = (R / B) * ‖x - y‖ + (R / B) * (B - A) := by
        rw [sub_mul, div_mul_cancel₀ _ hA.ne', mul_sub, div_mul_cancel₀ _ hB.ne']
      _ ≤ 1 * ‖x - y‖ + 1 * ‖x - y‖ := by
        gcongr
      _ = 2 * ‖x - y‖ := by ring
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rcases le_total (max R ‖x‖) (max R ‖y‖) with hxy | hyx
  · simpa only [NNReal.coe_ofNat, dist_eq_norm] using hbound x y hxy
  · simpa only [NNReal.coe_ofNat, dist_eq_norm, norm_sub_rev] using hbound y x hyx

end PDE.Analysis
