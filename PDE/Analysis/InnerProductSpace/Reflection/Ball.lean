/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.InnerProductSpace.Reflection.Hyperplane

/-!
# Reflection of a ball cap

Reflection of the upper cap towards the centre stays in the ball. A positive
displacement takes the spherical part of the cap strictly inside. Both facts
follow from the exact squared-norm identity and hold in any real inner product space.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact squared norm after reflection across a displaced hyperplane. -/
theorem norm_reflectHyperplane_sq {e : E} (he : ‖e‖ = 1) (a : ℝ) (x : E) :
    ‖reflectHyperplane e a x‖ ^ 2 = ‖x‖ ^ 2 - 4 * a * (⟪x, e⟫ - a) := by
  rw [reflectHyperplane_eq he, norm_add_sq_real, norm_smul, he, mul_one,
    real_inner_smul_right, Real.norm_eq_abs, sq_abs]
  ring

/-- Reflection towards the origin cannot increase the norm in the upper cap. -/
theorem norm_reflectHyperplane_le {e x : E} {a : ℝ} (he : ‖e‖ = 1)
    (ha : 0 ≤ a) (hx : a ≤ ⟪x, e⟫) :
    ‖reflectHyperplane e a x‖ ≤ ‖x‖ := by
  have h := norm_reflectHyperplane_sq he a x
  have hp : 0 ≤ 4 * a * (⟪x, e⟫ - a) := mul_nonneg (by positivity) (sub_nonneg.mpr hx)
  nlinarith [norm_nonneg (reflectHyperplane e a x), norm_nonneg x]

/-- At positive displacement, reflection strictly decreases the norm above the plane. -/
theorem norm_reflectHyperplane_lt {e x : E} {a : ℝ} (he : ‖e‖ = 1)
    (ha : 0 < a) (hx : a < ⟪x, e⟫) :
    ‖reflectHyperplane e a x‖ < ‖x‖ := by
  have h := norm_reflectHyperplane_sq he a x
  have hp : 0 < 4 * a * (⟪x, e⟫ - a) := mul_pos (by positivity) (sub_pos.mpr hx)
  nlinarith [norm_nonneg (reflectHyperplane e a x), norm_nonneg x]

end PDE.Analysis
