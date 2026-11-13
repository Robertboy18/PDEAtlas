/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Second differences from local Hessian bounds

Two applications of Mathlib's mean value inequality bound the first-order remainder
by `M * ‖y - x‖²` when the Hessian has norm at most `M` on a convex set. Adding the
remainders at opposite displacements cancels the linear terms. The resulting
constant `2 * M` is sufficient for semiconcavity; it is not the sharp Taylor constant.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A Hessian bound on a convex set gives a quadratic first-order remainder.
The estimate follows from the mean value inequality for the derivative and then
for the function with its linear part subtracted. -/
theorem norm_sub_sub_fderiv_le_of_hessian_bound
    {f : E → F} {s : Set E} {M : ℝ} (hM : 0 ≤ M) (hs : Convex ℝ s)
    (hf : Differentiable ℝ f) (hdf : Differentiable ℝ (fderiv ℝ f))
    (hbound : ∀ z ∈ s, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ M)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ M * ‖y - x‖ ^ 2 := by
  have hsegment := hs.segment_subset hx hy
  have hderivative (z : E) (hz : z ∈ segment ℝ x y) :
      ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ M * ‖y - x‖ :=
    (hs.norm_image_sub_le_of_norm_fderiv_le
      (fun w _ ↦ hdf w) hbound hx (hsegment hz)).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) hM)
  have h := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le'
    (fun z _ ↦ hf z) hderivative (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [pow_two, mul_assoc] using h

/-- On a convex set, a Hessian norm bound controls the symmetric second difference.
The center and both endpoints must belong to that set. -/
theorem second_difference_le_of_hessian_bound
    {f : E → ℝ} {s : Set E} {M : ℝ} (hM : 0 ≤ M) (hs : Convex ℝ s)
    (hf : Differentiable ℝ f) (hdf : Differentiable ℝ (fderiv ℝ f))
    (hbound : ∀ z ∈ s, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ M)
    {x h : E} (hx : x ∈ s) (hplus : x + h ∈ s) (hminus : x - h ∈ s) :
    f (x + h) - 2 * f x + f (x - h) ≤ 2 * M * ‖h‖ ^ 2 := by
  have hp := norm_sub_sub_fderiv_le_of_hessian_bound hM hs hf hdf hbound hx hplus
  have hm := norm_sub_sub_fderiv_le_of_hessian_bound hM hs hf hdf hbound hx hminus
  have hsub : x - h - x = -h := by abel
  simp only [add_sub_cancel_left, Real.norm_eq_abs] at hp
  simp only [hsub, map_neg, norm_neg, Real.norm_eq_abs, sub_neg_eq_add] at hm
  have hp' := (le_abs_self _).trans hp
  have hm' := (le_abs_self _).trans hm
  linarith

/-- A twice continuously differentiable map has a uniformly bounded Hessian on
each closed ball in a proper real normed space. -/
theorem exists_hessian_bound_closedBall [ProperSpace E]
    {f : E → F} (hf : ContDiff ℝ 2 f) (R : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ Metric.closedBall (0 : E) R, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ M := by
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn
    (hdf.continuous_fderiv (by norm_num)).continuousOn
  exact ⟨max 0 M, le_max_left _ _, fun z hz ↦ (hM z hz).trans (le_max_right _ _)⟩

end PDE.Analysis
