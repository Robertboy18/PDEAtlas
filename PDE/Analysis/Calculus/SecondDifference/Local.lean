/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalExtension
public import PDE.Analysis.Calculus.SecondDifference

/-!
# Local quadratic remainders

A twice continuously differentiable germ in a finite-dimensional space has a
quadratic first-order remainder. A compactly supported representative reduces the
local statement to the existing Hessian estimate on a closed ball.
-/

@[expose] public section

open Filter Metric Set
open scoped Topology

/-- A `C²` germ has a quadratic first-order remainder on a neighborhood.
The constant is constructed from the germ; no derivative bound is assumed. -/
theorem ContDiffAt.exists_norm_sub_sub_fderiv_le_mul_sq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 x,
      ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ C * ‖y - x‖ ^ 2 := by
  obtain ⟨g, hg, _hcompact, heq⟩ :=
    hf.exists_contDiff_compactSupport_eventuallyEq
  have hzero : f x = g x := heq.self_of_nhds
  have hderiv : fderiv ℝ f x = fderiv ℝ g x := heq.fderiv.self_of_nhds
  obtain ⟨C, hC, hbound⟩ :=
    PDE.Analysis.exists_hessian_bound_closedBall hg (‖x‖ + 1)
  have hx : x ∈ closedBall (0 : E) (‖x‖ + 1) := by
    simp only [mem_closedBall, dist_zero_right]
    linarith
  have hxball : x ∈ ball (0 : E) (‖x‖ + 1) := by
    simp only [mem_ball, dist_zero_right]
    linarith
  have hdf : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  refine ⟨C, hC, ?_⟩
  filter_upwards [heq, isOpen_ball.mem_nhds hxball] with y hy hyball
  have hb := PDE.Analysis.norm_sub_sub_fderiv_le_of_hessian_bound hC
    (convex_closedBall (0 : E) (‖x‖ + 1))
    (hg.differentiable (by norm_num)) (hdf.differentiable one_ne_zero)
    hbound hx (ball_subset_closedBall hyball)
  simpa only [hy, hzero, hderiv] using hb
