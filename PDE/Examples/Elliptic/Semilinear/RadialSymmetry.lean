/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.MovingPlanes.Ball
import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Closure
import PDE.FDeriv.Calculus
import PDE.FDeriv.Euclidean.Laplacian
import CAS.ExactTactic
import Mathlib.Analysis.Calculus.Deriv.Abs
import PDE.Symbolic.PDEDerivatives

import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Radial symmetry of positive semilinear solutions

The moving-plane theorem `exists_strictAntiOn_radial_profile_of_lipschitz` says that a
positive solution of `-Δu = f(u)` on the unit ball that vanishes on the sphere, with
`f` Lipschitz, is a strictly decreasing function of `|x|`. It applies in dimension two
to the truncated quadratic `max (1 - |x|², 0)` with the reaction `4 + |s| - s`, which
is not differentiable at zero. In dimension one it applies to `1 + cos(πx)`, whose
derivative vanishes at the boundary and whose reaction `π²(s - 1)` is negative at zero.
-/

@[expose] public noncomputable section

namespace PDE.Examples.RadialSymmetry

open Set Metric SobolevSpace
open scoped NNReal

/-- A globally Lipschitz reaction with a corner at zero. -/
def cornerReaction (s : ℝ) : ℝ := 4 + |s| - s

/-- The corner reaction is globally Lipschitz, including across zero. -/
theorem lipschitzWith_cornerReaction : LipschitzWith 2 cornerReaction := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  change |(4 + |a| - a) - (4 + |b| - b)| ≤ 2 * |a - b|
  calc
    |(4 + |a| - a) - (4 + |b| - b)| = |(|a| - |b|) - (a - b)| := by congr 1; ring
    _ ≤ |(|a| - |b|)| + |a - b| := abs_sub _ _
    _ ≤ |a - b| + |a - b| := by linarith [abs_abs_sub_abs_le_abs_sub a b]
    _ = 2 * |a - b| := by ring

/-- The reaction is not differentiable at zero. -/
theorem not_differentiableAt_cornerReaction :
    ¬ DifferentiableAt ℝ cornerReaction 0 := by
  intro h
  apply not_differentiableAt_abs_zero
  convert (h.sub_const 4).add (differentiableAt_id (x := (0 : ℝ))) using 1
  funext s
  change |s| = (4 + |s| - s - 4) + s
  ring

/-- The function `max (1 - |x|², 0)`, equal to `1 - |x|²` on the closed ball. -/
def truncatedQuadratic (x : ℝ^2) : ℝ := max (1 - ‖x‖ ^ 2) 0

private theorem truncatedQuadratic_eq {x : ℝ^2} (hx : x ∈ closedBall (0 : ℝ^2) 1) :
    truncatedQuadratic x = 1 - ‖x‖ ^ 2 := by
  have hn : ‖x‖ ≤ 1 := by simpa using hx
  exact max_eq_left (by nlinarith [norm_nonneg x])

/-- The truncated quadratic is `C²` up to the boundary of the ball. -/
theorem contDiffUpToBoundary_truncatedQuadratic :
    ContDiffUpToBoundary 2 truncatedQuadratic (ball (0 : ℝ^2) 1) := by
  have hg : ContDiff ℝ 2 (fun x : ℝ^2 ↦ 1 - ‖x‖ ^ 2) :=
    contDiff_const.sub (contDiff_norm_sq ℝ)
  exact (ContDiffUpToBoundary.of_contDiff hg isBounded_ball).congr isOpen_ball
    (fun _ hx ↦ truncatedQuadratic_eq (ball_subset_closedBall hx))

private theorem truncatedQuadratic_pos {x : ℝ^2} (hx : x ∈ ball (0 : ℝ^2) 1) :
    0 < truncatedQuadratic x := by
  rw [truncatedQuadratic_eq (ball_subset_closedBall hx)]
  have hn : ‖x‖ < 1 := by simpa using hx
  nlinarith [norm_nonneg x]

/-- In the ball the truncated quadratic solves `-Δu = 4 + |u| - u`. -/
theorem truncatedQuadratic_equation {x : ℝ^2} (hx : x ∈ ball (0 : ℝ^2) 1) :
    -laplacian truncatedQuadratic x = cornerReaction (truncatedQuadratic x) := by
  have heq : EqOn truncatedQuadratic (fun y : ℝ^2 ↦ 1 - ‖y‖ ^ 2)
      (ball (0 : ℝ^2) 1) := fun _ hy ↦ truncatedQuadratic_eq (ball_subset_closedBall hy)
  rw [EuclideanLaplacian.laplacian_congr_nhds
    (heq.eventuallyEq_of_mem (isOpen_ball.mem_nhds hx))]
  rw [laplacian_sub _ _ x contDiffAt_const (contDiff_norm_sq ℝ).contDiffAt,
    laplacian_const, EuclideanLaplacian.laplacian_norm_sq, cornerReaction,
    abs_of_pos (truncatedQuadratic_pos hx)]
  norm_num

/-- The truncated quadratic is a strictly decreasing function of `|x|` on the closed
disk. -/
theorem truncatedQuadratic_radial_profile :
    ∃ v : ℝ → ℝ, ContinuousOn v (Icc 0 1) ∧ StrictAntiOn v (Icc 0 1) ∧
      (∀ r ∈ Icc 0 1, 0 ≤ v r) ∧ v 1 = 0 ∧
      ∀ x ∈ closedBall (0 : ℝ^2) 1, truncatedQuadratic x = v ‖x‖ := by
  apply Elliptic.Semilinear.exists_strictAntiOn_radial_profile_of_lipschitz
    lipschitzWith_cornerReaction contDiffUpToBoundary_truncatedQuadratic
    (by unfold truncatedQuadratic; fun_prop)
    (fun _ hx ↦ truncatedQuadratic_equation hx) (fun _ hx ↦ truncatedQuadratic_pos hx)
  intro x hx
  have hn : ‖x‖ = 1 := by simpa using hx
  simp [truncatedQuadratic, hn]

/-- A positive one-dimensional profile with vanishing derivative at both boundary points. -/
def cosineProfile (x : ℝ^1) : ℝ := 1 + Real.cos (Real.pi * x 0)

/-- The affine reaction `π²(s - 1)`, which is negative at `s = 0`. -/
def cosineReaction (s : ℝ) : ℝ := Real.pi ^ 2 * (s - 1)

private theorem contDiff_cosineProfile : ContDiff ℝ 2 cosineProfile := by
  unfold cosineProfile
  fun_prop

/-- The cosine profile solves `-Δu = π²(u - 1)`. -/
theorem cosineProfile_equation (x : ℝ^1) :
    -laplacian cosineProfile x = cosineReaction (cosineProfile x) := by
  unfold cosineProfile cosineReaction
  cas

private theorem abs_coordinate_eq_one {x : ℝ^1} (hx : x ∈ sphere (0 : ℝ^1) 1) :
    |x 0| = 1 := by
  have hn : ‖x‖ = 1 := by simpa using hx
  have hxsingle : x = EuclideanSpace.single 0 (x 0) := by
    ext i
    fin_cases i
    simp
  have hnorm := congrArg norm hxsingle
  rw [PiLp.norm_single, Real.norm_eq_abs] at hnorm
  exact hnorm.symm.trans hn

private theorem cosineProfile_zero {x : ℝ^1} (hx : x ∈ sphere (0 : ℝ^1) 1) :
    cosineProfile x = 0 := by
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp (abs_coordinate_eq_one hx) with h | h
  · simp [cosineProfile, h]
  · simp [cosineProfile, h]

private theorem cosineProfile_pos {x : ℝ^1} (hx : x ∈ ball (0 : ℝ^1) 1) :
    0 < cosineProfile x := by
  have hn : ‖x‖ < 1 := by simpa using hx
  have hcoord : |x 0| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 0
  have hc : |x 0| < 1 := hcoord.trans_lt hn
  have ht : |Real.pi * x 0| < Real.pi := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg (Real.pi * x 0)) le_rfl ht
  rw [Real.cos_pi, Real.cos_abs] at h
  dsimp [cosineProfile]
  linarith

/-- The first derivative vanishes at the boundary, where the Laplacian is positive. -/
theorem cosineProfile_boundary_jet {x : ℝ^1} (hx : x ∈ sphere (0 : ℝ^1) 1) :
    (∂[0] cosineProfile) x = 0 ∧ laplacian cosineProfile x = Real.pi ^ 2 := by
  have hd (y : ℝ^1) :
      (∂[0] cosineProfile) y = -Real.pi * Real.sin (Real.pi * y 0) := by
    unfold cosineProfile
    cas
  have habs := abs_coordinate_eq_one hx
  refine ⟨?_, ?_⟩
  · rw [hd]
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs with h | h <;> simp [h]
  · have h := cosineProfile_equation x
    rw [cosineProfile_zero hx, cosineReaction] at h
    linarith

/-- The cosine profile is a strictly decreasing function of `|x|` on `[-1, 1]`. -/
theorem cosineProfile_radial_profile :
    ∃ v : ℝ → ℝ, ContinuousOn v (Icc 0 1) ∧ StrictAntiOn v (Icc 0 1) ∧
      (∀ r ∈ Icc 0 1, 0 ≤ v r) ∧ v 1 = 0 ∧
      ∀ x ∈ closedBall (0 : ℝ^1) 1, cosineProfile x = v ‖x‖ := by
  have hf : LipschitzWith ⟨Real.pi ^ 2, sq_nonneg _⟩ cosineReaction := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    change |Real.pi ^ 2 * (a - 1) - Real.pi ^ 2 * (b - 1)| ≤
      Real.pi ^ 2 * |a - b|
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg Real.pi)]
    simp
  exact Elliptic.Semilinear.exists_strictAntiOn_radial_profile_of_lipschitz hf
    (ContDiffUpToBoundary.of_contDiff contDiff_cosineProfile isBounded_ball)
    contDiff_cosineProfile.continuous.continuousOn
    (fun x _ ↦ cosineProfile_equation x) (fun _ hx ↦ cosineProfile_pos hx)
    (fun _ hx ↦ cosineProfile_zero hx)

end PDE.Examples.RadialSymmetry
