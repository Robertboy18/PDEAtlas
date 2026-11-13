/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harmonic.LevelSets.StarConvex
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# A shifted logarithmic harmonic level set

The annulus has center `(1/2, 0)` and radii one and two. Both bounding balls are
star-convex about the origin, but the logarithmic potential is centered elsewhere.
The potential is harmonic on the annulus, equal to one on the inner circle and zero on
the outer circle, so the level-set theorem `filledSuperlevel_geometry` makes its filled
superlevel sets star-convex about the origin with smooth graph boundary
(`smooth_starConvex_level`).
-/

@[expose] public section

open Set Metric PDE.Analysis LaplacianEquation
open scoped ContDiff

namespace PDE.Examples.ShiftedLogLevelSets

/-- The center `(1/2, 0)` of the annulus and pole of the potential. -/
noncomputable def center : ℝ^2 := EuclideanSpace.single 0 (1 / 2)

/-- Squared distance from the shifted pole in coordinates. -/
noncomputable def radiusSquared (p : ℝ^2) : ℝ := (p 0 - 1 / 2) ^ 2 + (p 1) ^ 2

/-- The normalized logarithmic potential between radii one and two. -/
noncomputable def profile (p : ℝ^2) : ℝ :=
  1 - Real.log (radiusSquared p) / Real.log 4

private theorem radiusSquared_eq_norm_sq (p : ℝ^2) :
    radiusSquared p = ‖p - center‖ ^ 2 := by
  simpa [radiusSquared, center, Fin.sum_univ_two] using
    (EuclideanSpace.real_norm_sq_eq (p - center)).symm

private theorem radiusSquared_pos_on_closure
    {p : ℝ^2} (hp : p ∈ closure (ball center 2 \ closure (ball center 1))) :
    0 < radiusSquared p := by
  have hsub : ball center 2 \ closure (ball center 1) ⊆ (ball center 1)ᶜ :=
    fun _ hq hqball ↦ hq.2 (subset_closure hqball)
  have hpnot : p ∉ ball center 1 :=
    closure_minimal hsub isOpen_ball.isClosed_compl hp
  have hpdist : 1 ≤ ‖p - center‖ := by
    simpa only [mem_ball, dist_eq_norm, not_lt] using hpnot
  rw [radiusSquared_eq_norm_sq]
  nlinarith

private theorem contDiffAt_profile {p : ℝ^2} (hp : radiusSquared p ≠ 0) :
    ContDiffAt ℝ 2 profile p := by
  have hq : ContDiff ℝ 2 radiusSquared := by
    unfold radiusSquared
    fun_prop
  exact contDiffAt_const.sub ((hq.contDiffAt.log hp).div_const (Real.log 4))

/-- The potential is harmonic on the annulus. -/
theorem isHarmonicPDE_profile :
    IsHarmonicPDE 2 profile (ball center 2 \ closure (ball center 1)) := by
  refine ⟨fun p hp ↦ (contDiffAt_profile
    (radiusSquared_pos_on_closure (subset_closure hp)).ne').contDiffWithinAt, ?_⟩
  intro p hp
  have hq : (p 0 - 1 / 2) ^ 2 + (p 1) ^ 2 ≠ 0 :=
    (radiusSquared_pos_on_closure (subset_closure hp)).ne'
  have hlog : Real.log 4 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 4)).ne'
  unfold profile radiusSquared
  cas

private theorem continuousOn_profile_closure :
    ContinuousOn profile (closure (ball center 2 \ closure (ball center 1))) :=
  fun _ hp ↦
    (contDiffAt_profile (radiusSquared_pos_on_closure hp).ne').continuousAt.continuousWithinAt

private theorem profile_inner (p : ℝ^2) (hp : p ∈ frontier (ball center 1)) :
    profile p = 1 := by
  rw [frontier_ball center one_ne_zero] at hp
  have hnorm : ‖p - center‖ = 1 := by simpa only [mem_sphere, dist_eq_norm] using hp
  simp [profile, radiusSquared_eq_norm_sq, hnorm]

private theorem profile_outer (p : ℝ^2) (hp : p ∈ frontier (ball center 2)) :
    profile p = 0 := by
  rw [frontier_ball center (by norm_num : (2 : ℝ) ≠ 0)] at hp
  have hnorm : ‖p - center‖ = 2 := by simpa only [mem_sphere, dist_eq_norm] using hp
  have hlog : Real.log 4 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 4)).ne'
  norm_num [profile, radiusSquared_eq_norm_sq, hnorm, hlog]

/-- The filled level sets of the off-center logarithmic potential are star-convex about the
origin, with smooth boundary equal to the level curve. -/
theorem smooth_starConvex_level {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    StarConvex ℝ 0 (filledSuperlevel (closure (ball center 1)) (ball center 2) profile c) ∧
      SobolevSpace.Boundary.HasContDiffGraphBoundary ⊤
        (filledSuperlevel (closure (ball center 1)) (ball center 2) profile c) ∧
      frontier (filledSuperlevel (closure (ball center 1)) (ball center 2) profile c) =
        {p | p ∈ ball center 2 \ closure (ball center 1) ∧ profile p = c} := by
  have hzero : ‖(0 : ℝ^2) - center‖ = 1 / 2 := by
    norm_num [center]
  have hinner : StarConvex ℝ 0 (closure (ball center 1)) := by
    rw [closure_ball center one_ne_zero]
    exact (convex_closedBall center 1).starConvex (by
      simpa only [mem_closedBall, dist_eq_norm, hzero] using (by norm_num : (1 / 2 : ℝ) ≤ 1))
  have houter : StarConvex ℝ 0 (ball center 2) :=
    (convex_ball center 2).starConvex (by
      simpa only [mem_ball, dist_eq_norm, hzero] using (by norm_num : (1 / 2 : ℝ) < 2))
  have hsub : closure (ball center 1) ⊆ ball center 2 := by
    rw [closure_ball center one_ne_zero]
    exact closedBall_subset_ball (by norm_num)
  obtain ⟨_, _, hstar, hfront, hgraph, _⟩ :=
    isHarmonicPDE_profile.filledSuperlevel_geometry hinner houter isOpen_ball isBounded_ball
      hsub continuousOn_profile_closure profile_inner profile_outer hc0 hc1
  exact ⟨hstar, hgraph, hfront⟩

/-- The point `center + (√2, 0)`, at distance `√2` from the center. -/
noncomputable def halfLevelPoint : ℝ^2 := center + EuclideanSpace.single 0 (Real.sqrt 2)

/-- The smooth half-level boundary is nonempty. -/
theorem halfLevelPoint_mem_frontier :
    halfLevelPoint ∈
      frontier (filledSuperlevel (closure (ball center 1)) (ball center 2) profile (1 / 2)) := by
  rw [(smooth_starConvex_level (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)).2.2]
  have hnorm : ‖halfLevelPoint - center‖ = Real.sqrt 2 := by
    simp [halfLevelPoint, Real.sqrt_nonneg]
  have hsqrt : 1 < Real.sqrt 2 ∧ Real.sqrt 2 < 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hn := Real.sqrt_nonneg (2 : ℝ)
    constructor <;> nlinarith
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa only [mem_ball, dist_eq_norm, hnorm] using hsqrt.2
  · rw [closure_ball center one_ne_zero]
    simpa only [mem_closedBall, dist_eq_norm, hnorm, not_le] using hsqrt.1
  · have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    have hlogfour : Real.log 4 = 2 * Real.log 2 := by
      calc
        Real.log 4 = Real.log ((2 : ℝ) ^ 2) := by norm_num
        _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
    simp only [profile, radiusSquared_eq_norm_sq, hnorm,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), hlogfour]
    field_simp [hlog]
    ring

end PDE.Examples.ShiftedLogLevelSets
