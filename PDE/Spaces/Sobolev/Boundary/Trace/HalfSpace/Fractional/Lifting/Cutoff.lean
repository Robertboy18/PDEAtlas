/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalExtension

/-!
# Cutting off the height of a boundary lifting

The lifting uses mollification at height `t`. A fixed cutoff leaves this
construction unchanged near the boundary and makes it vanish for `t ≥ 2`.
We use the standard bump in one Euclidean dimension.
-/

@[expose] public section

noncomputable section

open Function Metric Set
open scoped Topology

namespace SobolevSpace.Trace.HalfSpace

open PDE.Analysis

/-- The height cutoff is one on `[-1,1]` and zero outside `(-2,2)`. -/
def heightCutoff (t : ℝ) : ℝ :=
  standardBump 1 (t • EuclideanSpace.single (0 : Fin 1) 1)

/-- The height cutoff is smooth on the whole real line. -/
theorem contDiff_heightCutoff : ContDiff ℝ (⊤ : ℕ∞) heightCutoff :=
  (standardBump 1).contDiff.comp (contDiff_id.smul contDiff_const)

/-- The height cutoff is nonnegative. -/
theorem heightCutoff_nonneg (t : ℝ) : 0 ≤ heightCutoff t :=
  (standardBump 1).nonneg

/-- The height cutoff never increases the magnitude of a function. -/
theorem heightCutoff_le_one (t : ℝ) : heightCutoff t ≤ 1 :=
  (standardBump 1).le_one

/-- The height cutoff preserves the lifting within unit distance of the boundary. -/
theorem heightCutoff_eq_one {t : ℝ} (ht : |t| ≤ 1) : heightCutoff t = 1 := by
  apply (standardBump 1).one_of_mem_closedBall
  simpa [standardBump, mem_closedBall, dist_zero_right, norm_smul, PiLp.norm_single] using ht

/-- The height cutoff vanishes once the distance from zero is at least two. -/
theorem heightCutoff_eq_zero {t : ℝ} (ht : 2 ≤ |t|) : heightCutoff t = 0 := by
  apply (standardBump 1).zero_of_le_dist
  simpa [standardBump, dist_zero_right, norm_smul, PiLp.norm_single] using ht

/-- The cutoff has compact support, so its derivative does as well. -/
theorem hasCompactSupport_heightCutoff : HasCompactSupport heightCutoff := by
  apply HasCompactSupport.intro (K := Icc (-2 : ℝ) 2) isCompact_Icc
  intro t ht
  apply heightCutoff_eq_zero
  have h : ¬ |t| ≤ 2 := by simpa only [abs_le, mem_Icc] using ht
  exact (lt_of_not_ge h).le

/-- The cutoff equals one on a neighborhood of the boundary. -/
theorem heightCutoff_eventuallyEq_one :
    heightCutoff =ᶠ[𝓝 (0 : ℝ)] fun _ ↦ 1 := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : 0 < (1 : ℝ))] with t ht
  apply heightCutoff_eq_one
  exact (show |t| < 1 by simpa [mem_ball, Real.dist_eq] using ht).le

end SobolevSpace.Trace.HalfSpace
