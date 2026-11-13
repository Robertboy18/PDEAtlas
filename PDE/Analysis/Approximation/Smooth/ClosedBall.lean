/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Projection.Retraction
public import Mathlib.Geometry.Manifold.SmoothApprox

/-!
# Smooth approximation of a map between closed balls

Retraction onto the domain ball extends a continuous map to a uniformly continuous map on
the entire finite-dimensional space. A small contraction of its range leaves room for a smooth
approximation. The resulting globally smooth map takes values strictly inside the target ball
and approximates the original map uniformly on its domain.
-/

@[expose] public section

open Set Metric
open scoped ContDiff

namespace PDE.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous map between closed unit balls has uniformly close smooth approximations
defined on the whole domain space and valued strictly inside the target unit ball. -/
theorem exists_contDiff_strict_ball_approximation
    (f : C(closedBall (0 : E) 1, closedBall (0 : F) 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ (∀ x, ‖g x‖ < 1) ∧
      ∀ x : closedBall (0 : E) 1, dist (g x) (f x : F) < ε := by
  let : CompactSpace (closedBall (0 : E) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E) 1)
  obtain ⟨p, hp, hpball, hpid⟩ := exists_lipschitzWith_retraction_of_isComplete_convex
    (nonempty_closedBall.mpr (by norm_num : (0 : ℝ) ≤ 1))
    (isCompact_closedBall (0 : E) 1).isComplete (convex_closedBall (0 : E) 1)
  let F₀ : E → F := fun x ↦ (f ⟨p x, hpball x⟩ : F)
  have hF : UniformContinuous F₀ :=
    uniformContinuous_subtype_val.comp
      ((CompactSpace.uniformContinuous_of_continuous f.continuous).comp
        (hp.uniformContinuous.subtype_mk hpball))
  have hFnorm (x : E) : ‖F₀ x‖ ≤ 1 := by
    simpa only [mem_closedBall, dist_zero_right] using (f ⟨p x, hpball x⟩).property
  let η := min (1 / 4 : ℝ) (ε / 4)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hηone : η ≤ 1 / 4 := min_le_left _ _
  have hηε : η ≤ ε / 4 := min_le_right _ _
  have hshrink : 0 ≤ 1 - η := by linarith
  obtain ⟨g, hg, hnear, -⟩ := (hF.continuous.const_smul (1 - η)).exists_contDiff_approx
    (⊤ : ℕ∞) continuous_const fun _ ↦ half_pos hη
  change ∀ x, dist (g x) ((1 - η) • F₀ x) < η / 2 at hnear
  have hscaled (x : E) : ‖(1 - η) • F₀ x‖ ≤ 1 - η := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hshrink]
    exact mul_le_of_le_one_right hshrink (hFnorm x)
  have hmove (x : E) : dist ((1 - η) • F₀ x) (F₀ x) ≤ η := by
    have heq : (1 - η) • F₀ x - F₀ x = (-η) • F₀ x := by module
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hη]
    exact mul_le_of_le_one_right hη.le (hFnorm x)
  refine ⟨g, hg, ?_, ?_⟩
  · intro x
    have hnorm := norm_sub_norm_le (g x) ((1 - η) • F₀ x)
    rw [← dist_eq_norm] at hnorm
    have := hnear x
    have := hscaled x
    linarith
  · intro x
    have hid : F₀ x = (f x : F) := by
      dsimp [F₀]
      congr 2
      exact Subtype.ext (hpid x.property)
    rw [← hid]
    have := dist_triangle (g x) ((1 - η) • F₀ x) (F₀ x)
    have := hnear x
    have := hmove x
    linarith

end PDE.Analysis
