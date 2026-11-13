/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Tactic.Positivity.Finset

/-!
# Nearby contacts from a quadratic penalty

A quadratic penalty makes a local upper contact strict. Uniform convergence
on a small closed ball then places a maximum of each approximating difference
inside the ball. This argument uses continuity and compactness alone; derivative
estimates at the resulting contacts can be supplied separately.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Set Metric Filter
open scoped Topology

variable {X : Type*} [NormedAddCommGroup X] [ProperSpace X]

/-- A quadratic penalty produces nearby upper contacts for all sufficiently
late approximants. No derivatives of the approximants or the test are needed. -/
theorem eventually_exists_upper_contact_of_quadratic_penalty
    {Q : X → ℝ} (hQzero : Q 0 = 0) (hQlower : ∀ y, ‖y‖ ^ 2 ≤ Q y)
    {U : Set X} {v : ℕ → X → ℝ} {u φ : X → ℝ} {x : X} {r : ℝ}
    (hr : 0 < r) (hballU : closedBall x r ⊆ U)
    (hv : ∀ n, UpperSemicontinuousOn (v n) U)
    (hvu : TendstoLocallyUniformlyOn v u atTop U)
    (hφ : ContinuousOn (fun y ↦ φ y + Q (y - x)) (closedBall x r))
    (hmax : ∀ y ∈ closedBall x r, u y - φ y ≤ u x - φ x) :
    ∀ᶠ n in atTop, ∃ y ∈ ball x r,
      IsLocalMaxOn (fun z ↦ v n z - (φ z + Q (z - x))) U y := by
  have hconv : TendstoUniformlyOn v u atTop (closedBall x r) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (isCompact_closedBall x r)).mp (hvu.mono hballU)
  have herr := (Metric.tendstoUniformlyOn_iff.mp hconv) (r ^ 2 / 4) (by positivity)
  filter_upwards [herr] with n hn
  have hupper : UpperSemicontinuousOn
      (fun y ↦ v n y - (φ y + Q (y - x))) (closedBall x r) := by
    simpa only [sub_eq_add_neg] using!
      ((hv n).mono hballU).add hφ.neg.upperSemicontinuousOn
  obtain ⟨y, hy, hymax⟩ := UpperSemicontinuousOn.exists_isMaxOn
    ⟨x, mem_closedBall_self hr.le⟩ (isCompact_closedBall x r) hupper
  have hybound : ‖y - x‖ ≤ r := by
    simpa only [mem_closedBall, dist_eq_norm] using hy
  have hyinner : ‖y - x‖ < r := by
    by_contra h
    have hysphere : ‖y - x‖ = r := le_antisymm hybound (le_of_not_gt h)
    have hcenter := (isMaxOn_iff.mp hymax) x (mem_closedBall_self hr.le)
    have hex : |u x - v n x| < r ^ 2 / 4 := by
      simpa only [Real.dist_eq] using hn x (mem_closedBall_self hr.le)
    have hey : |u y - v n y| < r ^ 2 / 4 := by
      simpa only [Real.dist_eq] using hn y hy
    have hquadlower := hQlower (y - x)
    rw [hysphere] at hquadlower
    simp only [sub_self, hQzero, add_zero] at hcenter
    have hlimit := hmax y hy
    have hexupper := (abs_lt.mp hex).2
    have heylower := (abs_lt.mp hey).1
    linarith [sq_pos_of_pos hr]
  have hyball : y ∈ ball x r := by
    simpa only [mem_ball, dist_eq_norm] using hyinner
  exact ⟨y, hyball,
    (hymax.isLocalMax (closedBall_mem_nhds_of_mem hyball)).isLocalMaxOn U⟩

end PDE.Analysis
