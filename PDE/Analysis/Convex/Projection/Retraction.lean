/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-!
# Retraction onto a complete convex set

Nearest points define a nonexpansive retraction onto every nonempty complete convex subset of
a real inner product space. Completeness is needed only for the subset. The estimate follows
from the two variational inequalities for the nearest points.
-/

@[expose] public section

open Set
open scoped InnerProductSpace

namespace PDE.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A nonempty complete convex set admits a retraction with Lipschitz constant one. -/
theorem exists_lipschitzWith_retraction_of_isComplete_convex {K : Set H}
    (hne : K.Nonempty) (hcomplete : IsComplete K) (hconv : Convex ℝ K) :
    ∃ p : H → H, LipschitzWith 1 p ∧ (∀ x, p x ∈ K) ∧ EqOn p id K := by
  choose p hp hmin using exists_norm_eq_iInf_of_complete_convex hne hcomplete hconv
  have hvariational (x : H) (y : H) (hy : y ∈ K) :
      ⟪x - p x, y - p x⟫_ℝ ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hconv (hp x)).mp (hmin x) y hy
  refine ⟨p, LipschitzWith.of_dist_le_mul ?_, hp, ?_⟩
  · intro x y
    have hfirm : ‖p x - p y‖ ^ 2 ≤ ⟪x - y, p x - p y⟫_ℝ := by
      have hx := hvariational x (p y) (hp y)
      have hy := hvariational y (p x) (hp x)
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right] at hx hy ⊢
      linarith
    have hbound := hfirm.trans (real_inner_le_norm (x - y) (p x - p y))
    simp only [dist_eq_norm, NNReal.coe_one, one_mul]
    by_cases hz : ‖p x - p y‖ = 0
    · simp [hz]
    · have hpos : 0 < ‖p x - p y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      nlinarith
  · intro x hx
    have hself := hvariational x x hx
    rw [real_inner_self_eq_norm_sq] at hself
    have hz : ‖x - p x‖ = 0 := by nlinarith [norm_nonneg (x - p x)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

end PDE.Analysis
