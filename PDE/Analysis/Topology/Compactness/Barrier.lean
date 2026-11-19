/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Real

/-!
# Domination by a barrier on a compact set

A continuous nonnegative function that is positive away from one point controls
the oscillation of any continuous function, up to an arbitrarily small constant.
Continuity controls a neighbourhood of the distinguished point; a positive
minimum of the barrier controls the remaining compact set.
-/

public section

namespace PDE.Analysis

open Metric Set

/-- On a compact set, a barrier positive off `z` controls the oscillation of
a continuous function about its value at `z`, up to any positive error. -/
theorem exists_nonneg_mul_barrier_bound
    {X : Type*} [PseudoMetricSpace X] {K : Set X} (hK : IsCompact K)
    {f b : X → ℝ} (hf : ContinuousOn f K) (hb : ContinuousOn b K)
    (hb0 : ∀ x ∈ K, 0 ≤ b x) {z : X} (hz : z ∈ K)
    (hbpos : ∀ x ∈ K, x ≠ z → 0 < b x) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |f x - f z| ≤ ε + C * b x := by
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousWithinAt_iff.mp (hf z hz) ε hε
  have hKfar : IsCompact (K \ Metric.ball z δ) := hK.diff isOpen_ball
  obtain ⟨κ, hκ, hfar⟩ := hKfar.exists_forall_le'
    (hb.mono sdiff_subset) (a := 0) (fun x hx ↦ hbpos x hx.1 (by
      intro hxz
      subst x
      exact hx.2 (by simpa only [mem_ball, dist_self] using hδ)))
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (f := fun x ↦ f x - f z)
    (show ContinuousOn (fun x ↦ f x - f z) K from hf.sub continuousOn_const)
  have hM0 : 0 ≤ M := by simpa only [sub_self, norm_zero] using hM z hz
  refine ⟨M / κ, div_nonneg hM0 hκ.le, ?_⟩
  intro x hx
  by_cases hxd : dist x z < δ
  · have hsmall : |f x - f z| < ε := by
      simpa only [Real.dist_eq] using hnear hx hxd
    exact hsmall.le.trans (le_add_of_nonneg_right
      (mul_nonneg (div_nonneg hM0 hκ.le) (hb0 x hx)))
  · have hxκ := hfar x ⟨hx, hxd⟩
    have hlarge : M ≤ M / κ * b x := by
      calc
        M = (M / κ) * κ := (div_mul_cancel₀ M hκ.ne').symm
        _ ≤ (M / κ) * b x :=
          mul_le_mul_of_nonneg_left hxκ (div_nonneg hM0 hκ.le)
    exact (show |f x - f z| ≤ M by simpa only [Real.norm_eq_abs] using hM x hx).trans
      (hlarge.trans (le_add_of_nonneg_left hε.le))

end PDE.Analysis
