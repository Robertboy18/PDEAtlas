/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Smooth.ClosedBall
public import PDE.Analysis.Convex.Ball.RayExit
public import PDE.Analysis.FixedPoint.Brouwer.SmoothObstruction

/-!
# Continuous Brouwer fixed points on the Euclidean unit ball

Every continuous self-map of the closed unit ball of `ℝ^n` has a fixed point. This is
Brouwer's fixed point theorem as stated in Evans, §8.1.4(c), Theorem 3. Dimension zero, where
the ball is a single point, is treated directly.

## Main results

* `exists_isFixedPt_unitClosedBall`: every continuous self-map of the closed unit ball of
  `ℝ^n` has a fixed point.

## How it works

Evans argues by contradiction. Steps 1 and 2 of his proof show, with the determinant as a null
Lagrangian, that no smooth map of the ball into its sphere fixes the sphere; step 3 mollifies a
continuous such map, and step 4 builds one from a self-map without fixed points by following
rays. We keep steps 1 and 2, as `not_contDiff_unitBall_retraction`, and the ray construction
of step 4, as `ballRayExit`, but replace step 3. If `f` had no fixed point, compactness would
give a positive minimum displacement `δ`, and `exists_contDiff_strict_ball_approximation` gives
a smooth map `g` with values strictly inside the ball and within `δ` of `f`, so `g` has no
fixed point anywhere. The ray construction applied to `g` is smooth (`ContDiff.ballRayExit`),
so we smooth the self-map instead of the retraction.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.1.4(c), Theorem 3 (Brouwer's fixed point theorem)
  and its proof, pp. 463-464. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set Metric Function
open scoped ContDiff

namespace PDE.FixedPoint

open Analysis

/-- Every continuous self-map of the closed Euclidean unit ball has a fixed point,
including in dimension zero. -/
theorem exists_isFixedPt_unitClosedBall (n : ℕ)
    (f : C(closedBall (0 : ℝ^n) 1, closedBall (0 : ℝ^n) 1)) :
    ∃ x, IsFixedPt f x := by
  classical
  by_cases hn : n = 0
  · subst n
    exact ⟨⟨0, by simp⟩, Subsingleton.elim _ _⟩
  have : Fact (0 < n) := ⟨Nat.pos_of_ne_zero hn⟩
  let : CompactSpace (closedBall (0 : ℝ^n) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  by_contra hno
  have hneq (x : closedBall (0 : ℝ^n) 1) : f x ≠ x := by
    intro hx
    exact hno ⟨x, hx⟩
  have hdist : Continuous (fun x : closedBall (0 : ℝ^n) 1 ↦ dist (f x) x) :=
    f.continuous.dist continuous_id
  obtain ⟨δ, hδ, hlower⟩ := isCompact_univ.exists_forall_le' hdist.continuousOn
    (fun x _ ↦ dist_pos.mpr (hneq x))
  obtain ⟨g, hg, hgnorm, happrox⟩ := exists_contDiff_strict_ball_approximation f hδ
  have hgnofix (x : ℝ^n) : x ≠ g x := by
    intro hx
    have hxball : x ∈ closedBall (0 : ℝ^n) 1 := by
      rw [mem_closedBall, dist_zero_right, hx]
      exact (hgnorm x).le
    have hnear := happrox ⟨x, hxball⟩
    have hlow := hlower ⟨x, hxball⟩ (mem_univ _)
    change δ ≤ dist (f ⟨x, hxball⟩ : ℝ^n) x at hlow
    rw [← hx, dist_comm] at hnear
    exact (not_lt_of_ge hlow) hnear
  apply not_contDiff_unitBall_retraction
    ((hg.ballRayExit contDiff_id hgnorm hgnofix).of_le (by simp))
  · intro x _
    exact norm_ballRayExit (hgnorm x) (hgnofix x)
  · intro x hx
    exact ballRayExit_eq_self_of_norm_eq_one (hgnorm x)
      (by simpa only [mem_sphere, dist_zero_right, id_eq] using hx)

end PDE.FixedPoint
