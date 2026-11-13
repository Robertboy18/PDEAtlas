/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harmonic.WeakMaximumPrinciple
public import PDE.Elliptic.PotentialTheory.GreenFunction.Ball.Dirichlet.Basic

/-!
# Uniqueness of the Dirichlet problem on a ball

The weak maximum principle identifies every classical solution with the Poisson solution when
their boundary values agree: for `0 < r` and `g` continuous on the sphere, a function harmonic in
`B(0, r)`, continuous on the closed ball and equal to `g` on the sphere agrees with
`poissonBallDirichletSolution r g` on the closed ball
(`eq_poissonBallDirichletSolution_of_isHarmonicPDE`). This is Evans's uniqueness theorem,
§2.2.3(a), Theorem 5, on a ball with `f = 0`, applied to the solution given by Poisson's formula
(45) in §2.2.4(c).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.3(a), Theorem 5 (Uniqueness), p. 28; §2.2.4(c),
  Poisson's formula (45) and Theorem 15 (Poisson's formula for ball), p. 41.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace GreenFunction

open LaplacianEquation
open Set

/-- The Poisson integral is the unique classical Dirichlet solution on a ball. -/
theorem eq_poissonBallDirichletSolution_of_isHarmonicPDE {n : ℕ} [Fact (0 < n)]
    {r : ℝ} (hr : 0 < r) {g u : ℝ^n → ℝ} (hg : ContinuousOn g (Metric.sphere (0 : ℝ^n) r))
    (hu : IsHarmonicPDE n u (Metric.ball (0 : ℝ^n) r))
    (hu_cont : ContinuousOn u (Metric.closedBall (0 : ℝ^n) r))
    (hu_boundary : ∀ x ∈ Metric.sphere (0 : ℝ^n) r, u x = g x) :
    Set.EqOn u (poissonBallDirichletSolution (n := n) r g)
      (Metric.closedBall (0 : ℝ^n) r) := by
  apply hu.eq_of_boundary_eq (poissonBallDirichletSolution_isHarmonicPDE (n := n) hr hg)
    hr hu_cont (continuousOn_poissonBallDirichletSolution (n := n) hr hg)
  intro x hx
  rw [poissonBallDirichletSolution_eq_boundary g hx]
  exact hu_boundary x hx

end GreenFunction
