/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harmonic.Definitions
public import PDE.Elliptic.PotentialTheory.GreenFunction.Ball.PoissonExtension.BoundaryConvergence

/-!
# The classical Dirichlet solution on a ball

We define `poissonBallDirichletSolution r g`, the Poisson extension of `g` in the open ball
`B(0, r)` with the data `g` attached outside it. For `0 < r` and `g` continuous on the sphere we
prove that it equals `g` on the sphere, is continuous on the closed ball and is harmonic in the
open ball, so that it is a classical solution of Evans's boundary-value problem (44) in §2.2.4(c),
the solution given by Theorem 15 there.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(c), the boundary-value problem (44), p. 40, and
  Theorem 15 (Poisson's formula for ball), p. 41.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace GreenFunction

open LaplacianEquation
open Set

variable {n : ℕ}

open scoped Classical in
/-- The Poisson solution with its prescribed boundary values attached outside the open ball. -/
noncomputable def poissonBallDirichletSolution (r : ℝ) (g : ℝ^n → ℝ) : ℝ^n → ℝ :=
  fun x ↦ if x ∈ Metric.ball (0 : ℝ^n) r then poissonBallExtension (n := n) r g x else g x

/-- Inside the open ball, attaching the boundary data leaves the Poisson extension unchanged. -/
@[simp] theorem poissonBallDirichletSolution_eq_extension {r : ℝ} (g : ℝ^n → ℝ)
    {x : ℝ^n} (hx : x ∈ Metric.ball (0 : ℝ^n) r) :
    poissonBallDirichletSolution (n := n) r g x =
      poissonBallExtension (n := n) r g x := by
  simp [poissonBallDirichletSolution, hx]

/-- On the boundary sphere, the boundary-attached Poisson solution equals the prescribed data. -/
theorem poissonBallDirichletSolution_eq_boundary {r : ℝ} (g : ℝ^n → ℝ)
    {x : ℝ^n} (hx : x ∈ Metric.sphere (0 : ℝ^n) r) :
    poissonBallDirichletSolution (n := n) r g x = g x := by
  have hxnot : x ∉ Metric.ball (0 : ℝ^n) r := by
    intro hxball
    exact Metric.sphere_disjoint_ball.ne_of_mem hx hxball rfl
  simp [poissonBallDirichletSolution, hxnot]

/-- The boundary-attached Poisson solution is continuous on the closed ball. -/
theorem continuousOn_poissonBallDirichletSolution {r : ℝ}
    (hr : 0 < r) {g : ℝ^n → ℝ} (hg : ContinuousOn g (Metric.sphere (0 : ℝ^n) r)) :
    ContinuousOn (poissonBallDirichletSolution (n := n) r g)
      (Metric.closedBall (0 : ℝ^n) r) := by
  classical
  intro x hxclosed
  by_cases hxball : x ∈ Metric.ball (0 : ℝ^n) r
  · have hpbeAt : ContinuousAt (poissonBallExtension (n := n) r g) x :=
      ((contDiffOn_poissonBallExtension (m := 0) (n := n) (r := r) hr hg x hxball).contDiffAt
        (Metric.isOpen_ball.mem_nhds hxball)).continuousAt
    have heq :
        poissonBallDirichletSolution (n := n) r g =ᶠ[nhds x]
          poissonBallExtension (n := n) r g := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hxball] with y hy
      exact poissonBallDirichletSolution_eq_extension g hy
    exact (hpbeAt.congr_of_eventuallyEq heq).continuousWithinAt
  · have hxsphere : x ∈ Metric.sphere (0 : ℝ^n) r := by
      rw [Metric.mem_sphere]
      exact le_antisymm
        (by simpa [Metric.mem_closedBall, dist_eq_norm] using hxclosed)
        (by simpa [Metric.mem_ball, dist_eq_norm, not_lt] using hxball)
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ :=
      poissonBallExtension_tendsto_g_on_sphere (n := n) (r := r) hg x hxsphere ε hε
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ :=
      Metric.continuousWithinAt_iff.mp (hg x hxsphere) ε hε
    refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, ?_⟩
    intro y hyclosed hynear
    have hyδ₁ : dist y x < δ₁ := hynear.trans_le (min_le_left _ _)
    have hyδ₂ : dist y x < δ₂ := hynear.trans_le (min_le_right _ _)
    have hxvalue := poissonBallDirichletSolution_eq_boundary g hxsphere
    by_cases hyball : y ∈ Metric.ball (0 : ℝ^n) r
    · simpa [poissonBallDirichletSolution_eq_extension g hyball, hxvalue, Real.dist_eq] using
        hδ₁ y hyball hyδ₁
    · have hyvalue : poissonBallDirichletSolution (n := n) r g y = g y := by
        simp [poissonBallDirichletSolution, hyball]
      have hysphere : y ∈ Metric.sphere (0 : ℝ^n) r := by
        rw [Metric.mem_sphere]
        exact le_antisymm hyclosed (not_lt.mp hyball)
      simpa [hyvalue, hxvalue] using hδ₂ hysphere hyδ₂

/-- The boundary-attached Poisson solution is PDE-harmonic in the open ball. -/
theorem poissonBallDirichletSolution_isHarmonicPDE {r : ℝ} (hr : 0 < r)
    {g : ℝ^n → ℝ} (hg : ContinuousOn g (Metric.sphere (0 : ℝ^n) r)) :
    IsHarmonicPDE n (poissonBallDirichletSolution (n := n) r g)
      (Metric.ball (0 : ℝ^n) r) := by
  have heq : Set.EqOn (poissonBallDirichletSolution (n := n) r g)
      (poissonBallExtension (n := n) r g) (Metric.ball (0 : ℝ^n) r) :=
    fun _ hx ↦ poissonBallDirichletSolution_eq_extension g hx
  have hbase :
      IsHarmonicPDE n (poissonBallExtension (n := n) r g)
        (Metric.ball (0 : ℝ^n) r) :=
    ⟨contDiffOn_poissonBallExtension (m := 2) (n := n) (r := r) hr hg,
      fun x hx ↦ laplacian_poissonBallExtension_eq_zero (n := n) (r := r) hr hg hx⟩
  constructor
  · exact hbase.contDiffOn.congr heq
  · intro x hx
    have hlocal :
        poissonBallDirichletSolution (n := n) r g =ᶠ[nhds x]
          poissonBallExtension (n := n) r g := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
      exact heq hy
    rw [EuclideanLaplacian.laplacian_congr_nhds hlocal]
    exact hbase.laplacian_eq_zero hx

end GreenFunction
