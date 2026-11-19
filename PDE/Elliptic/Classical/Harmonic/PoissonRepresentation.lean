/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harmonic.MathlibBridge
public import PDE.Elliptic.PotentialTheory.GreenFunction.Ball.Dirichlet.Uniqueness
public import Mathlib.Topology.TietzeExtension
import PDE.FDeriv.Calculus

/-!
# Local Poisson representation of harmonic functions

On every closed ball contained in its domain, a harmonic function agrees in the
interior with the Poisson extension of its boundary trace. Mathlib's Tietze extension theorem
(`ContinuousMap.exists_restrict_eq`) supplies continuous data on the ambient space; uniqueness
makes the choice of extension immaterial. Mean-value formulas, interior smoothness, and derivative
estimates can all use this one representation.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.3, Theorem 5 (Uniqueness), p. 28; §2.2.4, Poisson's
  formula (45) and Theorem 15 (Poisson's formula for ball), p. 41.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace LaplacianEquation

open MeasureTheory Set

/-- A harmonic function on a set containing a closed ball has a Poisson
representation after translating the ball to the origin. The continuous datum
agrees with the original function on the translated boundary sphere. -/
theorem IsHarmonicPDE.exists_poisson_representation {n : ℕ} [Fact (0 < n)]
    {u : ℝ^n → ℝ} {U : Set (ℝ^n)} (hu : IsHarmonicPDE n u U)
    {x : ℝ^n} {r : ℝ} (hr : 0 < r) (hclosed : Metric.closedBall x r ⊆ U) :
    ∃ g : C(ℝ^n, ℝ),
      EqOn (g : ℝ^n → ℝ) (fun z ↦ u (x + z)) (Metric.sphere (0 : ℝ^n) r) ∧
      EqOn (fun z ↦ u (x + z)) (GreenFunction.poissonBallExtension r g)
        (Metric.ball (0 : ℝ^n) r) := by
  classical
  let v : ℝ^n → ℝ := fun z ↦ u (x + z)
  have hu_ball : IsHarmonicPDE n u (Metric.ball x r) :=
    hu.mono (Metric.ball_subset_closedBall.trans hclosed)
  have hmap_open : MapsTo (x + ·) (Metric.ball (0 : ℝ^n) r) (Metric.ball x r) := fun z hz ↦ by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hmap_closed : MapsTo (x + ·) (Metric.closedBall (0 : ℝ^n) r) (Metric.closedBall x r) :=
    fun z hz ↦ by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hv_harmonic : IsHarmonicPDE n v (Metric.ball (0 : ℝ^n) r) := by
    refine ⟨hu_ball.contDiffOn.comp (by fun_prop) hmap_open, fun z hz ↦ ?_⟩
    simpa [v] using (PDE.laplacian_comp_add_left u x z
      (hu_ball.contDiffAt_of_isOpen Metric.isOpen_ball (hmap_open hz))).trans
        (hu_ball.laplacian_eq_zero (hmap_open hz))
  have hv_cont_closed : ContinuousOn v (Metric.closedBall (0 : ℝ^n) r) :=
    ((hu.contDiffOn.mono hclosed).comp (by fun_prop) hmap_closed).continuousOn
  obtain ⟨g, hg_restrict⟩ := ContinuousMap.exists_restrict_eq Metric.isClosed_sphere
    (⟨fun z ↦ v z, continuousOn_iff_continuous_domRestrict.mp
      (hv_cont_closed.mono Metric.sphere_subset_closedBall)⟩ : C(Metric.sphere (0 : ℝ^n) r, ℝ))
  have hg_boundary : EqOn (g : ℝ^n → ℝ) v (Metric.sphere (0 : ℝ^n) r) := fun z hz ↦
    congrArg (fun q : C(Metric.sphere (0 : ℝ^n) r, ℝ) ↦ q ⟨z, hz⟩) hg_restrict
  have hv_unique := GreenFunction.eq_poissonBallDirichletSolution_of_isHarmonicPDE
    (n := n) hr g.continuous.continuousOn hv_harmonic hv_cont_closed
    (fun z hz ↦ (hg_boundary hz).symm)
  exact ⟨g, hg_boundary, fun z hz ↦ (hv_unique (Metric.ball_subset_closedBall hz)).trans
    (GreenFunction.poissonBallDirichletSolution_eq_extension g hz)⟩

end LaplacianEquation
