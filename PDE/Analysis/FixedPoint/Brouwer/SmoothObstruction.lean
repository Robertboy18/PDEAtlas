/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Jacobian.Sphere
public import PDE.CalculusOfVariations.NullLagrangian.BoundaryAction
public import PDE.CalculusOfVariations.NullLagrangian.Determinant
public import PDE.Spaces.Sobolev.Boundary.Atlas.UnitBall.SmoothGraph

/-!
# The determinant obstruction to a smooth ball retraction

A `C²` map from the closed unit ball into the unit sphere has zero Jacobian determinant.
The determinant is a null Lagrangian, so its action depends only on boundary values. If the
map fixed the sphere, its action would equal that of the identity, which is the positive
volume of the ball. The boundary regularity of the ball comes from its smooth graph atlas.

These are steps 1 and 2 of Evans's proof of Brouwer's theorem (§8.1.4(c), Theorem 3). The two
facts about null Lagrangians are Theorems 1 and 2 of his §8.1.4(b), which we use as
`IsNullLagrangianOn.lagrangianAction_eq_of_contDiff` and `isNullLagrangianOn_determinant`; the
vanishing of the determinant is `det_jacobianMatrix_eq_zero_of_eventually_norm_eq`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.1.4(b), Theorem 1, p. 461, and Theorem 2, p. 463,
  and §8.1.4(c), steps 1 and 2 of the proof of Theorem 3, p. 464.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped Topology Matrix.Norms.Elementwise

namespace PDE.FixedPoint

open Analysis CalculusOfVariations SobolevSpace

/-- In positive dimension no ambient `C²` map can send the closed unit ball into its sphere
while fixing the sphere pointwise. -/
theorem not_contDiff_unitBall_retraction {n : ℕ} [Fact (0 < n)] {w : ℝ^n → ℝ^n}
    (hw : ContDiff ℝ 2 w) (hsphere : ∀ x ∈ closedBall (0 : ℝ^n) 1, ‖w x‖ = 1)
    (hboundary : EqOn w id (sphere (0 : ℝ^n) 1)) : False := by
  have haction := (isNullLagrangianOn_determinant
    (Ω := ball (0 : ℝ^n) 1) isOpen_ball).lagrangianAction_eq_of_contDiff
    isOpen_ball isBounded_ball
    ((Boundary.Atlas.UnitBall.hasContDiffGraphBoundary n 1).hasC1GraphBoundary le_rfl)
    (ContinuousSecondJetOn.ofContDiff contDiff_determinantLagrangian _)
    hw contDiff_id (by simpa only [frontier_ball (0 : ℝ^n) one_ne_zero] using hboundary)
  have hzero : lagrangianAction (ball (0 : ℝ^n) 1) determinantLagrangian w = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with x hx
    apply det_jacobianMatrix_eq_zero_of_eventually_norm_eq
      (hw.differentiable (by norm_num) x) one_ne_zero
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact hsphere y (ball_subset_closedBall hy)
  have hvolume : (0 : ℝ) = volume.real (ball (0 : ℝ^n) 1) := by
    rw [hzero] at haction
    change 0 = ∫ x in ball (0 : ℝ^n) 1,
      (jacobianMatrix (fun z : ℝ^n ↦ z) x).det at haction
    simpa only [jacobianMatrix_id, Matrix.det_one, setIntegral_const,
      smul_eq_mul, mul_one] using haction
  have hpos : 0 < volume.real (ball (0 : ℝ^n) 1) :=
    ENNReal.toReal_pos (ne_of_gt (measure_ball_pos volume (0 : ℝ^n) zero_lt_one))
      (ne_of_lt (isBounded_ball.measure_lt_top (μ := volume)))
  linarith

end PDE.FixedPoint
