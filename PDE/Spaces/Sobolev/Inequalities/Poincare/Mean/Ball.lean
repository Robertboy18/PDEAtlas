/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Poincare.Mean.BallPullback
public import PDE.Spaces.Sobolev.Inequalities.Poincare.Mean.Endpoint
import PDE.Elliptic.Regularity.Boundary.ConcreteUnitBallAtlas

/-!
# Mean-subtracted Poincaré on balls

Poincaré's inequality for a ball (Evans §5.8.1, Theorem 2), for every `1 ≤ p ≤ ∞`. As in
Evans's proof, a constant for the unit ball comes from the connected-domain Poincaré theorem
(Evans §5.8.1, Theorem 1), applied with an explicit boundary atlas of the unit ball, and
the affine Sobolev pullback gives the estimate on every ball with the factor `r`.
The constant depends only on the dimension and exponent.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.1, Theorems 1 and 2, (7), pp. 290-291.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

/-- The mean-subtracted Poincaré estimate on the unit ball: for `1 ≤ p ≤ ∞` there is `C > 0`
with `‖u - (u)_{0,1}‖_{Lᵖ(B(0,1))} ≤ C * ‖∇ u‖` for every `u ∈ W^{1,p}(B(0, 1))`. The boundary
atlas of the ball is constructed explicitly. -/
theorem exists_poincare_mean_unitBall {n : ℕ} [Fact (0 < n)]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    ∃ C : ℝ, 0 < C ∧ ∀ U : W^{1,p}(ball (0 : ℝ^n) 1),
      (eLpNorm (fun x ↦ wkpBaseCoordinateCLM U x -
        ⨍ y, wkpBaseCoordinateCLM U y ∂domainMeasure n (ball 0 1))
          p (domainMeasure n (ball 0 1))).toReal ≤ C * ‖∇ U‖ := by
  let : Boundary.C1ExtensionAtlas n (ball (0 : ℝ^n) 1) :=
    (Boundary.Atlas.UnitBall.ConcreteAtlas.c2BoundaryAtlas n).toC1ExtensionAtlas
  obtain ⟨C, hC, hP⟩ := exists_norm_base_subtractMean_le_of_c1Domain (p := p)
    ((convex_ball (0 : ℝ^n) 1).isConnected (nonempty_ball.mpr zero_lt_one))
  refine ⟨C, hC, fun U ↦ ?_⟩
  rw [← eLpNorm_congr_ae (subtractMean_base_ae U), ← Lp.norm_def]
  exact hP U

/-- Evans §5.8.1, Theorem 2: on every ball of positive radius, the `Lᵖ` norm of a Sobolev
function minus its integral average is at most `C(n,p) r` times its weak gradient norm.
The constant is independent of the center and radius, and the exponent includes infinity. -/
theorem exists_poincare_mean_ball {n : ℕ} [Fact (0 < n)]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℝ^n) (r : ℝ), 0 < r →
      ∀ U : W^{1,p}(ball x r),
        (eLpNorm (fun y ↦ wkpBaseCoordinateCLM U y -
          ⨍ z, wkpBaseCoordinateCLM U z ∂domainMeasure n (ball x r))
            p (domainMeasure n (ball x r))).toReal ≤ C * r * ‖∇ U‖ := by
  obtain ⟨C, hC, hP⟩ := exists_poincare_mean_unitBall (n := n) (p := p)
  refine ⟨C, hC, fun x r hr U ↦ ?_⟩
  obtain ⟨V, hmean, hgrad⟩ := MeanScaling.exists_ballPullback_scaling x hr U
  have h := hP V
  rw [hmean, hgrad] at h
  apply (mul_le_mul_iff_right₀ (MeanScaling.normFactor_pos (n := n) hr p)).mp
  calc
    _ ≤ C * (MeanScaling.normFactor n r p * (r * ‖∇ U‖)) := h
    _ = _ := by ring

end SobolevSpace.GraphSpace
