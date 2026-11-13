/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.NullLagrangian.BoundaryAction
public import PDE.CalculusOfVariations.NullLagrangian.Determinant
public import PDE.Spaces.Sobolev.Boundary.Atlas.UnitBall.SmoothGraph
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# A nonlinear equal-boundary determinant integral on the disk

The polynomial map `(x(x²+y²), y)` equals the identity on the unit circle.
Its Jacobian determinant is `3x²+y²`, so it is singular at the origin and is
not constant. Since the map agrees with the identity on the circle, the determinant
integral over the disk equals the integral of `1`, the area of the disk.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric
open scoped Matrix.Norms.Elementwise

namespace PDE.Examples.NullBoundary

open Analysis CalculusOfVariations SobolevSpace

/-- A nonlinear disk deformation fixing every point of the unit circle. -/
def diskDeformation (x : ℝ^2) : ℝ^2 :=
  WithLp.toLp 2 ![x 0 * (x 0 ^ 2 + x 1 ^ 2), x 1]

/-- `diskDeformation` is `C²`. -/
theorem contDiff_diskDeformation : ContDiff ℝ 2 diskDeformation := by
  apply (contDiff_piLp 2).mpr
  intro k
  fin_cases k
  · change ContDiff ℝ 2 (fun x : ℝ^2 ↦ x 0 * (x 0 ^ 2 + x 1 ^ 2))
    cas
  · change ContDiff ℝ 2 (fun x : ℝ^2 ↦ x 1)
    cas

/-- The Jacobian matrix of `diskDeformation` is `!![3x₀² + x₁², 2x₀x₁; 0, 1]`. -/
theorem jacobianMatrix_diskDeformation (x : ℝ^2) :
    jacobianMatrix diskDeformation x = !![3 * x 0 ^ 2 + x 1 ^ 2, 2 * x 0 * x 1; 0, 1] := by
  ext k i
  fin_cases k <;> fin_cases i
  · change (∂[0] (fun y : ℝ^2 ↦ y 0 * (y 0 ^ 2 + y 1 ^ 2))) x =
      3 * x 0 ^ 2 + x 1 ^ 2
    cas
  · change (∂[1] (fun y : ℝ^2 ↦ y 0 * (y 0 ^ 2 + y 1 ^ 2))) x =
      2 * x 0 * x 1
    cas
  · change (∂[0] (fun y : ℝ^2 ↦ y 1)) x = 0
    cas
  · change (∂[1] (fun y : ℝ^2 ↦ y 1)) x = 1
    cas

/-- The Jacobian determinant is `3x₀² + x₁²`. -/
theorem det_jacobianMatrix_diskDeformation (x : ℝ^2) :
    (jacobianMatrix diskDeformation x).det = 3 * x 0 ^ 2 + x 1 ^ 2 := by
  rw [jacobianMatrix_diskDeformation, Matrix.det_fin_two]
  simp

/-- The Jacobian is singular at the interior point `0`. -/
theorem det_jacobianMatrix_diskDeformation_zero :
    (jacobianMatrix diskDeformation 0).det = 0 := by
  simp [det_jacobianMatrix_diskDeformation]

/-- The deformation agrees pointwise with the identity on the boundary. -/
theorem diskDeformation_eq_on_frontier :
    EqOn diskDeformation (fun x ↦ x) (frontier (ball (0 : ℝ^2) 1)) := by
  intro x hx
  have hxnorm : ‖x‖ = 1 := by
    simpa [frontier_ball (0 : ℝ^2) one_ne_zero, mem_sphere, dist_zero_right] using hx
  have hs : x 0 ^ 2 + x 1 ^ 2 = 1 := by
    simpa [Fin.sum_univ_two, hxnorm] using (EuclideanSpace.real_norm_sq_eq x).symm
  ext k
  fin_cases k
  · change x 0 * (x 0 ^ 2 + x 1 ^ 2) = x 0
    rw [hs, mul_one]
  · rfl

/-- The disk map and the identity agree on the circle, so they have the same determinant
action. -/
theorem diskDeformation_action_eq_identity :
    lagrangianAction (ball (0 : ℝ^2) 1) determinantLagrangian diskDeformation =
      lagrangianAction (ball (0 : ℝ^2) 1) determinantLagrangian (fun x ↦ x) := by
  apply (isNullLagrangianOn_determinant isOpen_ball).lagrangianAction_eq_of_eqOn_frontier
    isOpen_ball isBounded_ball
    (Boundary.Atlas.UnitBall.hasContDiffGraphBoundary 2 2)
    (ContinuousSecondJetOn.ofContDiff contDiff_determinantLagrangian _)
  · intro k
    exact ContDiffUpToBoundary.of_contDiff
      ((EuclideanSpace.proj k : ℝ^2 →L[ℝ] ℝ).contDiff.comp contDiff_diskDeformation)
      isBounded_ball
  · intro k
    exact ContDiffUpToBoundary.of_contDiff
      (EuclideanSpace.proj k : ℝ^2 →L[ℝ] ℝ).contDiff isBounded_ball
  · exact contDiff_diskDeformation.continuous.continuousOn
  · exact continuous_id.continuousOn
  · exact diskDeformation_eq_on_frontier

/-- The nonconstant polynomial determinant has the same disk integral as `1`. -/
theorem integral_polynomial_det_eq_integral_one :
    (∫ x in ball (0 : ℝ^2) 1, 3 * x 0 ^ 2 + x 1 ^ 2) =
      ∫ _x in ball (0 : ℝ^2) 1, (1 : ℝ) := by
  simpa only [lagrangianAction, determinantLagrangian,
    det_jacobianMatrix_diskDeformation, jacobianMatrix_id, Matrix.det_one] using
    diskDeformation_action_eq_identity

end PDE.Examples.NullBoundary
