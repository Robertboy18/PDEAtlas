/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.WeightedCalculus.Linearization
public import PDE.Analysis.Evolution.ODE.InvariantGraph.WeightedComposition
public import PDE.Analysis.Calculus.Implicit.QuadraticResidual
import PDE.Analysis.Calculus.SecondDifference

/-!
# Differentiability of composition into a larger weight

The Hessian estimate gives a quadratic pointwise Taylor remainder.
Its weighted norm is quadratic only after doubling the input weight. This
gives the Fréchet derivative of composition as a map into that larger space.
-/

@[expose] public noncomputable section

open NNReal Set

namespace BoundedContinuousFunction

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {L : ℝ≥0} {N : E → F} {η : ℝ}

/-- A bounded Hessian gives a quadratic composition remainder in the
doubled exponential weight. -/
theorem norm_weighted_composition_remainder_le (hη : 0 ≤ η)
    (hN : LipschitzWith L N) (hN0 : N 0 = 0) (hN2 : ContDiff ℝ 2 N)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x, ‖fderiv ℝ (fderiv ℝ N) x‖ ≤ M)
    (u v : ℝ →ᵇ E) :
    ‖increaseExponentialWeight (by linarith : η ≤ 2 * η)
      (composeExponentialWeight hN hN0 η v - composeExponentialWeight hN hN0 η u -
        linearizedExponentialComposition hN (hN2.of_le (by norm_num)) η u (v - u))‖ ≤
      M * ‖v - u‖ ^ 2 := by
  apply norm_le_of_quadratic_exponentialLift_bound η (v - u) _ hM
  intro t
  simp only [exponentialLift_increaseExponentialWeight, exponentialLift_sub,
    exponentialLift_composeExponentialWeight, exponentialLift_linearizedExponentialComposition]
  have hdf : Differentiable ℝ (fderiv ℝ N) :=
    (hN2.fderiv_right (by norm_num) : ContDiff ℝ 1 (fderiv ℝ N)).differentiable_one
  exact PDE.Analysis.norm_sub_sub_fderiv_le_of_hessian_bound hM convex_univ
    (hN2.differentiable (by norm_num)) hdf (fun x _ ↦ hbound x) (mem_univ _) (mem_univ _)

/-- Nonlinear composition is differentiable from weight `η` to
weight `2η`, with the pointwise derivative. -/
theorem hasFDerivAt_increaseExponentialWeight_compose (hη : 0 ≤ η)
    (hN : LipschitzWith L N) (hN0 : N 0 = 0) (hN2 : ContDiff ℝ 2 N)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x, ‖fderiv ℝ (fderiv ℝ N) x‖ ≤ M)
    (u : ℝ →ᵇ E) :
    HasFDerivAt
      (fun v ↦ increaseExponentialWeight (by linarith : η ≤ 2 * η)
        (composeExponentialWeight hN hN0 η v))
      ((increaseExponentialWeight (by linarith : η ≤ 2 * η)).comp
        (linearizedExponentialComposition hN (hN2.of_le (by norm_num)) η u)) u := by
  let J : (ℝ →ᵇ F) →L[ℝ] (ℝ →ᵇ F) := increaseExponentialWeight (by linarith : η ≤ 2 * η)
  let D := linearizedExponentialComposition hN (hN2.of_le (by norm_num)) η u
  have h := PDE.hasFDerivAt_of_quadratic_linear_residual
    (fun v ↦ J (composeExponentialWeight hN hN0 η v)) u
    (ContinuousLinearEquiv.refl ℝ (ℝ →ᵇ F)) (J.comp D) M (by
      intro v
      simpa only [ContinuousLinearEquiv.refl_apply, ContinuousLinearMap.comp_apply,
        ← map_sub] using norm_weighted_composition_remainder_le hη hN hN0 hN2 hM hbound u v)
  simpa only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
    ContinuousLinearMap.id_comp] using h

end BoundedContinuousFunction
