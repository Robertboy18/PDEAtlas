/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.WeightedCalculus.Linearization

/-!
# Variation of the linearized coefficients

Changing a base path of weight `η` costs that weight in the linearized operator.
A Lipschitz derivative gives a quantitative bound from any variation weight
`α` to `α + η`.
-/

@[expose] public noncomputable section

open NNReal

namespace BoundedContinuousFunction

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {L M : ℝ≥0} {N : E → F}

/-- A change in the base path costs its exponential weight in the pointwise
derivative. The estimate is uniform over all represented variations. -/
theorem norm_increaseExponentialWeight_linearized_sub_le
    {η : ℝ} (hη : 0 ≤ η) (α : ℝ)
    (hN : LipschitzWith L N) (hN1 : ContDiff ℝ 1 N)
    (hDN : LipschitzWith M (fderiv ℝ N)) (u v : ℝ →ᵇ E) :
    ‖(increaseExponentialWeight (by linarith : α ≤ α + η)).comp
      (linearizedExponentialComposition hN hN1 η v -
        linearizedExponentialComposition hN hN1 η u)‖ ≤ M * ‖v - u‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg M.coe_nonneg (norm_nonneg _))
  intro w
  apply norm_le_of_norm_exponentialLift_le (α + η) _
    (mul_nonneg (mul_nonneg M.coe_nonneg (norm_nonneg _)) (norm_nonneg w))
  intro t
  simp only [ContinuousLinearMap.comp_apply, _root_.sub_apply,
    exponentialLift_increaseExponentialWeight, exponentialLift_sub,
    exponentialLift_linearizedExponentialComposition]
  have hd : ‖fderiv ℝ N (exponentialLift η v t) -
      fderiv ℝ N (exponentialLift η u t)‖ ≤
      M * ‖exponentialLift η (v - u) t‖ := by
    simpa only [dist_eq_norm, exponentialLift_sub] using
      hDN.dist_le_mul (exponentialLift η v t) (exponentialLift η u t)
  calc
    ‖fderiv ℝ N (exponentialLift η v t) (exponentialLift α w t) -
        fderiv ℝ N (exponentialLift η u t) (exponentialLift α w t)‖ =
      ‖(fderiv ℝ N (exponentialLift η v t) -
        fderiv ℝ N (exponentialLift η u t)) (exponentialLift α w t)‖ := rfl
    _ ≤ (M * ‖exponentialLift η (v - u) t‖) * ‖exponentialLift α w t‖ :=
      ContinuousLinearMap.le_of_opNorm_le_of_le _ hd le_rfl
    _ ≤ (M * (Real.exp (η * |t|) * ‖v - u‖)) *
        (Real.exp (α * |t|) * ‖w‖) := by
      gcongr
      · exact norm_exponentialLift_le η (v - u) t
      · exact norm_exponentialLift_le α w t
    _ = Real.exp ((α + η) * |t|) * (M * ‖v - u‖ * ‖w‖) := by
      rw [add_mul, Real.exp_add]
      ring

end BoundedContinuousFunction
