/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.WeightedCalculus.Hessian
import PDE.Analysis.Calculus.SecondDifference

/-!
# Taylor remainder of the linearized coefficients

Taylor expansion of the first derivative has a quadratic remainder in
the base displacement. Applying it to a variation of weight `α` therefore
requires output weight `α + 2η`. The estimate uses the mean-value
remainder theorem for the operator-valued first derivative.
-/

@[expose] public noncomputable section

open NNReal Set

namespace BoundedContinuousFunction

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {L M K : ℝ≥0} {N : E → F}

/-- A Lipschitz Hessian bounds the Taylor remainder of the coefficient
operator from weight `α` to weight `α + 2η`. -/
theorem norm_increaseExponentialWeight_linearized_remainder_le
    {η : ℝ} (hη : 0 ≤ η) (α : ℝ)
    (hN : LipschitzWith L N) (hN3 : ContDiff ℝ 3 N)
    (hDN : LipschitzWith M (fderiv ℝ N))
    (hDDN : LipschitzWith K (fderiv ℝ (fderiv ℝ N))) (u v : ℝ →ᵇ E) :
    ‖(increaseExponentialWeight (by linarith : α ≤ α + 2 * η)).comp
        (linearizedExponentialComposition hN (hN3.of_le (by norm_num)) η v -
          linearizedExponentialComposition hN (hN3.of_le (by norm_num)) η u) -
      (increaseExponentialWeight (by linarith : η + α ≤ α + 2 * η)).comp
        (secondExponentialComposition hDN (hN3.of_le (by norm_num)) η u (v - u))‖ ≤
      K * ‖v - u‖ ^ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg K.coe_nonneg (sq_nonneg _))
  intro w
  apply norm_le_of_norm_exponentialLift_le (α + 2 * η) _
    (mul_nonneg (mul_nonneg K.coe_nonneg (sq_nonneg _)) (norm_nonneg w))
  intro t
  simp only [ContinuousLinearMap.comp_apply, _root_.sub_apply,
    exponentialLift_sub, exponentialLift_increaseExponentialWeight,
    exponentialLift_linearizedExponentialComposition,
    exponentialLift_secondExponentialComposition]
  have hDN2 : ContDiff ℝ 2 (fderiv ℝ N) := hN3.fderiv_right (by norm_num)
  have hDDN1 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ N)) := hDN2.fderiv_right (by norm_num)
  have hr : ‖fderiv ℝ N (exponentialLift η v t) - fderiv ℝ N (exponentialLift η u t) -
      fderiv ℝ (fderiv ℝ N) (exponentialLift η u t)
        (exponentialLift η v t - exponentialLift η u t)‖ ≤
      K * ‖exponentialLift η (v - u) t‖ ^ 2 := by
    simpa only [exponentialLift_sub] using
      PDE.Analysis.norm_sub_sub_fderiv_le_of_hessian_bound K.coe_nonneg convex_univ
        (hDN2.differentiable (by norm_num)) hDDN1.differentiable_one
        (fun _ _ ↦ norm_fderiv_le_of_lipschitz ℝ hDDN) (mem_univ (exponentialLift η u t))
        (mem_univ (exponentialLift η v t))
  calc
    ‖fderiv ℝ N (exponentialLift η v t) (exponentialLift α w t) -
        fderiv ℝ N (exponentialLift η u t) (exponentialLift α w t) -
        fderiv ℝ (fderiv ℝ N) (exponentialLift η u t)
          (exponentialLift η v t - exponentialLift η u t) (exponentialLift α w t)‖ ≤
      (K * ‖exponentialLift η (v - u) t‖ ^ 2) * ‖exponentialLift α w t‖ :=
      ContinuousLinearMap.le_of_opNorm_le_of_le _ hr le_rfl
    _ ≤ (K * (Real.exp (η * |t|) * ‖v - u‖) ^ 2) *
        (Real.exp (α * |t|) * ‖w‖) := by
      gcongr
      · exact norm_exponentialLift_le η (v - u) t
      · exact norm_exponentialLift_le α w t
    _ = Real.exp ((α + 2 * η) * |t|) * (K * ‖v - u‖ ^ 2 * ‖w‖) := by
      rw [mul_pow, ← Real.exp_nat_mul, Nat.cast_ofNat,
        show 2 * (η * |t|) = 2 * η * |t| by ring, add_mul, Real.exp_add]
      ring

end BoundedContinuousFunction
