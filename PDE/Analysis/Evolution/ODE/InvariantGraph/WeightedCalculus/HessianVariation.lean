/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.WeightedCalculus.Hessian

/-!
# Variation of the Hessian along weighted paths

A Lipschitz Hessian costs one base-path weight when its two represented
variations are held fixed. The output weight is the sum of all three input
weights.
-/

@[expose] public noncomputable section

open NNReal

namespace BoundedContinuousFunction

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M K : ℝ≥0} {N : E → F}

/-- The change of the Hessian has one factor for the base-path
displacement and one for each variation. -/
theorem norm_increaseExponentialWeight_second_sub_le
    {η : ℝ} (hη : 0 ≤ η) (α β : ℝ)
    (hN2 : ContDiff ℝ 2 N) (hDN : LipschitzWith M (fderiv ℝ N))
    (hDDN : LipschitzWith K (fderiv ℝ (fderiv ℝ N))) (u v a b : ℝ →ᵇ E) :
    ‖increaseExponentialWeight (by linarith : α + β ≤ η + α + β)
      (secondExponentialComposition hDN hN2 η v a b -
        secondExponentialComposition hDN hN2 η u a b)‖ ≤
      K * ‖v - u‖ * ‖a‖ * ‖b‖ := by
  apply norm_le_of_norm_exponentialLift_le (η + α + β) _
    (by positivity : 0 ≤ K * ‖v - u‖ * ‖a‖ * ‖b‖)
  intro t
  simp only [exponentialLift_increaseExponentialWeight, exponentialLift_sub,
    exponentialLift_secondExponentialComposition]
  have hd : ‖fderiv ℝ (fderiv ℝ N) (exponentialLift η v t) -
      fderiv ℝ (fderiv ℝ N) (exponentialLift η u t)‖ ≤
      K * ‖exponentialLift η (v - u) t‖ := by
    simpa only [dist_eq_norm, exponentialLift_sub] using
      hDDN.dist_le_mul (exponentialLift η v t) (exponentialLift η u t)
  calc
    ‖fderiv ℝ (fderiv ℝ N) (exponentialLift η v t)
          (exponentialLift α a t) (exponentialLift β b t) -
        fderiv ℝ (fderiv ℝ N) (exponentialLift η u t)
          (exponentialLift α a t) (exponentialLift β b t)‖ ≤
      (K * ‖exponentialLift η (v - u) t‖) *
        ‖exponentialLift α a t‖ * ‖exponentialLift β b t‖ :=
      ContinuousLinearMap.le_of_opNorm₂_le_of_le _ hd le_rfl le_rfl
    _ ≤ (K * (Real.exp (η * |t|) * ‖v - u‖)) *
        (Real.exp (α * |t|) * ‖a‖) * (Real.exp (β * |t|) * ‖b‖) := by
      gcongr
      · exact norm_exponentialLift_le η (v - u) t
      · exact norm_exponentialLift_le α a t
      · exact norm_exponentialLift_le β b t
    _ = Real.exp ((η + α + β) * |t|) * (K * ‖v - u‖ * ‖a‖ * ‖b‖) := by
      rw [add_mul, add_mul, Real.exp_add, Real.exp_add]
      ring

end BoundedContinuousFunction
