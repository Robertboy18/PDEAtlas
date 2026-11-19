/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.WeightedCalculus.Linearization
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# The Hessian along a weighted path

The derivative of the derivative acts pointwise on two variations. Their
exponential weights add, while the uniform Hessian bound is independent of the
base path. This is a bounded bilinear operator.
-/

@[expose] public noncomputable section

open NNReal

namespace BoundedContinuousFunction

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : ℝ≥0} {N : E → F}

/-- The Hessian along the base path, applied to two represented
variations. The output represents the sum of their weights. -/
def secondExponentialComposition
    (hDN : LipschitzWith M (fderiv ℝ N)) (hN2 : ContDiff ℝ 2 N)
    (η : ℝ) (u : ℝ →ᵇ E) :
    (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ F) :=
  ((ContinuousLinearMap.id ℝ (E →L[ℝ] F)).compLeftContinuousBounded₂ ℝ).comp
    (linearizedExponentialComposition hDN (hN2.fderiv_right (by norm_num)) η u)

/-- Both arguments are acted on by the second Fréchet derivative. -/
@[simp] theorem secondExponentialComposition_apply
    (hDN : LipschitzWith M (fderiv ℝ N)) (hN2 : ContDiff ℝ 2 N)
    (η : ℝ) (u v w : ℝ →ᵇ E) (t : ℝ) :
    secondExponentialComposition hDN hN2 η u v w t =
      fderiv ℝ (fderiv ℝ N) (exponentialLift η u t) (v t) (w t) := rfl

/-- The Hessian takes variations of weights `α` and `β` to weight
`α + β`. -/
@[simp] theorem exponentialLift_secondExponentialComposition
    (hDN : LipschitzWith M (fderiv ℝ N)) (hN2 : ContDiff ℝ 2 N)
    (η α β : ℝ) (u v w : ℝ →ᵇ E) (t : ℝ) :
    exponentialLift (α + β) (secondExponentialComposition hDN hN2 η u v w) t =
      fderiv ℝ (fderiv ℝ N) (exponentialLift η u t)
        (exponentialLift α v t) (exponentialLift β w t) := by
  change Real.exp ((α + β) * |t|) •
    fderiv ℝ (fderiv ℝ N) (exponentialLift η u t) (v t) (w t) =
      fderiv ℝ (fderiv ℝ N) (exponentialLift η u t)
        (Real.exp (α * |t|) • v t) (Real.exp (β * |t|) • w t)
  simp only [map_smul, _root_.smul_apply, smul_smul,
    add_mul, Real.exp_add]
  rw [mul_comm]

/-- The bilinear operator norm is bounded by the original Hessian bound. -/
theorem norm_secondExponentialComposition_le
    (hDN : LipschitzWith M (fderiv ℝ N)) (hN2 : ContDiff ℝ 2 N)
    (η : ℝ) (u : ℝ →ᵇ E) :
    ‖secondExponentialComposition hDN hN2 η u‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ M.coe_nonneg
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg M.coe_nonneg (norm_nonneg v))
  intro w
  apply (norm_le (mul_nonneg (mul_nonneg M.coe_nonneg (norm_nonneg v))
    (norm_nonneg w))).mpr
  intro t
  exact (fderiv ℝ (fderiv ℝ N) (exponentialLift η u t)).le_of_opNorm₂_le_of_le
    (norm_fderiv_le_of_lipschitz ℝ hDN) (v.norm_coe_le_norm t) (w.norm_coe_le_norm t)

/-- Increasing the second variation weight commutes with the Hessian,
with the corresponding increase in the sum weight. -/
theorem increaseExponentialWeight_secondExponentialComposition
    (hDN : LipschitzWith M (fderiv ℝ N)) (hN2 : ContDiff ℝ 2 N)
    (η α : ℝ) {β γ : ℝ} (hβγ : β ≤ γ) (u v w : ℝ →ᵇ E) :
    increaseExponentialWeight (by linarith : α + β ≤ α + γ)
      (secondExponentialComposition hDN hN2 η u v w) =
        secondExponentialComposition hDN hN2 η u v (increaseExponentialWeight hβγ w) := by
  apply exponentialLift_injective (α + γ)
  ext t
  simp only [exponentialLift_increaseExponentialWeight,
    exponentialLift_secondExponentialComposition]

/-- Increasing the first variation weight makes the same change to the
sum weight. No symmetry of the bilinear derivative is needed. -/
theorem increaseExponentialWeight_secondExponentialComposition_left
    (hDN : LipschitzWith M (fderiv ℝ N)) (hN2 : ContDiff ℝ 2 N)
    (η β : ℝ) {α γ : ℝ} (hαγ : α ≤ γ) (u v w : ℝ →ᵇ E) :
    increaseExponentialWeight (by linarith : α + β ≤ γ + β)
      (secondExponentialComposition hDN hN2 η u v w) =
        secondExponentialComposition hDN hN2 η u (increaseExponentialWeight hαγ v) w := by
  apply exponentialLift_injective (γ + β)
  ext t
  simp only [exponentialLift_increaseExponentialWeight,
    exponentialLift_secondExponentialComposition]

end BoundedContinuousFunction
