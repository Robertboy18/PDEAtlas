/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.WeightedPaths

/-!
# Norm estimates for weighted paths

Decoding `u ↦ e^{η|t|} u(t)` is additive. A pointwise bound
`‖e^{η|t|} u(t)‖ ≤ e^{η|t|} C` gives `‖u‖ ≤ C`, so pointwise exponential estimates
for nonlinear remainders bound weighted norms directly. Increasing the weight is a
linear map of norm at most one.
-/

@[expose] public noncomputable section

namespace BoundedContinuousFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Decoding preserves addition of represented paths. -/
@[simp] theorem exponentialLift_add (η : ℝ) (u v : ℝ →ᵇ E) (t : ℝ) :
    exponentialLift η (u + v) t = exponentialLift η u t + exponentialLift η v t :=
  smul_add _ _ _

/-- Decoding preserves subtraction of represented paths. -/
@[simp] theorem exponentialLift_sub (η : ℝ) (u v : ℝ →ᵇ E) (t : ℝ) :
    exponentialLift η (u - v) t = exponentialLift η u t - exponentialLift η v t :=
  smul_sub _ _ _

/-- A pointwise exponential bound controls the norm of the representation. -/
theorem norm_le_of_norm_exponentialLift_le (η : ℝ) (u : ℝ →ᵇ E) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ t, ‖exponentialLift η u t‖ ≤ Real.exp (η * |t|) * C) :
    ‖u‖ ≤ C := by
  apply (norm_le hC).mpr
  intro t
  have ht := h t
  change ‖Real.exp (η * |t|) • u t‖ ≤ _ at ht
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at ht
  exact (mul_le_mul_iff_right₀ (Real.exp_pos _)).mp ht

/-- Increasing the exponential weight is a nonexpansive linear operator. -/
theorem norm_increaseExponentialWeight_le {η θ : ℝ} (hηθ : η ≤ θ) :
    ‖increaseExponentialWeight (E := E) hηθ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [one_mul]
  apply norm_le_of_norm_exponentialLift_le θ _ (norm_nonneg u)
  intro t
  simpa only [exponentialLift_increaseExponentialWeight] using
    norm_exponentialLift_le_of_weight_le hηθ u t

end BoundedContinuousFunction
