/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Exponentially weighted paths on the whole time line

The weighted path space is represented by Mathlib's bounded continuous functions.
A bounded function `u` represents the path `exp(η * |t|) • u t`; completeness is
therefore the completeness of bounded continuous functions.

Increasing the weight gives a contraction between these representations. This
allows an integral equation and its first and second variations to use different
exponential weights without introducing another normed-space instance.
-/

@[expose] public noncomputable section

namespace BoundedContinuousFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Recover the continuous path represented in the exponential weight `η`. -/
def exponentialLift (η : ℝ) (u : ℝ →ᵇ E) : C(ℝ, E) where
  toFun t := Real.exp (η * |t|) • u t
  continuous_toFun := by fun_prop

/-- The weight equals one at the distinguished time zero. -/
@[simp] theorem exponentialLift_zero (η : ℝ) (u : ℝ →ᵇ E) :
    exponentialLift η u 0 = u 0 := by
  simp [exponentialLift]

/-- The norm of a represented path grows at most at its specified exponential rate. -/
theorem norm_exponentialLift_le (η : ℝ) (u : ℝ →ᵇ E) (t : ℝ) :
    ‖exponentialLift η u t‖ ≤ Real.exp (η * |t|) * ‖u‖ := by
  simpa [exponentialLift, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
    mul_le_mul_of_nonneg_left (u.norm_coe_le_norm t) (Real.exp_nonneg (η * |t|))

/-- A path with exponential rate `η` also satisfies every larger growth bound. -/
theorem norm_exponentialLift_le_of_weight_le {η θ : ℝ} (hηθ : η ≤ θ)
    (u : ℝ →ᵇ E) (t : ℝ) :
    ‖exponentialLift η u t‖ ≤ Real.exp (θ * |t|) * ‖u‖ :=
  (norm_exponentialLift_le η u t).trans
    (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hηθ (abs_nonneg t)))
      (norm_nonneg u))

/-- The representation of a continuous path at a fixed weight is unique. -/
theorem exponentialLift_injective (η : ℝ) :
    Function.Injective (exponentialLift η : (ℝ →ᵇ E) → C(ℝ, E)) := by
  intro u v h
  ext t
  have ht := congrArg (fun f : C(ℝ, E) ↦ f t) h
  exact (smul_right_injective E (Real.exp_ne_zero (η * |t|))) ht

/-- Encode a continuous path with a proved exponential growth bound. -/
def ofExponentialBound (η : ℝ) (f : C(ℝ, E)) (C : ℝ)
    (hbound : ∀ t, ‖f t‖ ≤ Real.exp (η * |t|) * C) : ℝ →ᵇ E :=
  ofNormedAddCommGroup (fun t ↦ Real.exp (-(η * |t|)) • f t) (by fun_prop) C fun t ↦ by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-(η * |t|)) * ‖f t‖ ≤
          Real.exp (-(η * |t|)) * (Real.exp (η * |t|) * C) :=
        mul_le_mul_of_nonneg_left (hbound t) (Real.exp_nonneg _)
      _ = C := by
        rw [Real.exp_neg, ← mul_assoc, inv_mul_cancel₀ (Real.exp_ne_zero _), one_mul]

/-- Decoding an exponentially bounded path recovers the original function exactly. -/
@[simp] theorem exponentialLift_ofExponentialBound
    (η : ℝ) (f : C(ℝ, E)) (C : ℝ)
    (hbound : ∀ t, ‖f t‖ ≤ Real.exp (η * |t|) * C) :
    exponentialLift η (ofExponentialBound η f C hbound) = f := by
  ext t
  change Real.exp (η * |t|) • (Real.exp (-(η * |t|)) • f t) = f t
  rw [smul_smul, Real.exp_neg, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]

/-- The norm of an encoded path is at most its proved growth constant. -/
theorem norm_ofExponentialBound_le (η : ℝ) (f : C(ℝ, E)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ t, ‖f t‖ ≤ Real.exp (η * |t|) * C) :
    ‖ofExponentialBound η f C hbound‖ ≤ C :=
  norm_ofNormedAddCommGroup_le _ hC _

/-- A larger exponential weight represents the same path with no larger norm. -/
def increaseExponentialWeight {η θ : ℝ} (hηθ : η ≤ θ) :
    (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E) :=
  LinearMap.mkContinuous
    { toFun u := ofExponentialBound θ (exponentialLift η u) ‖u‖
        (norm_exponentialLift_le_of_weight_le hηθ u)
      map_add' u v := by
        ext t
        change Real.exp (-(θ * |t|)) • (Real.exp (η * |t|) • (u t + v t)) = _
        simp only [smul_add]
        rfl
      map_smul' c u := by
        ext t
        change Real.exp (-(θ * |t|)) • (Real.exp (η * |t|) • (c • u t)) =
          c • (Real.exp (-(θ * |t|)) • (Real.exp (η * |t|) • u t))
        rw [smul_comm (Real.exp (η * |t|)) c, smul_comm (Real.exp (-(θ * |t|))) c] }
    1 fun u ↦ by
      change ‖ofExponentialBound θ (exponentialLift η u) ‖u‖
        (norm_exponentialLift_le_of_weight_le hηθ u)‖ ≤ 1 * ‖u‖
      rw [one_mul]
      exact norm_ofExponentialBound_le θ (exponentialLift η u) (norm_nonneg u)
        (norm_exponentialLift_le_of_weight_le hηθ u)

/-- Changing weights leaves the whole-line path unchanged. -/
@[simp] theorem exponentialLift_increaseExponentialWeight
    {η θ : ℝ} (hηθ : η ≤ θ) (u : ℝ →ᵇ E) :
    exponentialLift θ (increaseExponentialWeight hηθ u) = exponentialLift η u := by
  change exponentialLift θ (ofExponentialBound θ (exponentialLift η u) ‖u‖
    (norm_exponentialLift_le_of_weight_le hηθ u)) = _
  exact exponentialLift_ofExponentialBound θ (exponentialLift η u) ‖u‖
    (norm_exponentialLift_le_of_weight_le hηθ u)

end BoundedContinuousFunction
