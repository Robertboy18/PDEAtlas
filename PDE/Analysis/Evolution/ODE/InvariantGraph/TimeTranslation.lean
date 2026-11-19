/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.WeightedPaths

/-!
# Time translation of exponentially weighted paths

Translation by `τ` preserves the space of paths of exponential rate `η`, with
operator norm at most `exp (η * |τ|)`. The bound is for each translation
separately.
-/

@[expose] public noncomputable section

namespace BoundedContinuousFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {η : ℝ}

/-- Translation preserves an exponential growth bound. -/
theorem norm_exponentialLift_add_time_le (hη : 0 ≤ η) (u : ℝ →ᵇ E) (τ t : ℝ) :
    ‖exponentialLift η u (t + τ)‖ ≤
      Real.exp (η * |t|) * (Real.exp (η * |τ|) * ‖u‖) := by
  calc
    ‖exponentialLift η u (t + τ)‖ ≤ Real.exp (η * |t + τ|) * ‖u‖ :=
      norm_exponentialLift_le η u (t + τ)
    _ ≤ Real.exp (η * (|t| + |τ|)) * ‖u‖ :=
      mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_add_le t τ) hη)) (norm_nonneg u)
    _ = Real.exp (η * |t|) * (Real.exp (η * |τ|) * ‖u‖) := by
      rw [mul_add, Real.exp_add, mul_assoc]

/-- Translate the represented path by a fixed time. -/
def translateWeightedPath (hη : 0 ≤ η) (τ : ℝ) :
    (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E) :=
  LinearMap.mkContinuous
    { toFun u := ofExponentialBound η
        ⟨fun t ↦ exponentialLift η u (t + τ), by fun_prop⟩
        (Real.exp (η * |τ|) * ‖u‖) (norm_exponentialLift_add_time_le hη u τ)
      map_add' u v := by
        ext t
        change Real.exp (-(η * |t|)) •
            (Real.exp (η * |t + τ|) • (u (t + τ) + v (t + τ))) = _
        simp only [smul_add]
        rfl
      map_smul' c u := by
        ext t
        change Real.exp (-(η * |t|)) •
            (Real.exp (η * |t + τ|) • (c • u (t + τ))) =
          c • (Real.exp (-(η * |t|)) • (Real.exp (η * |t + τ|) • u (t + τ)))
        rw [smul_comm (Real.exp (η * |t + τ|)) c,
          smul_comm (Real.exp (-(η * |t|))) c] }
    (Real.exp (η * |τ|)) fun u ↦
      norm_ofExponentialBound_le η
        ⟨fun t ↦ exponentialLift η u (t + τ), by fun_prop⟩
        (mul_nonneg (Real.exp_nonneg _) (norm_nonneg u))
        (norm_exponentialLift_add_time_le hη u τ)

/-- Decoding a translated path gives literal time translation. -/
@[simp] theorem exponentialLift_translateWeightedPath (hη : 0 ≤ η) (τ : ℝ)
    (u : ℝ →ᵇ E) (t : ℝ) :
    exponentialLift η (translateWeightedPath hη τ u) t = exponentialLift η u (t + τ) := by
  change Real.exp (η * |t|) • (Real.exp (-(η * |t|)) • exponentialLift η u (t + τ)) = _
  rw [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]

/-- The translation norm depends only on the time shift and exponential weight. -/
theorem norm_translateWeightedPath_le (hη : 0 ≤ η) (τ : ℝ) :
    ‖translateWeightedPath (E := E) hη τ‖ ≤ Real.exp (η * |τ|) :=
  LinearMap.mkContinuous_norm_le _ (Real.exp_nonneg _) _

end BoundedContinuousFunction
