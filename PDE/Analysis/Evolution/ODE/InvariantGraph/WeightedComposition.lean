/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.WeightedPaths

/-!
# Composition on exponentially weighted paths

A Lipschitz map fixing zero acts on represented paths with the same Lipschitz
constant. The input and output weights cancel in the distance estimate.
-/

@[expose] public noncomputable section

open NNReal

namespace BoundedContinuousFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] {L : ℝ≥0} {N : E → F}

/-- A Lipschitz map fixing zero preserves an exponential growth rate. -/
theorem norm_comp_exponentialLift_le (hN : LipschitzWith L N) (hN0 : N 0 = 0)
    (η : ℝ) (u : ℝ →ᵇ E) (t : ℝ) :
    ‖N (exponentialLift η u t)‖ ≤ Real.exp (η * |t|) * (L * ‖u‖) := by
  calc
    ‖N (exponentialLift η u t)‖ ≤ L * ‖exponentialLift η u t‖ := hN.norm_le_mul hN0 _
    _ ≤ L * (Real.exp (η * |t|) * ‖u‖) :=
      mul_le_mul_of_nonneg_left (norm_exponentialLift_le η u t) L.coe_nonneg
    _ = Real.exp (η * |t|) * (L * ‖u‖) := mul_left_comm _ _ _

variable [NormedSpace ℝ F]

/-- Compose a weighted path with a Lipschitz map fixing zero, then
represent the resulting path at the same weight. -/
def composeExponentialWeight (hN : LipschitzWith L N) (hN0 : N 0 = 0)
    (η : ℝ) (u : ℝ →ᵇ E) : ℝ →ᵇ F :=
  ofExponentialBound η
    ⟨fun t ↦ N (exponentialLift η u t), hN.continuous.comp (exponentialLift η u).continuous⟩
    (L * ‖u‖) (norm_comp_exponentialLift_le hN hN0 η u)

/-- Decoding the composition gives the composition of the paths. -/
@[simp] theorem exponentialLift_composeExponentialWeight
    (hN : LipschitzWith L N) (hN0 : N 0 = 0) (η : ℝ) (u : ℝ →ᵇ E) (t : ℝ) :
    exponentialLift η (composeExponentialWeight hN hN0 η u) t =
      N (exponentialLift η u t) := by
  unfold composeExponentialWeight
  rw [exponentialLift_ofExponentialBound]
  rfl

/-- Composition has the original Lipschitz constant in the weighted norm. -/
theorem lipschitzWith_composeExponentialWeight
    (hN : LipschitzWith L N) (hN0 : N 0 = 0) (η : ℝ) :
    LipschitzWith L (composeExponentialWeight hN hN0 η) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [dist_eq_norm, dist_eq_norm]
  apply (norm_le (mul_nonneg L.coe_nonneg (norm_nonneg (u - v)))).mpr
  intro t
  change ‖Real.exp (-(η * |t|)) • N (Real.exp (η * |t|) • u t) -
      Real.exp (-(η * |t|)) • N (Real.exp (η * |t|) • v t)‖ ≤ L * ‖u - v‖
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h := hN.dist_le_mul (Real.exp (η * |t|) • u t) (Real.exp (η * |t|) • v t)
  simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] at h
  calc
    Real.exp (-(η * |t|)) *
        ‖N (Real.exp (η * |t|) • u t) - N (Real.exp (η * |t|) • v t)‖ ≤
        Real.exp (-(η * |t|)) * (L * (Real.exp (η * |t|) * ‖u t - v t‖)) :=
      mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)
    _ = L * ‖u t - v t‖ := by
      rw [show Real.exp (-(η * |t|)) * (L * (Real.exp (η * |t|) * ‖u t - v t‖)) =
          (Real.exp (-(η * |t|)) * Real.exp (η * |t|)) * (L * ‖u t - v t‖) by ac_rfl]
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    _ ≤ L * ‖u - v‖ :=
      mul_le_mul_of_nonneg_left ((u - v).norm_coe_le_norm t) L.coe_nonneg

end BoundedContinuousFunction
