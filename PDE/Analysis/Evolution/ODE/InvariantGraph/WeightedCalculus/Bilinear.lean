/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.WeightedCalculus.Norms
public import PDE.Analysis.Normed.ContinuousMap.Bounded.Bilinear

/-!
# Bilinear products add exponential weights

Pointwise bilinear operations on bounded representatives encode the
bilinear operation on paths with output weight equal to the sum of the input weights.
The operator itself is the generic bounded-function bilinear map.
-/

@[expose] public noncomputable section

namespace BoundedContinuousFunction

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The product of paths of rates `η` and `θ` has rate `η + θ`. -/
@[simp] theorem exponentialLift_compLeftContinuousBounded₂
    (B : E →L[ℝ] F →L[ℝ] G) (η θ : ℝ) (u : ℝ →ᵇ E) (v : ℝ →ᵇ F) (t : ℝ) :
    exponentialLift (η + θ) (B.compLeftContinuousBounded₂ ℝ u v) t =
      B (exponentialLift η u t) (exponentialLift θ v t) := by
  change Real.exp ((η + θ) * |t|) • B (u t) (v t) =
    B (Real.exp (η * |t|) • u t) (Real.exp (θ * |t|) • v t)
  rw [B.map_smul, _root_.smul_apply, (B (u t)).map_smul, smul_smul,
    add_mul, Real.exp_add]

/-- The product estimate uses only the original bilinear operator norm. -/
theorem norm_compLeftContinuousBounded₂_le
    (B : E →L[ℝ] F →L[ℝ] G) (u : ℝ →ᵇ E) (v : ℝ →ᵇ F) :
    ‖B.compLeftContinuousBounded₂ ℝ u v‖ ≤ ‖B‖ * ‖u‖ * ‖v‖ :=
  (B.compLeftContinuousBounded₂ ℝ).le_of_opNorm₂_le_of_le
    (B.norm_compLeftContinuousBounded₂_le ℝ) le_rfl le_rfl

/-- A quadratic pointwise remainder has twice the input exponential weight. -/
theorem norm_le_of_quadratic_exponentialLift_bound
    (η : ℝ) (u : ℝ →ᵇ E) (r : ℝ →ᵇ F) {C : ℝ} (hC : 0 ≤ C)
    (hr : ∀ t, ‖exponentialLift (2 * η) r t‖ ≤ C * ‖exponentialLift η u t‖ ^ 2) :
    ‖r‖ ≤ C * ‖u‖ ^ 2 := by
  apply norm_le_of_norm_exponentialLift_le (2 * η) r (mul_nonneg hC (sq_nonneg _))
  intro t
  calc
    ‖exponentialLift (2 * η) r t‖ ≤ C * ‖exponentialLift η u t‖ ^ 2 := hr t
    _ ≤ C * (Real.exp (η * |t|) * ‖u‖) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (norm_exponentialLift_le η u t) 2) hC
    _ = Real.exp (2 * η * |t|) * (C * ‖u‖ ^ 2) := by
      rw [mul_pow, ← Real.exp_nat_mul, Nat.cast_ofNat,
        show 2 * (η * |t|) = 2 * η * |t| by ring]
      ac_rfl

end BoundedContinuousFunction
