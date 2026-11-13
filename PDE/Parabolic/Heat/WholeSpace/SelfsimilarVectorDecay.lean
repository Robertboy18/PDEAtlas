/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.SelfsimilarVector
public import PDE.Parabolic.Heat.WholeSpace.SelfsimilarDecaySmoothing
public import PDE.Analysis.Normed.PiLp.Coordinatewise

/-!
# Free decay and smoothing on vector fields

Finite ℓ² sums transfer the scalar estimates without changing their constants.
-/

@[expose] public noncomputable section

open SobolevSpace SobolevSpace.GraphSpace
open scoped NNReal Sobolev

namespace HeatEquation.WholeSpace

variable {n k : ℕ}

/-- The actual vector free semigroup has the dimension-dependent decay rate. -/
theorem norm_vectorSelfsimilarHeat_le (τ : ℝ≥0) (u : VectorH n k) :
    ‖vectorSelfsimilarHeat n k τ u‖ ≤
      selfsimilarGraphConstant n k * Real.exp (((2 : ℝ) - n) * τ / 4) * ‖u‖ := by
  apply PiLp.norm_le_mul_of_norm_apply_le _ u
    (mul_nonneg (selfsimilarGraphConstant_nonneg n k) (Real.exp_pos _).le)
  intro j
  rw [vectorSelfsimilarHeat_apply]
  exact norm_selfsimilarHeatSobolev_le τ (u j)

/-- From dimension two on, free self-similar evolution is uniformly bounded. -/
theorem norm_vectorSelfsimilarHeat_le_of_two_le (hn : 2 ≤ n) (τ : ℝ≥0) (u : VectorH n k) :
    ‖vectorSelfsimilarHeat n k τ u‖ ≤ selfsimilarGraphConstant n k * ‖u‖ := by
  have hexp : Real.exp (((2 : ℝ) - n) * τ / 4) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hτ := τ.coe_nonneg
    nlinarith
  calc
    _ ≤ _ := norm_vectorSelfsimilarHeat_le τ u
    _ ≤ selfsimilarGraphConstant n k * 1 * ‖u‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp (selfsimilarGraphConstant_nonneg n k)) (norm_nonneg u)
    _ = _ := by ring

/-- Vector one-derivative gain combines free decay with the short-time singularity. -/
theorem norm_vectorSelfsimilarHeatGain_le_exp (τ : ℝ≥0) (hτ : 0 < τ)
    (u : VectorH n k) :
    ‖vectorSelfsimilarHeatGain n k τ hτ u‖ ≤
      selfsimilarSmoothingConstant n k * Real.exp (((2 : ℝ) - n) * τ / 4) *
        (1 + (Real.sqrt (τ : ℝ))⁻¹) * ‖u‖ := by
  apply PiLp.norm_le_mul_of_norm_apply_le _ u
    (mul_nonneg
      (mul_nonneg (selfsimilarSmoothingConstant_nonneg n k) (Real.exp_pos _).le)
      (by positivity))
  intro j
  rw [vectorSelfsimilarHeatGain_apply]
  exact norm_selfsimilarHeatGain_le_exp τ hτ (u j)

end HeatEquation.WholeSpace
