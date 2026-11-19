/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Power growth after continuous linear maps

Separate power bounds on two linear coordinates give a power bound in the ambient norm.
This also transports growth estimates between finite-dimensional norm conventions.
-/

@[expose] public section

namespace ContinuousLinearMap

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Two coordinate powers are bounded by one ambient power, with an explicit constant. -/
theorem mul_add_norm_rpow_le (S : E →L[ℝ] F) (T : E →L[ℝ] G)
    {r C : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C) (z : E) :
    C * (‖S z‖ ^ r + ‖T z‖ ^ r + 1) ≤
      C + (C * (‖S‖ ^ r + ‖T‖ ^ r)) * ‖z‖ ^ r := by
  have hS := Real.rpow_le_rpow (norm_nonneg (S z)) (S.le_opNorm z) hr
  have hT := Real.rpow_le_rpow (norm_nonneg (T z)) (T.le_opNorm z) hr
  rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)] at hS hT
  calc
    _ ≤ C * ((‖S‖ ^ r * ‖z‖ ^ r + ‖T‖ ^ r * ‖z‖ ^ r) + 1) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add hS hT) le_rfl) hC
    _ = _ := by rw [← add_mul, mul_add, mul_one, add_comm, mul_assoc]

end ContinuousLinearMap
