/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Inverse estimates from strong monotonicity

A positive lower bound for the pairing of two increments bounds the input increment by the
output increment. For a family of operators, the same estimate separates the change in the
output from the change in the parameter. The operator need not be invertible.
-/

@[expose] public section

namespace PDE.Analysis.Operator

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Strong monotonicity at a pair gives an inverse estimate at that pair. -/
theorem mul_norm_sub_le_norm_sub_of_pairing_lower_bound
    {A : E → E} {m : ℝ} {x y : E}
    (hmono : m * ‖x - y‖ * ‖x - y‖ ≤ ⟪A x - A y, x - y⟫) :
    m * ‖x - y‖ ≤ ‖A x - A y‖ := by
  by_cases hxy : x = y
  · simp [hxy]
  have hnorm : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  exact (mul_le_mul_iff_of_pos_right hnorm).mp
    (hmono.trans (real_inner_le_norm _ _))

/-- The inverse estimate for a family splits variation in the output and in the parameter.
The parameter can contain both a spatial point and already controlled components of a jet. -/
theorem mul_norm_sub_le_output_add_parameter
    {P : Type*} (A : P → E → E) {m : ℝ} {p q : P} {x y : E}
    (hmono : m * ‖x - y‖ * ‖x - y‖ ≤ ⟪A p x - A p y, x - y⟫) :
    m * ‖x - y‖ ≤ ‖A p x - A q y‖ + ‖A q y - A p y‖ :=
  (mul_norm_sub_le_norm_sub_of_pairing_lower_bound hmono).trans
    (norm_sub_le_norm_sub_add_norm_sub (A p x) (A q y) (A p y))

end PDE.Analysis.Operator
