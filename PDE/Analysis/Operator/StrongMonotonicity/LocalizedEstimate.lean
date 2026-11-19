/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Operator.StrongMonotonicity.InverseEstimate

/-!
# Cutoffs in an inverse estimate

Multiplying the unknown and the output by a cutoff introduces two commutators. One
contains the output and the other contains the unknown itself. Both terms are needed
because a cutoff of a solution need not solve the original nonlinear equation.
-/

@[expose] public section

namespace PDE.Analysis.Operator

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Localize an increment estimate. The error created by unequal weights is explicit. -/
theorem mul_norm_smul_sub_le_of_inverse_estimate
    {m R : ℝ} (hm : 0 ≤ m) {x y : E} {v w : F}
    (hbound : m * ‖x - y‖ ≤ ‖v - w‖ + R) (a b : ℝ) :
    m * ‖a • x - b • y‖ ≤
      ‖a • v - b • w‖ + |a| * R + |a - b| * (‖w‖ + m * ‖y‖) := by
  have hu : a • x - b • y = a • (x - y) + (a - b) • y := by
    simp only [smul_sub, sub_smul]
    abel
  have hv : a • (v - w) = (a • v - b • w) - (a - b) • w := by
    simp only [smul_sub, sub_smul]
    abel
  have hq : |a| * ‖v - w‖ ≤ ‖a • v - b • w‖ + |a - b| * ‖w‖ := by
    calc
      |a| * ‖v - w‖ = ‖a • (v - w)‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖a • v - b • w‖ + ‖(a - b) • w‖ := by rw [hv]; exact norm_sub_le _ _
      _ = _ := by rw [norm_smul, Real.norm_eq_abs]
  calc
    m * ‖a • x - b • y‖ ≤ m * (|a| * ‖x - y‖ + |a - b| * ‖y‖) := by
      rw [hu]
      simpa only [norm_smul, Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_left (norm_add_le (a • (x - y)) ((a - b) • y)) hm
    _ = |a| * (m * ‖x - y‖) + m * |a - b| * ‖y‖ := by ring
    _ ≤ |a| * (‖v - w‖ + R) + m * |a - b| * ‖y‖ :=
      add_le_add (mul_le_mul_of_nonneg_left hbound (abs_nonneg a)) le_rfl
    _ ≤ ‖a • v - b • w‖ + |a| * R + |a - b| * (‖w‖ + m * ‖y‖) := by
      nlinarith

end PDE.Analysis.Operator
