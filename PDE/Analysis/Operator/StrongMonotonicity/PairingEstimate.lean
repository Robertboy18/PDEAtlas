/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Operator.StrongMonotonicity.InverseEstimate

/-!
# Coercivity of a scaled flux increment

In a difference quotient the spatial parameter and the unknown change together.
Separating the parameter change leaves a coercive pairing and a norm product error.
The scalar multiplier may include a cutoff and a reciprocal step.
-/

@[expose] public section

namespace PDE.Analysis.Operator

open scoped RealInnerProductSpace

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A common scalar multiplier preserves coercivity, with the spatial increment isolated
as a product error. Neither parameter is assumed to depend differentiably on space. -/
theorem scaled_pairing_lower_bound_with_parameter_error
    (A : P → E → E) {p q : P} {m : ℝ}
    (hmono : ∀ x y, m * ‖x - y‖ * ‖x - y‖ ≤ ⟪A q x - A q y, x - y⟫)
    (x y : E) (c : ℝ) :
    m * ‖c • (y - x)‖ ^ 2 ≤
      ⟪c • (A q y - A p x), c • (y - x)⟫ +
        ‖c • (A q x - A p x)‖ * ‖c • (y - x)‖ := by
  have hs : m * ‖c • (y - x)‖ ^ 2 ≤
      ⟪c • (A q y - A q x), c • (y - x)⟫ := by
    have h := mul_le_mul_of_nonneg_left (hmono y x) (sq_nonneg c)
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    simpa only [
      real_inner_smul_left, real_inner_smul_right, pow_two,
      mul_assoc, mul_left_comm, mul_comm] using h
  have hd : c • (A q y - A q x) =
      c • (A q y - A p x) - c • (A q x - A p x) := by
    rw [← smul_sub, sub_sub_sub_cancel_right]
  rw [hd, inner_sub_left] at hs
  have he := neg_le_abs ⟪c • (A q x - A p x), c • (y - x)⟫
  have hn := abs_real_inner_le_norm (c • (A q x - A p x)) (c • (y - x))
  linarith

/-- The parameter error after a positive step is bounded independently of that step. -/
theorem norm_scaled_parameter_error_le
    (A : P → E → E) {p q : P} {K h : ℝ} (hh : 0 < h)
    (x : E) (η : ℝ)
    (hvariation : ‖A q x - A p x‖ ≤ K * h * ‖x‖) :
    ‖(η / h) • (A q x - A p x)‖ ≤ K * |η| * ‖x‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hh]
  calc
    |η| / h * ‖A q x - A p x‖ ≤ |η| / h * (K * h * ‖x‖) :=
      mul_le_mul_of_nonneg_left hvariation (div_nonneg (abs_nonneg _) hh.le)
    _ = _ := by field_simp

/-- Joint variation of the flux bounds its scaled quotient by the scaled unknown
quotient and a spatial error independent of the positive step. -/
theorem norm_scaled_flux_increment_le
    (A : P → E → E) {p q : P} {K C h : ℝ} (hh : 0 < h)
    (x y : E) (η : ℝ)
    (hvariation : ‖A q y - A p x‖ ≤ K * h * ‖x‖ + C * ‖y - x‖) :
    ‖(η / h) • (A q y - A p x)‖ ≤
      K * |η| * ‖x‖ + C * ‖(η / h) • (y - x)‖ := by
  simp only [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hh]
  calc
    |η| / h * ‖A q y - A p x‖ ≤
        |η| / h * (K * h * ‖x‖ + C * ‖y - x‖) :=
      mul_le_mul_of_nonneg_left hvariation (div_nonneg (abs_nonneg _) hh.le)
    _ = _ := by field_simp

end PDE.Analysis.Operator
