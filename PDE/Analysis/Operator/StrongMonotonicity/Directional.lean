/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Operator.StrongMonotonicity.InverseEstimate

/-!
# A scalar equation along a unit direction

Projecting a strongly monotone flux onto a unit direction gives a strongly monotone
scalar equation along that direction. The remaining vector enters only as a parameter.
-/

@[expose] public section

namespace PDE.Analysis.Operator

open scoped NNReal RealInnerProductSpace

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Evaluate a flux along a line and project its value onto the direction of that line. -/
noncomputable def directionalFlux (A : E → E) (e z : E) (t : ℝ) : ℝ :=
  ⟪A (z + t • e), e⟫

/-- Vector strong monotonicity gives the same scalar constant along a unit direction. -/
theorem directionalFlux_pairing_lower_bound
    (A : E → E) {m : ℝ}
    (hmono : ∀ x y, m * ‖x - y‖ * ‖x - y‖ ≤ ⟪A x - A y, x - y⟫)
    (e : E) (he : ‖e‖ = 1) (z : E) (s t : ℝ) :
    m * ‖s - t‖ * ‖s - t‖ ≤
      ⟪directionalFlux A e z s - directionalFlux A e z t, s - t⟫ := by
  have hd : (z + s • e) - (z + t • e) = (s - t) • e := by
    rw [add_sub_add_left_eq_sub, sub_smul]
  have h := hmono (z + s • e) (z + t • e)
  rw [hd, norm_smul, he, mul_one, real_inner_smul_right, inner_sub_left] at h
  simpa only [directionalFlux, Real.inner_apply, mul_comm (s - t)] using h

/-- Joint spatial and vector variation of a flux gives the corresponding parameter
bound for its scalar directional equation. -/
theorem directionalFlux_norm_sub_le
    [NormedAddCommGroup X]
    (A : X → E → E) (K C : ℝ≥0) {x y : X}
    (hvariation : ∀ z w : E,
      ‖A y w - A x z‖ ≤ K * ‖y - x‖ * ‖z‖ + C * ‖w - z‖)
    (e : E) (he : ‖e‖ = 1) (z w : E) (t : ℝ) :
    ‖directionalFlux (A y) e w t - directionalFlux (A x) e z t‖ ≤
      K * ‖y - x‖ * (‖t‖ + ‖z‖) + C * ‖w - z‖ := by
  have hz : ‖z + t • e‖ ≤ ‖t‖ + ‖z‖ := by
    simpa only [norm_smul, he, mul_one, add_comm] using norm_add_le z (t • e)
  calc
    _ = ‖⟪A y (w + t • e) - A x (z + t • e), e⟫‖ := by
      rw [inner_sub_left]
      rfl
    _ ≤ ‖A y (w + t • e) - A x (z + t • e)‖ * ‖e‖ := norm_inner_le_norm _ _
    _ = ‖A y (w + t • e) - A x (z + t • e)‖ := by rw [he, mul_one]
    _ ≤ K * ‖y - x‖ * ‖z + t • e‖ + C * ‖(w + t • e) - (z + t • e)‖ :=
      hvariation _ _
    _ ≤ K * ‖y - x‖ * (‖t‖ + ‖z‖) + C * ‖w - z‖ := by
      rw [add_sub_add_right_eq_sub]
      exact add_le_add (mul_le_mul_of_nonneg_left hz (by positivity)) le_rfl

end PDE.Analysis.Operator
