/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Pullback of a monotone flux

A linear change of gradient variables transforms a flux `A` into `J • T† ∘ A ∘ T`.
The pairing identity preserves strong monotonicity when `J` is positive and `T` is
bounded below. The Lipschitz estimate uses the same map and its adjoint.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Operator

open scoped NNReal RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The flux associated with a linear pullback of the gradient and a scalar volume factor. -/
def pullbackFlux (A : E → E) (T : F →L[ℝ] E) (J : ℝ) (x : F) : F :=
  J • T.adjoint (A (T x))

/-- The adjoint gives the exact transformed increment pairing. -/
theorem pullbackFlux_pairing_sub (A : E → E) (T : F →L[ℝ] E) (J : ℝ) (x y : F) :
    ⟪pullbackFlux A T J x - pullbackFlux A T J y, x - y⟫ =
      J * ⟪A (T x) - A (T y), T x - T y⟫ := by
  simp only [pullbackFlux, ← smul_sub, ← map_sub, real_inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left]

/-- A lower bound for the linear map transfers the monotonicity constant of the flux. -/
theorem pullbackFlux_pairing_lower_bound
    (A : E → E) {m : ℝ} (hm : 0 ≤ m)
    (hmono : ∀ x y, m * ‖x - y‖ * ‖x - y‖ ≤ ⟪A x - A y, x - y⟫)
    (T : F →L[ℝ] E) {c : ℝ} (hc : 0 ≤ c)
    (hT : ∀ x, c * ‖x‖ ≤ ‖T x‖) {J : ℝ} (hJ : 0 ≤ J) (x y : F) :
    (J * m * c ^ 2) * ‖x - y‖ * ‖x - y‖ ≤
      ⟪pullbackFlux A T J x - pullbackFlux A T J y, x - y⟫ := by
  rw [pullbackFlux_pairing_sub]
  have hnorm : c * ‖x - y‖ ≤ ‖T x - T y‖ := by simpa only [map_sub] using hT (x - y)
  have hsq : c ^ 2 * ‖x - y‖ ^ 2 ≤ ‖T x - T y‖ ^ 2 := by
    have hnonneg := mul_nonneg hc (norm_nonneg (x - y))
    nlinarith
  calc
    (J * m * c ^ 2) * ‖x - y‖ * ‖x - y‖ = J * (m * (c ^ 2 * ‖x - y‖ ^ 2)) := by ring
    _ ≤ J * (m * ‖T x - T y‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hm) hJ
    _ ≤ J * ⟪A (T x) - A (T y), T x - T y⟫ :=
      mul_le_mul_of_nonneg_left (by simpa only [pow_two, mul_assoc] using hmono (T x) (T y)) hJ

/-- A linear pullback has Lipschitz constant `|J| ‖T‖²` times that of the original flux. -/
theorem lipschitzWith_pullbackFlux
    (A : E → E) {C : ℝ≥0} (hA : LipschitzWith C A) (T : F →L[ℝ] E) (J : ℝ) :
    LipschitzWith (‖J‖₊ * ‖T‖₊ ^ 2 * C) (pullbackFlux A T J) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, pullbackFlux, ← smul_sub, ← map_sub, norm_smul,
    NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm]
  calc
    ‖J‖ * ‖T.adjoint (A (T x) - A (T y))‖ ≤
        ‖J‖ * (‖T‖ * ‖A (T x) - A (T y)‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg J)
      simpa only [LinearIsometryEquiv.norm_map] using T.adjoint.le_opNorm (A (T x) - A (T y))
    _ ≤ ‖J‖ * (‖T‖ * (C * ‖T (x - y)‖)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg J)
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg T)
      simpa only [dist_eq_norm, map_sub] using hA.dist_le_mul (T x) (T y)
    _ ≤ ‖J‖ * (‖T‖ * (C * (‖T‖ * ‖x - y‖))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (T.le_opNorm (x - y)) C.coe_nonneg) (norm_nonneg T))
        (norm_nonneg J)
    _ = _ := by ring

/-- A centered flux remains centered after pullback. -/
@[simp]
theorem pullbackFlux_zero (A : E → E) (hA : A 0 = 0) (T : F →L[ℝ] E) (J : ℝ) :
    pullbackFlux A T J 0 = 0 := by
  simp only [pullbackFlux, map_zero, hA, smul_zero]

end PDE.Analysis.Operator
