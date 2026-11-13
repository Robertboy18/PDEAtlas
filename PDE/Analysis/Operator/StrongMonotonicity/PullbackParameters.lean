/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Operator.StrongMonotonicity.Pullback

/-!
# Variation of a pulled-back flux

For a centered Lipschitz flux, variation of the linear gradient map and of the volume
factor has linear growth in the input. This estimate explains why centering at `A(0)`
is useful in boundary regularity: the resulting coefficient error is homogeneous.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Operator

open scoped NNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Varying a linear gradient map changes its adjoint-composed centered flux by a
quantity proportional to the input norm. -/
theorem norm_adjoint_flux_sub_le
    (A : E → E) {C : ℝ≥0} (hA : LipschitzWith C A) (hzero : A 0 = 0)
    (T S : F →L[ℝ] E) (x : F) :
    ‖T.adjoint (A (T x)) - S.adjoint (A (S x))‖ ≤
      C * (‖T‖ + ‖S‖) * ‖T - S‖ * ‖x‖ := by
  have ha : ‖A (T x)‖ ≤ C * ‖T‖ * ‖x‖ := by
    calc
      ‖A (T x)‖ ≤ C * ‖T x‖ := by
        simpa only [dist_eq_norm, hzero, sub_zero] using hA.dist_le_mul (T x) 0
      _ ≤ C * (‖T‖ * ‖x‖) := mul_le_mul_of_nonneg_left (T.le_opNorm x) C.coe_nonneg
      _ = _ := by ring
  have had : ‖A (T x) - A (S x)‖ ≤ C * ‖T - S‖ * ‖x‖ := by
    calc
      ‖A (T x) - A (S x)‖ ≤ C * ‖(T - S) x‖ := by
        simpa only [dist_eq_norm, sub_apply] using hA.dist_le_mul (T x) (S x)
      _ ≤ C * (‖T - S‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left ((T - S).le_opNorm x) C.coe_nonneg
      _ = _ := by ring
  have heq : T.adjoint (A (T x)) - S.adjoint (A (S x)) =
      (T - S).adjoint (A (T x)) + S.adjoint (A (T x) - A (S x)) := by
    simp only [map_sub, sub_apply]
    abel
  calc
    _ ≤ ‖(T - S).adjoint (A (T x))‖ + ‖S.adjoint (A (T x) - A (S x))‖ := by
      rw [heq]
      exact norm_add_le _ _
    _ ≤ ‖T - S‖ * ‖A (T x)‖ + ‖S‖ * ‖A (T x) - A (S x)‖ := by
      apply add_le_add
      · simpa only [LinearIsometryEquiv.norm_map] using (T - S).adjoint.le_opNorm (A (T x))
      · simpa only [LinearIsometryEquiv.norm_map] using S.adjoint.le_opNorm (A (T x) - A (S x))
    _ ≤ ‖T - S‖ * (C * ‖T‖ * ‖x‖) + ‖S‖ * (C * ‖T - S‖ * ‖x‖) :=
      add_le_add (mul_le_mul_of_nonneg_left ha (norm_nonneg _))
        (mul_le_mul_of_nonneg_left had (norm_nonneg S))
    _ = _ := by ring

/-- Exact coefficient variation bound, allowing signed scalar factors. -/
theorem norm_pullbackFlux_sub_same_input_le
    (A : E → E) {C : ℝ≥0} (hA : LipschitzWith C A) (hzero : A 0 = 0)
    (T S : F →L[ℝ] E) (J K : ℝ) (x : F) :
    ‖pullbackFlux A T J x - pullbackFlux A S K x‖ ≤
      |J - K| * C * ‖T‖ ^ 2 * ‖x‖ +
        |K| * C * (‖T‖ + ‖S‖) * ‖T - S‖ * ‖x‖ := by
  have ha : ‖T.adjoint (A (T x))‖ ≤ C * ‖T‖ ^ 2 * ‖x‖ := by
    have h := (lipschitzWith_pullbackFlux A hA T 1).dist_le_mul x 0
    simpa only [dist_eq_norm, pullbackFlux, map_zero, hzero, smul_zero, sub_zero,
      one_smul, NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm, norm_one, one_mul,
      mul_comm (‖T‖ ^ 2) (C : ℝ)] using h
  have heq : pullbackFlux A T J x - pullbackFlux A S K x =
      (J - K) • T.adjoint (A (T x)) +
        K • (T.adjoint (A (T x)) - S.adjoint (A (S x))) := by
    simp only [pullbackFlux, sub_smul, smul_sub]
    abel
  calc
    _ ≤ ‖(J - K) • T.adjoint (A (T x))‖ +
        ‖K • (T.adjoint (A (T x)) - S.adjoint (A (S x)))‖ := by
      rw [heq]
      exact norm_add_le _ _
    _ = |J - K| * ‖T.adjoint (A (T x))‖ +
        |K| * ‖T.adjoint (A (T x)) - S.adjoint (A (S x))‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ |J - K| * (C * ‖T‖ ^ 2 * ‖x‖) +
        |K| * (C * (‖T‖ + ‖S‖) * ‖T - S‖ * ‖x‖) :=
      add_le_add (mul_le_mul_of_nonneg_left ha (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (norm_adjoint_flux_sub_le A hA hzero T S x) (abs_nonneg K))
    _ = _ := by ring

/-- Uniform coefficient bounds give a spatial Lipschitz estimate with linear input growth. -/
theorem norm_pullbackFlux_sub_le_of_parameter_bounds
    {X : Type*} [NormedAddCommGroup X]
    (A : E → E) {C : ℝ≥0} (hA : LipschitzWith C A) (hzero : A 0 = 0)
    (T : X → F →L[ℝ] E) (J : X → ℝ) (M B D H : ℝ≥0) {x y : X}
    (hTx : ‖T x‖ ≤ M) (hTy : ‖T y‖ ≤ M) (hJx : |J x| ≤ B)
    (hTdiff : ‖T y - T x‖ ≤ D * ‖y - x‖)
    (hJdiff : |J y - J x| ≤ H * ‖y - x‖) (v : F) :
    ‖pullbackFlux A (T y) (J y) v - pullbackFlux A (T x) (J x) v‖ ≤
      (H * C * M ^ 2 + 2 * B * C * M * D) * ‖y - x‖ * ‖v‖ := by
  have hsq : ‖T y‖ ^ 2 ≤ (M : ℝ) ^ 2 := by
    nlinarith [norm_nonneg (T y), M.coe_nonneg]
  have hsum : ‖T y‖ + ‖T x‖ ≤ 2 * M := by linarith
  calc
    _ ≤ |J y - J x| * C * ‖T y‖ ^ 2 * ‖v‖ +
        |J x| * C * (‖T y‖ + ‖T x‖) * ‖T y - T x‖ * ‖v‖ :=
      norm_pullbackFlux_sub_same_input_le A hA hzero (T y) (T x) (J y) (J x) v
    _ ≤ (H * ‖y - x‖) * C * M ^ 2 * ‖v‖ +
        B * C * (2 * M) * (D * ‖y - x‖) * ‖v‖ := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
        exact mul_le_mul (mul_le_mul_of_nonneg_right hJdiff C.coe_nonneg) hsq
          (sq_nonneg _) (by positivity)
      · apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
        apply mul_le_mul _ hTdiff (norm_nonneg _) (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_right hJx C.coe_nonneg) hsum
          (by positivity) (by positivity)
    _ = _ := by ring

/-- Combining spatial variation with the state Lipschitz bound gives the joint
estimate needed by nonlinear difference quotients. -/
theorem norm_pullbackFlux_joint_sub_le_of_parameter_bounds
    {X : Type*} [NormedAddCommGroup X]
    (A : E → E) {C : ℝ≥0} (hA : LipschitzWith C A) (hzero : A 0 = 0)
    (T : X → F →L[ℝ] E) (J : X → ℝ) (M B D H : ℝ≥0) {x y : X}
    (hTx : ‖T x‖ ≤ M) (hTy : ‖T y‖ ≤ M)
    (hJx : |J x| ≤ B) (hJy : |J y| ≤ B)
    (hTdiff : ‖T y - T x‖ ≤ D * ‖y - x‖)
    (hJdiff : |J y - J x| ≤ H * ‖y - x‖) (z w : F) :
    ‖pullbackFlux A (T y) (J y) w - pullbackFlux A (T x) (J x) z‖ ≤
      (H * C * M ^ 2 + 2 * B * C * M * D) * ‖y - x‖ * ‖z‖ +
        (B * M ^ 2 * C) * ‖w - z‖ := by
  have hstate :
      ‖pullbackFlux A (T y) (J y) w - pullbackFlux A (T y) (J y) z‖ ≤
        (B * M ^ 2 * C) * ‖w - z‖ := by
    have h := (lipschitzWith_pullbackFlux A hA (T y) (J y)).dist_le_mul w z
    simp only [dist_eq_norm, NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm,
      Real.norm_eq_abs] at h
    apply h.trans
    have hsq : ‖T y‖ ^ 2 ≤ (M : ℝ) ^ 2 := by
      nlinarith [norm_nonneg (T y), M.coe_nonneg]
    gcongr
  have hspace := norm_pullbackFlux_sub_le_of_parameter_bounds
    A hA hzero T J M B D H hTx hTy hJx hTdiff hJdiff z
  calc
    _ ≤ ‖pullbackFlux A (T y) (J y) w - pullbackFlux A (T y) (J y) z‖ +
        ‖pullbackFlux A (T y) (J y) z - pullbackFlux A (T x) (J x) z‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith only [hstate, hspace]

end PDE.Analysis.Operator
