/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Signed powers for interpolation by integration by parts

The function `x ↦ x * |x| ^ a` is continuously differentiable for every `a > 0`.
In particular its derivative at zero vanishes, even when the absolute power
factor itself is not differentiable there.
-/

@[expose] public section

open Asymptotics Filter
open scoped Topology

namespace Real

/-- The derivative of a signed power, including at zero. -/
theorem hasDerivAt_mul_abs_rpow (x : ℝ) {a : ℝ} (ha : 0 < a) :
    HasDerivAt (fun x : ℝ ↦ x * |x| ^ a) ((a + 1) * |x| ^ a) x := by
  by_cases hx : x = 0
  · subst x
    simp only [abs_zero, zero_rpow ha.ne', mul_zero]
    apply HasDerivAt.of_isLittleO
    simp only [zero_mul, sub_zero, smul_zero]
    have hsmall : (fun x : ℝ ↦ |x| ^ a) =o[𝓝 0] fun _ ↦ (1 : ℝ) := by
      apply (isLittleO_const_iff one_ne_zero).mpr
      simpa only [id_eq, abs_zero, zero_rpow ha.ne'] using
        ((continuousAt_id (x := (0 : ℝ))).abs.rpow_const (Or.inr ha.le)).tendsto
    simpa only [mul_one] using (isBigO_refl (fun x : ℝ ↦ x) (𝓝 0)).mul_isLittleO hsmall
  · have h := (hasDerivAt_id x).mul
      ((hasDerivAt_abs hx).rpow_const (p := a) (Or.inl (abs_ne_zero.mpr hx)))
    convert h using 1
    · rfl
    · rw [rpow_sub_one (abs_ne_zero.mpr hx)]
      rcases lt_or_gt_of_ne hx with hx | hx
      · simp [hx, abs_of_neg hx]
        field_simp
        ring
      · simp [hx, abs_of_pos hx]
        field_simp
        ring

/-- Signed powers with positive exponent have a continuous first derivative. -/
theorem contDiff_mul_abs_rpow {a : ℝ} (ha : 0 < a) :
    ContDiff ℝ 1 (fun x : ℝ ↦ x * |x| ^ a) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x ↦ (hasDerivAt_mul_abs_rpow x ha).differentiableAt, ?_⟩
  simp only [funext (fun x ↦ (hasDerivAt_mul_abs_rpow x ha).deriv)]
  exact continuous_const.mul (continuous_abs.rpow_const (fun _ ↦ Or.inr ha.le))

end Real
