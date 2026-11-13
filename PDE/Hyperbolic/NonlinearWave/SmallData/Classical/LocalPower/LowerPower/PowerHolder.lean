/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SignedPower
public import Mathlib.Analysis.InnerProductSpace.NormPow
public import Mathlib.Analysis.MeanInequalitiesPow
import CAS.ExactTactic

/-!
# Hölder control of the lower-power reaction derivative

For `1 < p ≤ 2`, the derivative of `|x|^p` is globally Hölder continuous
with exponent `p - 1`. The estimate includes pairs crossing zero and uses
no bounded second derivative. It is a coefficient estimate for subsequent
regularity arguments for the constructed integral solution.
-/

@[expose] public noncomputable section

namespace WaveEquation.SmallData.Classical.LocalPower.LowerPower

/-- Subadditivity of a concave power bounds its increment on the nonnegative
half-line by the same power of the increment. -/
theorem norm_rpow_sub_le_rpow_norm_sub {r a b : ℝ}
    (hr : 0 ≤ r) (hr₁ : r ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖a ^ r - b ^ r‖ ≤ ‖a - b‖ ^ r := by
  wlog hab : b ≤ a generalizing a b
  · simpa only [norm_sub_rev] using this hb ha (le_of_not_ge hab)
  have hpow := Real.rpow_add_le_add_rpow (sub_nonneg.mpr hab) hb hr hr₁
  rw [sub_add_cancel] at hpow
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr
    (Real.rpow_le_rpow hb hab hr)), Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)]
  linarith

/-- A positive odd power of exponent at most one is globally Hölder,
including arguments on opposite sides of zero. -/
theorem norm_signedPower_sub_le_rpow {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (x y : ℝ) :
    ‖Real.signedPower r x - Real.signedPower r y‖ ≤ 2 * ‖x - y‖ ^ r := by
  have hp : ‖x⁺ - y⁺‖ ≤ ‖x - y‖ := by
    simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using lipschitzWith_posPart.dist_le_mul x y
  have hn : ‖x⁻ - y⁻‖ ≤ ‖x - y‖ := by
    simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using lipschitzWith_negPart.dist_le_mul x y
  rw [Real.signedPower_eq_posPart_sub_negPart hr, Real.signedPower_eq_posPart_sub_negPart hr]
  calc
    ‖(x⁺ ^ r - x⁻ ^ r) - (y⁺ ^ r - y⁻ ^ r)‖ =
        ‖(x⁺ ^ r - y⁺ ^ r) - (x⁻ ^ r - y⁻ ^ r)‖ := by congr 1; cas
    _ ≤ ‖x⁺ ^ r - y⁺ ^ r‖ + ‖x⁻ ^ r - y⁻ ^ r‖ := norm_sub_le _ _
    _ ≤ ‖x⁺ - y⁺‖ ^ r + ‖x⁻ - y⁻‖ ^ r := add_le_add
        (norm_rpow_sub_le_rpow_norm_sub hr.le hr₁ (posPart_nonneg x) (posPart_nonneg y))
        (norm_rpow_sub_le_rpow_norm_sub hr.le hr₁ (negPart_nonneg x) (negPart_nonneg y))
    _ ≤ ‖x - y‖ ^ r + ‖x - y‖ ^ r := add_le_add (Real.rpow_le_rpow (norm_nonneg _) hp hr.le)
        (Real.rpow_le_rpow (norm_nonneg _) hn hr.le)
    _ = 2 * ‖x - y‖ ^ r := by cas

/-- Express the absolute-power derivative formula using the odd
power of exponent `p - 1`, including its value at zero. -/
theorem deriv_abs_rpow_eq_signedPower {p : ℝ} (hp : 1 < p) (x : ℝ) :
    deriv (fun y : ℝ ↦ |y| ^ p) x = p * Real.signedPower (p - 1) x := by
  rw [(hasDerivAt_abs_rpow x hp).deriv]
  unfold Real.signedPower
  rw [show p - 1 - 1 = p - 2 by cas]
  exact mul_assoc _ _ _

/-- The derivative of the lower-power reaction has a global Hölder bound with exponent `p - 1`. -/
theorem norm_deriv_abs_rpow_sub_le {p : ℝ} (hp : 1 < p) (hp₂ : p ≤ 2) (x y : ℝ) :
    ‖deriv (fun z : ℝ ↦ |z| ^ p) x - deriv (fun z : ℝ ↦ |z| ^ p) y‖ ≤
      (2 * p) * ‖x - y‖ ^ (p - 1) := by
  rw [deriv_abs_rpow_eq_signedPower hp, deriv_abs_rpow_eq_signedPower hp,
    ← mul_sub, norm_mul, Real.norm_of_nonneg (by linarith : 0 ≤ p)]
  calc
    p * ‖Real.signedPower (p - 1) x - Real.signedPower (p - 1) y‖ ≤ p * (2 * ‖x - y‖ ^ (p - 1)) :=
      mul_le_mul_of_nonneg_left
        (norm_signedPower_sub_le_rpow (by linarith) (by linarith) x y) (by linarith)
    _ = (2 * p) * ‖x - y‖ ^ (p - 1) := by cas

end WaveEquation.SmallData.Classical.LocalPower.LowerPower
