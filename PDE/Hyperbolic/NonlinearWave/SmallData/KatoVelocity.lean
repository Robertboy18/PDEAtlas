/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CAS.ExactTactic

/-!
# From scalar energy to a negative-power velocity bound

A square-velocity estimate and positivity give its positive square root. A linear mass
lower bound then transfers part of the mass power into the time weight. This is the
algebraic step that yields the strict weighted Kato range.
-/

@[expose] public noncomputable section

namespace WaveEquation.SmallData.Kato

/-- Taking the positive square root of the weighted energy inequality. -/
theorem velocity_lower_bound {A r f v p q : ℝ} (hA : 0 ≤ A) (hr : 0 < r) (hf : 0 < f) (hv : 0 ≤ v)
    (hsq : A * r ^ (-q) * f ^ (p + 1) ≤ v ^ 2) :
    A ^ (1 / 2 : ℝ) * r ^ (-q / 2) * f ^ ((p + 1) / 2) ≤ v := by
  have hhalf (x b : ℝ) (hx : 0 ≤ x) : (x ^ (b / 2)) ^ 2 = x ^ b := by
    rw [← Real.rpow_mul_natCast hx]
    congr 1
    push_cast
    cas
  apply (sq_le_sq₀ (by positivity) hv).mp
  rw [mul_pow, mul_pow, hhalf r (-q) hr.le, hhalf f (p + 1) hf.le, hhalf A 1 hA, Real.rpow_one]
  exact hsq

/-- Linear mass growth converts the positive square-root estimate into a lower bound
for `v * f^(-1-e)`. The remaining time exponent is `(p-1-q)/2-e`. -/
theorem weighted_power_velocity_lower_bound {c r f v δ p q e : ℝ} (hc : 0 ≤ c) (hr : 0 < r)
    (hδ : 0 ≤ δ) (hf : 0 < f) (he : e ≤ (p - 1) / 2) (hlinear : δ * r ≤ f)
    (hvelocity : c * r ^ (-q / 2) * f ^ ((p + 1) / 2) ≤ v) :
    c * δ ^ ((p - 1) / 2 - e) * r ^ ((p - 1 - q) / 2 - e) ≤ v * f ^ (-1 - e) := by
  let z := (p - 1) / 2 - e
  have hz : 0 ≤ z := sub_nonneg.mpr he
  have hpow : (δ * r) ^ z ≤ f ^ z := Real.rpow_le_rpow (mul_nonneg hδ hr.le) hlinear hz
  calc
    c * δ ^ ((p - 1) / 2 - e) * r ^ ((p - 1 - q) / 2 - e) =
        c * r ^ (-q / 2) * (δ * r) ^ z := by
      rw [Real.mul_rpow hδ hr.le]
      rw [show (p - 1 - q) / 2 - e = -q / 2 + z by dsimp [z]; cas, Real.rpow_add hr]
      ring
    _ ≤ c * r ^ (-q / 2) * f ^ z :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg hc (Real.rpow_nonneg hr.le _))
    _ = (c * r ^ (-q / 2) * f ^ ((p + 1) / 2)) * f ^ (-1 - e) := by
      rw [mul_assoc (c * r ^ (-q / 2)), ← Real.rpow_add hf]
      congr 1
      congr 1
      dsimp [z]
      cas
    _ ≤ v * f ^ (-1 - e) := mul_le_mul_of_nonneg_right hvelocity (Real.rpow_nonneg hf.le _)

end WaveEquation.SmallData.Kato
