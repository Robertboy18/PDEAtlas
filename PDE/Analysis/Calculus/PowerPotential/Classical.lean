/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.PowerPotential
public import PDE.Analysis.Calculus.SignedPower.Deriv

/-!
# Classical identities for the real power potential

These identities include zero arguments and real, nonintegral exponents.
They connect the actual C² primitive to the energy density used in semilinear
Dirichlet equations.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace Real

/-- The primitive of the signed power is C¹, including at zero. -/
theorem contDiff_one_signedPowerPotential {p : ℝ} (hp : 1 ≤ p) :
    ContDiff ℝ 1 (signedPowerPotential p) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x ↦ (hasDerivAt_signedPowerPotential hp x).differentiableAt, ?_⟩
  have hd : deriv (signedPowerPotential p) = signedPower p :=
    funext fun x ↦ (hasDerivAt_signedPowerPotential hp x).deriv
  rw [hd]
  exact continuous_signedPower (zero_lt_one.trans_le hp)

/-- The power potential is C² for every exponent at least one.
This follows from the continuous first derivative of the odd power, without a
smoothness assumption on a nonintegral power. -/
theorem contDiff_two_signedPowerPotential {p : ℝ} (hp : 1 ≤ p) :
    ContDiff ℝ 2 (signedPowerPotential p) := by
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun x ↦ (hasDerivAt_signedPowerPotential hp x).differentiableAt, ?_, ?_⟩
  · simp
  · have hd : deriv (signedPowerPotential p) = signedPower p :=
      funext fun x ↦ (hasDerivAt_signedPowerPotential hp x).deriv
    rw [hd]
    exact contDiff_one_signedPower hp

/-- Multiplication by the argument gives the unnormalized potential density. -/
theorem mul_signedPower_eq_abs_rpow {p : ℝ} (hp : 1 ≤ p) (x : ℝ) :
    x * signedPower p x = |x| ^ (p + 1) := by
  rw [signedPower]
  have he : p + 1 = (p - 1) + 2 := by ring
  rw [he, rpow_add_of_nonneg (abs_nonneg x) (sub_nonneg.mpr hp) (by norm_num),
    rpow_two, sq_abs]
  ring

end Real
