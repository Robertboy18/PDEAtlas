/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import CAS.ExactTactic

/-!
# Closing the subcritical wave amplitude estimate

The retarded-potential estimate has amplitude exponent `max (p - 4) 0`. It is strictly below one for
every real `p < 5`, so the resulting scalar inequality bounds the amplitude uniformly. This is the
last step of the proof of Theorem 3 of Evans, §12.3.3, where for `4 < p < 5` the bound
`|u| ≤ C + C ‖u‖_∞ ^ (p - 4)` closes because `0 < p - 4 < 1`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.3.3, Theorem 3, step 3 of its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- A scalar inequality with a strictly sublinear power has a uniform upper bound.
The coefficient need not be positive, and the exponent may be negative. -/
theorem exists_bound_of_le_mul_one_add_rpow {q : ℝ} (hq : q < 1) (C : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ a : ℝ, 0 ≤ a → a ≤ C * (1 + a ^ q) → a ≤ B := by
  obtain ⟨b, hb⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (sub_pos.mpr hq)).eventually (eventually_gt_atTop (2 * C)))
  refine ⟨max 1 (max b (2 * C)), lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun a _ ha ↦ ?_⟩
  by_contra! hlarge
  have ha1 : 1 < a := (le_max_left _ _).trans_lt hlarge
  have ha0 : 0 < a := zero_lt_one.trans ha1
  have hab : b ≤ a := (le_max_left b (2 * C)).trans ((le_max_right _ _).trans hlarge.le)
  have haC : 2 * C ≤ a := (le_max_right b (2 * C)).trans ((le_max_right _ _).trans hlarge.le)
  have hpow : a / a ^ q ≤ 2 * C := by
    apply (div_le_iff₀ (Real.rpow_pos_of_pos ha0 q)).mpr
    nlinarith
  have heq : a ^ (1 - q) = a / a ^ q := by
    cas using ha0
  rw [← heq] at hpow
  exact (not_lt_of_ge hpow) (hb a hab)

/-- The three-dimensional subcritical power range closes the amplitude estimate,
including the interval `4 < p < 5` where its exponent is positive. -/
theorem exists_amplitude_bound {p : ℝ} (hp : p < 5) (C : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ a : ℝ, 0 ≤ a → a ≤ C * (1 + a ^ max (p - 4) 0) → a ≤ B := by
  apply exists_bound_of_le_mul_one_add_rpow
  exact max_lt (by linarith) zero_lt_one

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
