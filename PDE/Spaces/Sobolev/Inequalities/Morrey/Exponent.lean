/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Basic.ENNReal.Real

/-!
# Morrey exponents

`SobolevSpace.morreyExponent n p` is the Hölder exponent `γ = 1 - n / p` of Morrey's inequality,
Evans §5.6.2, Theorem 4, where `n < p ≤ ∞`. The quotient is taken through `ENNReal.toReal`, so
`γ = 1` at `p = ∞`, as in Evans. The definition is total: at `p = 0` it also returns `1`, a value of
totalized division with no analytic meaning. We prove the formula for real `p`
(`morreyExponent_ofReal`) and the positivity of `γ` for `0 < n < p ≤ ∞` (`morreyExponent_pos`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.6.2, Theorem 4, p. 280.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace


open scoped ENNReal

/-- The Morrey Hölder exponent `1 - n / p`. With Mathlib's convention
`ENNReal.toReal ∞ = 0`, this gives exponent `1` at `p = ∞`. The definition
is total, but its analytic use is restricted by hypotheses such as `n < p`. -/
def morreyExponent (n : ℕ) (p : ℝ≥0∞) : ℝ :=
  1 - (n : ℝ) / p.toReal

/-- At `p = ∞` the Morrey exponent is `1`, the Lipschitz exponent. -/
@[simp]
theorem morreyExponent_top (n : ℕ) :
    morreyExponent n ∞ = 1 := by
  simp [morreyExponent]

/-- At `p = 0` the totalized formula also returns `1`; this value has no analytic meaning and
only exists because `ENNReal.toReal 0 = 0` and division by zero is `0`. -/
@[simp]
theorem morreyExponent_zero (n : ℕ) :
    morreyExponent n 0 = 1 := by
  simp [morreyExponent]

/-- For real `p ≥ 0`, `morreyExponent n (ENNReal.ofReal p)` is the real number `1 - n / p`. -/
theorem morreyExponent_ofReal (n : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    morreyExponent n (ENNReal.ofReal p) = 1 - (n : ℝ) / p := by
  simp [morreyExponent, ENNReal.toReal_ofReal hp]

/-- If `0 < n` and `n < p` (including `p = ∞`), the Morrey exponent is positive. -/
theorem morreyExponent_pos {n : ℕ} {p : ℝ≥0∞}
    (hn : 0 < n) (hp : (n : ℝ≥0∞) < p) :
    0 < morreyExponent n p := by
  by_cases hpTop : p = ∞
  · simp [hpTop]
  · have hpReal : (n : ℝ) < p.toReal := by
      simpa using ENNReal.toReal_strict_mono hpTop hp
    have hpReal0 : 0 < p.toReal :=
      (Nat.cast_pos.mpr hn).trans hpReal
    simp only [morreyExponent]
    exact sub_pos.mpr ((div_lt_one hpReal0).2 hpReal)

/-- In one dimension the Morrey exponent `1 - 1/p` is positive for every `p > 1`. -/
theorem morreyExponent_one_pos {p : ℝ≥0∞} (hp : (1 : ℝ≥0∞) < p) :
    0 < morreyExponent 1 p := by
  apply morreyExponent_pos Nat.zero_lt_one
  simpa using hp

/-- The real-exponent form of `morreyExponent_pos`: if `0 < n` and `n < p` for real `p`, then
`1 - n / p > 0`. -/
theorem morreyExponent_ofReal_pos {n : ℕ} {p : ℝ} (hn : 0 < n) (hp : (n : ℝ) < p) :
    0 < morreyExponent n (ENNReal.ofReal p) := by
  have hp0 : 0 < p := lt_trans (Nat.cast_pos.mpr hn) hp
  rw [morreyExponent_ofReal n hp0.le]
  exact sub_pos.mpr (div_lt_one hp0 |>.2 hp)

end SobolevSpace
