/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Quarter powers of real numbers as iterated square roots

A constant such as `2 / (3 ^ (3 / 4) π)` or `η ^ (1 / 4)` is written with a real exponent, while
interval arithmetic evaluates square roots. For `y ≥ 0` the real power `y ^ (1 / 4)` is the
square root of the square root of `y`, and `y ^ (3 / 4)` is `√y` times that. Both follow from
`√y = y ^ (1 / 2)` and the rule for a power of a power. Other rational exponents with a power of
two in the denominator work the same way and are not stated. For `y > 0`,
`PDE.Analysis.rpow_three_quarters_eq_mul_sqrt` writes `y ^ (3 / 4)` as `y ^ (1 / 4) * √y`
instead.

## Main results

* `PDE.Analysis.rpow_quarter_eq_sqrt_sqrt`: `y ^ (1 / 4 : ℝ) = √√y` for every real `y ≥ 0`.
* `PDE.Analysis.rpow_three_quarters_eq_sqrt_mul`: `y ^ (3 / 4 : ℝ) = √y * √√y` for every real
  `y ≥ 0`.
-/

@[expose] public section

namespace PDE.Analysis

/-- For a real `y ≥ 0`, `y ^ (1 / 4) = √√y`, where `1 / 4` is a real exponent. -/
theorem rpow_quarter_eq_sqrt_sqrt {y : ℝ} (hy : 0 ≤ y) : y ^ (1 / 4 : ℝ) = √√y := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hy]
  norm_num

/-- For a real `y ≥ 0`, `y ^ (3 / 4) = √y * √√y`, where `3 / 4` is a real exponent. -/
theorem rpow_three_quarters_eq_sqrt_mul {y : ℝ} (hy : 0 ≤ y) :
    y ^ (3 / 4 : ℝ) = √y * √√y := by
  rw [← rpow_quarter_eq_sqrt_sqrt hy, Real.sqrt_eq_rpow, ← Real.rpow_add' hy (by norm_num)]
  norm_num

end PDE.Analysis
