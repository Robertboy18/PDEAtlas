/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Real.Sqrt
import CAS.ExactTactic

/-!
# The three-dimensional Strauss exponent

The critical exponent of the wave equation `u_tt - Δu = |u|^p` in `ℝ³` is `1 + √2`, the positive
root of `p (p - 2) = 1`. Two facts about this number, with no reference to the equation:

* `two_lt_one_add_sqrt_two`: it is larger than two, so the range `2 ≤ p < 1 + √2`, where the
  power `|u|^p` is `C²`, is not empty;
* `one_add_sqrt_two_strauss_equality`: it satisfies `p (p - 2) = 1`.
-/

@[expose] public section

namespace WaveEquation.SmallData

/-- The positive three-dimensional Strauss root is strictly greater than two. -/
theorem two_lt_one_add_sqrt_two : (2 : ℝ) < 1 + Real.sqrt 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := Real.sqrt_nonneg 2
  nlinarith only [hs, hn]

/-- The positive Strauss root satisfies the precise reciprocal-density identity. -/
theorem one_add_sqrt_two_strauss_equality :
    (1 + Real.sqrt 2) * ((1 + Real.sqrt 2) - 2) = 1 := by
  cas

end WaveEquation.SmallData
