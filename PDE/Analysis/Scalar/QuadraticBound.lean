/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

/-!
# A homogeneous bound from a quadratic energy inequality

The elementary split at `X = T` gives a convenient explicit constant without taking
square roots. This is useful when `T` is a norm of the data and `X` an unknown derivative.
-/

@[expose] public section

namespace PDE.Analysis.Scalar

/-- A coercive quadratic inequality gives a linear bound by the data size, also when
that size is zero. The constant is chosen for simplicity rather than sharpness. -/
theorem le_linear_of_quadratic_le {m a b X T : ℝ}
    (hm : 0 < m) (ha : 0 ≤ a) (hb : 0 ≤ b) (hT : 0 ≤ T)
    (h : m * X ^ 2 ≤ a * T * X + b * T ^ 2) :
    X ≤ (1 + (a + b) / m) * T := by
  by_cases hXT : X ≤ T
  · exact hXT.trans (by
      have := mul_nonneg (div_nonneg (add_nonneg ha hb) hm.le) hT
      nlinarith)
  · have hTX : T < X := lt_of_not_ge hXT
    have hX : 0 < X := hT.trans_lt hTX
    have hTT : T ^ 2 ≤ T * X := by nlinarith
    have hmul : m * X * X ≤ ((a + b) * T) * X := by
      nlinarith only [h, mul_le_mul_of_nonneg_left hTT hb]
    have hmX : m * X ≤ (a + b) * T := (mul_le_mul_iff_left₀ hX).mp hmul
    calc
      X ≤ (a + b) * T / m := (le_div_iff₀ hm).mpr (by nlinarith only [hmX])
      _ ≤ (1 + (a + b) / m) * T := by
        have heq : (1 + (a + b) / m) * T = T + (a + b) * T / m := by ring
        rw [heq]
        exact le_add_of_nonneg_left hT

end PDE.Analysis.Scalar
