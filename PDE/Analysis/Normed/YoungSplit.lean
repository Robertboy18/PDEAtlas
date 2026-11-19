/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Group.Basic

/-!
# The squared norm of a difference with a weight

`‖u - v‖² ≤ (1 + t) ‖u‖² + (1 + 1/t) ‖v‖²` for every `t > 0` (`norm_sub_sq_le_young`): the
triangle inequality and `2ab ≤ t a² + b² / t`.
-/

@[expose] public section

namespace PDE

/-- `‖u - v‖² ≤ (1 + t) ‖u‖² + (1 + 1/t) ‖v‖²` for `t > 0`. -/
theorem norm_sub_sq_le_young {E : Type*} [SeminormedAddCommGroup E] (u v : E) {t : ℝ}
    (ht : 0 < t) : ‖u - v‖ ^ 2 ≤ (1 + t) * ‖u‖ ^ 2 + (1 + 1 / t) * ‖v‖ ^ 2 := by
  have h1 : ‖u - v‖ ≤ ‖u‖ + ‖v‖ := norm_sub_le u v
  have h2 : 2 * ‖u‖ * ‖v‖ ≤ t * ‖u‖ ^ 2 + 1 / t * ‖v‖ ^ 2 := by
    have h := sq_nonneg (t * ‖u‖ - ‖v‖)
    have : 0 ≤ (t * ‖u‖ - ‖v‖) ^ 2 / t := div_nonneg h ht.le
    have e : (t * ‖u‖ - ‖v‖) ^ 2 / t = t * ‖u‖ ^ 2 + 1 / t * ‖v‖ ^ 2 - 2 * ‖u‖ * ‖v‖ := by
      field_simp
      ring
    linarith
  calc ‖u - v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by gcongr
    _ = ‖u‖ ^ 2 + 2 * ‖u‖ * ‖v‖ + ‖v‖ ^ 2 := by ring
    _ ≤ (1 + t) * ‖u‖ ^ 2 + (1 + 1 / t) * ‖v‖ ^ 2 := by linarith

end PDE
