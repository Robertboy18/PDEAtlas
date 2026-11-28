/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset

/-!
# Positive parameters with a small quadratic cost

For every `c > 0` and every real `K` there is `k > 0` with `K ^ 2 * k ^ 2 < c`
(`PDE.Analysis.exists_pos_sq_mul_sq_lt`). The proof takes `k = min d 1` for a `d > 0` with
`(K ^ 2 + 1) * d < c`.
-/

@[expose] public section

namespace PDE.Analysis

/-- A sufficiently short time scale makes the squared trace cost smaller
than any prescribed positive spatial-volume coefficient. -/
theorem exists_pos_sq_mul_sq_lt {c : ℝ} (hc : 0 < c) (K : ℝ) :
    ∃ k : ℝ, 0 < k ∧ K ^ 2 * k ^ 2 < c := by
  obtain ⟨d, hd, hdc⟩ := exists_pos_mul_lt hc (K ^ 2 + 1)
  refine ⟨min d 1, lt_min hd zero_lt_one, ?_⟩
  have hk : 0 ≤ min d 1 := (lt_min hd zero_lt_one).le
  have hk1 : min d 1 ≤ 1 := min_le_right _ _
  have hkd : min d 1 ≤ d := min_le_left _ _
  have hksq : (min d 1) ^ 2 ≤ min d 1 := by nlinarith
  calc
    K ^ 2 * (min d 1) ^ 2 ≤ K ^ 2 * min d 1 :=
      mul_le_mul_of_nonneg_left hksq (sq_nonneg K)
    _ ≤ (K ^ 2 + 1) * min d 1 := by nlinarith
    _ ≤ (K ^ 2 + 1) * d :=
      mul_le_mul_of_nonneg_left hkd (by positivity)
    _ < c := hdc

end PDE.Analysis
