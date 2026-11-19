/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Osgood

/-!
# Absorbing constants in the Kato and Osgood bounds

Estimates of a velocity built from several Biot-Savart terms meet the Kato bound
`1 + B log (2 + M) + B` and the homogeneous bound `φ_{2A+M}(η) + η` with the data multiplied by
constants. The constants are absorbed.

## Main results

* `log_two_add_mul_le`: `log (2 + c M) ≤ log (1 + c) + log (2 + M)` for `c, M ≥ 0`.
* `osgoodModulus_le_of_le_mul`: for `0 ≤ η ≤ A`, `M ≥ 0`, `l, κ ≥ 1` and `l η ≤ K ≤ κ (2A + M)`,
  `φ_K(l η) ≤ l (φ_{2A+M}(η) + η log κ)`.
* `osgoodModulus_le_of_le`: `φ_A(r) ≤ A` for `0 ≤ r ≤ A`, from `log t ≤ t - 1`.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

/-- `log (2 + c M) ≤ log (1 + c) + log (2 + M)` for `c, M ≥ 0`. -/
theorem log_two_add_mul_le {c M : ℝ} (hc : 0 ≤ c) (hM : 0 ≤ M) :
    Real.log (2 + c * M) ≤ Real.log (1 + c) + Real.log (2 + M) := by
  rw [← Real.log_mul (by positivity) (by positivity)]
  exact Real.log_le_log (by positivity) (by nlinarith)

/-- **Constants in the Osgood modulus**: for `0 ≤ η ≤ A`, `M ≥ 0`, `l, κ ≥ 1` and
`l η ≤ K ≤ κ (2A + M)`, `φ_K(l η) ≤ l (φ_{2A+M}(η) + η log κ)`. -/
theorem osgoodModulus_le_of_le_mul {K A M η κ l : ℝ} (hη : 0 ≤ η) (hηA : η ≤ A) (hM : 0 ≤ M)
    (hκ : 1 ≤ κ) (hl : 1 ≤ l) (hK : l * η ≤ K) (hK' : K ≤ κ * (2 * A + M)) :
    osgoodModulus K (l * η) ≤ l * (osgoodModulus (2 * A + M) η + η * Real.log κ) := by
  rcases hη.eq_or_lt with rfl | hη0
  · simp
  have hK0 : 0 < K := lt_of_lt_of_le (by nlinarith) hK
  have hX : 0 < 2 * A + M := by linarith
  calc osgoodModulus K (l * η) ≤ l * osgoodModulus K η := osgoodModulus_mul_le hK0 hl hη
    _ ≤ l * osgoodModulus (κ * (2 * A + M)) η :=
      mul_le_mul_of_nonneg_left (osgoodModulus_le_osgoodModulus hK0 hK' hη) (by linarith)
    _ = l * (osgoodModulus (2 * A + M) η + η * Real.log κ) := by
      congr 1
      unfold osgoodModulus
      rw [mul_div_assoc, Real.log_mul (by positivity) (by positivity)]
      ring

/-- `φ_A(r) ≤ A` for `0 ≤ r ≤ A`. -/
theorem osgoodModulus_le_of_le {A r : ℝ} (hr : 0 ≤ r) (hrA : r ≤ A) : osgoodModulus A r ≤ A := by
  rcases hr.eq_or_lt with rfl | hr0
  · simpa using hrA
  have hA : 0 < A := hr0.trans_le hrA
  have hlog := Real.log_le_sub_one_of_pos (div_pos hA hr0)
  unfold osgoodModulus
  calc r * (1 + Real.log (A / r)) ≤ r * (1 + (A / r - 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) hr
    _ = A := by field_simp; ring

end PDE.Analysis
