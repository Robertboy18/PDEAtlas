/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Tactic.Positivity.Finset

/-!
# Exponents for bounded-function derivative interpolation

For top derivative order `k`, the exponent at order `j` is `2k/j`, with
infinity at order zero. Adjacent exponents satisfy the Hölder relation
needed by the integration-by-parts estimate.
-/

@[expose] public noncomputable section

open scoped ENNReal

namespace SobolevSpace.GagliardoNirenberg

/-- The interpolation exponent `2k/j`, including infinity when `j = 0`. -/
def derivativeExponent (k j : ℕ) : ℝ≥0∞ :=
  (ENNReal.ofReal ((j : ℝ) / (2 * k)))⁻¹

@[simp]
theorem derivativeExponent_zero (k : ℕ) : derivativeExponent k 0 = ∞ := by
  simp [derivativeExponent]

/-- Positive derivative orders have the usual finite real exponent. -/
theorem derivativeExponent_eq_of_pos {k j : ℕ} (hk : 0 < k) (hj : 0 < j) :
    derivativeExponent k j = ENNReal.ofReal (2 * (k : ℝ) / j) := by
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hj' : 0 < (j : ℝ) := by exact_mod_cast hj
  rw [derivativeExponent, ← ENNReal.ofReal_inv_of_pos (div_pos hj' (by positivity)),
    inv_div]

@[simp]
theorem derivativeExponent_self {k : ℕ} (hk : 0 < k) : derivativeExponent k k = 2 := by
  rw [derivativeExponent_eq_of_pos hk hk]
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [mul_div_cancel_right₀ _ hk']
  norm_num

/-- All interpolation exponents through the top order are at least two. -/
theorem two_le_derivativeExponent {k j : ℕ} (hj : j ≤ k) :
    2 ≤ derivativeExponent k j := by
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · simp
  · have hk : 0 < k := hjpos.trans_le hj
    rw [derivativeExponent_eq_of_pos hk hjpos]
    have hj' : 0 < (j : ℝ) := by exact_mod_cast hjpos
    have hjk' : (j : ℝ) ≤ k := by exact_mod_cast hj
    have hreal : (2 : ℝ) ≤ 2 * (k : ℝ) / j := by
      rw [le_div_iff₀ hj']
      linarith
    simpa using ENNReal.ofReal_le_ofReal hreal

/-- Interior derivative orders have exponent strictly greater than two. -/
theorem two_lt_derivative_exponent {k j : ℕ} (hj : 0 < j) (hjk : j < k) :
    2 < 2 * (k : ℝ) / j := by
  have hj' : 0 < (j : ℝ) := by exact_mod_cast hj
  have hjk' : (j : ℝ) < k := by exact_mod_cast hjk
  rw [lt_div_iff₀ hj']
  linarith

/-- The exponents at orders `j - 1` and `j + 1` multiply into half the
exponent at order `j`. This includes the infinity exponent when `j = 1`. -/
theorem derivativeExponent_holder {k j : ℕ} (hk : 0 < k) (hj : 0 < j) :
    ENNReal.HolderTriple (derivativeExponent k (j - 1))
      (derivativeExponent k (j + 1)) (ENNReal.ofReal ((2 * (k : ℝ) / j) / 2)) := by
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hj' : 0 < (j : ℝ) := by exact_mod_cast hj
  constructor
  simp only [derivativeExponent, inv_inv]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_inv_of_pos (by positivity)]
  congr 1
  rw [Nat.cast_sub (by omega : 1 ≤ j), Nat.cast_add, Nat.cast_one]
  field_simp
  ring

end SobolevSpace.GagliardoNirenberg
