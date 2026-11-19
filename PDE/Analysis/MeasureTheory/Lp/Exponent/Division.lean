/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Basic.ENNReal.Holder

/-!
# Divided Lebesgue exponents

A homogeneous expression of degree `m` in `Lᵖ` variables has exponent `p/m`.
Multiplying it by one further `Lᵖ` variable gives exponent `p/(m+1)`.
The inequalities below keep finite real exponents available without restricting
them to integers.
-/

@[expose] public section

open scoped ENNReal

namespace ENNReal

/-- Dividing by a positive natural degree can only lower an exponent. -/
theorem div_ofReal_nat_le (p : ℝ≥0∞) {m : ℕ} (hm : 0 < m) :
    p / ENNReal.ofReal (m : ℝ) ≤ p := by
  have hden : 1 ≤ ENNReal.ofReal (m : ℝ) := by
    rw [← ofReal_one]
    exact ofReal_le_ofReal (by exact_mod_cast hm)
  simpa using ENNReal.div_le_div_left hden p

/-- Dividing a real exponent larger than a positive degree still gives an
exponent greater than one. -/
theorem one_lt_ofReal_div_nat {q : ℝ} {m : ℕ} (hm : 0 < m) (hmq : (m : ℝ) < q) :
    1 < ENNReal.ofReal q / ENNReal.ofReal (m : ℝ) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  rw [← ofReal_div_of_pos hmR, ← ofReal_one]
  apply (ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).mpr
  exact (lt_div_iff₀ hmR).mpr (by simpa using hmq)

/-- The exponent divided by a positive natural degree is finite. -/
theorem ofReal_div_nat_ne_top (q : ℝ) {m : ℕ} (hm : 0 < m) :
    ENNReal.ofReal q / ENNReal.ofReal (m : ℝ) ≠ ∞ :=
  div_ne_top ofReal_ne_top (by positivity)

/-- The exact Hölder relation for adding one factor to a homogeneous product.
It is a theorem rather than a global instance, to keep exponent inference local. -/
theorem holderTriple_div_nat_succ (p : ℝ≥0∞) {m : ℕ} (hm : 0 < m) :
    HolderTriple p (p / ENNReal.ofReal (m : ℝ))
      (p / ENNReal.ofReal ((m + 1 : ℕ) : ℝ)) := by
  constructor
  rw [ENNReal.inv_div (Or.inl ofReal_ne_top) (Or.inl (by positivity)),
    ENNReal.inv_div (Or.inl ofReal_ne_top) (Or.inl (by positivity))]
  simp only [ofReal_natCast, Nat.cast_add, Nat.cast_one, div_eq_mul_inv]
  rw [ofReal_add (Nat.cast_nonneg m) zero_le_one, ofReal_natCast, ofReal_one,
    add_mul, one_mul]
  exact add_comm _ _

end ENNReal
