/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Basic.ENNReal.Holder
import Mathlib.Tactic.Positivity.Finset

/-!
# Hölder exponents for real power growth

Real powers divide Lebesgue exponents. These arithmetic identities identify the
Hölder factor for differences and the conjugate exponent for derivatives of
integral potentials.
-/

@[expose] public section

open scoped ENNReal

namespace ENNReal

/-- Dividing the input exponent by `r - 1` gives the Hölder factor that
pairs with the input space to land in the exponent divided by `r`. -/
theorem holderTriple_div_ofReal {p : ℝ≥0∞} {r : ℝ}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (hr : 1 < r) :
    ENNReal.HolderTriple (p / ENNReal.ofReal (r - 1)) p
      (p / ENNReal.ofReal r) := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hs0 : 0 < r - 1 := sub_pos.mpr hr
  have hq0 : p / ENNReal.ofReal (r - 1) ≠ 0 :=
    ENNReal.div_ne_zero.mpr ⟨hp0, ENNReal.ofReal_ne_top⟩
  have ht0 : p / ENNReal.ofReal r ≠ 0 :=
    ENNReal.div_ne_zero.mpr ⟨hp0, ENNReal.ofReal_ne_top⟩
  constructor
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.add_ne_top.mpr
      ⟨ENNReal.inv_ne_top.mpr hq0, ENNReal.inv_ne_top.mpr hp0⟩)
    (ENNReal.inv_ne_top.mpr ht0)).mp
  rw [ENNReal.toReal_add (ENNReal.inv_ne_top.mpr hq0)
    (ENNReal.inv_ne_top.mpr hp0)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_div,
    ENNReal.toReal_ofReal hs0.le, ENNReal.toReal_ofReal hr0.le]
  field_simp [(ENNReal.toReal_pos hp0 hp).ne', hs0.ne', hr0.ne']
  ring

/-- The exponent divided by its real predecessor is its Hölder conjugate. -/
theorem HolderConjugate.div_ofReal_toReal_sub_one
    (p q : ℝ≥0∞) [HolderConjugate p q] (hp : p ≠ ∞) :
    p / ENNReal.ofReal (p.toReal - 1) = q := by
  rw [ENNReal.ofReal_sub _ zero_le_one, ENNReal.ofReal_toReal hp, ENNReal.ofReal_one]
  apply inv_inj.mp
  rw [ENNReal.inv_div (Or.inr hp) (Or.inr (HolderConjugate.ne_zero p q)),
    div_eq_mul_inv, HolderConjugate.sub_one_mul_inv p q hp]

end ENNReal
