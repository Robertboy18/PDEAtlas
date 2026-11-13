/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.Holder

/-!
# Constant bounded multipliers

An `L∞` coefficient represented almost everywhere by a constant acts on scalar `Lᵖ`
as ordinary scalar multiplication. The measure need not be finite.
-/

@[expose] public section

namespace MeasureTheory.Lp

open scoped ENNReal

/-- A constant representative identifies bounded multiplication with scalar multiplication. -/
theorem lpSMul_eq_const_smul
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    (a : Lp ℝ ∞ μ) (c : ℝ) (ha : (a : α → ℝ) =ᵐ[μ] fun _ ↦ c) (u : Lp ℝ p μ) :
    a • u = c • u := by
  apply Lp.ext
  filter_upwards [coeFn_lpSMul (r := p) a u, ha, coeFn_smul c u] with x hm ha hs
  simp only [hm, hs, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, ha]

end MeasureTheory.Lp
