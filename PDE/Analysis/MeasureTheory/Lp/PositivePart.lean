/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# The nonnegative cone in real `Lᵖ`

The positive-part map on `Lp` identifies the closed cone of almost-everywhere nonnegative
functions. No order instance on `Lp` is needed.
-/

@[expose] public section

namespace MeasureTheory.Lp

open Filter
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞}

/-- The positive part is nonnegative almost everywhere. -/
theorem posPart_nonneg_ae (u : Lp ℝ p μ) : ∀ᵐ x ∂μ, 0 ≤ posPart u x := by
  filter_upwards [coeFn_posPart u] with x hx
  exact hx.symm ▸ le_max_right (u x) 0

/-- Nonnegative representatives are precisely the fixed points of the positive-part map. -/
theorem posPart_eq_self_iff (u : Lp ℝ p μ) :
    posPart u = u ↔ ∀ᵐ x ∂μ, 0 ≤ u x := by
  constructor
  · intro h
    simpa only [h] using posPart_nonneg_ae u
  · intro h
    apply Lp.ext
    filter_upwards [coeFn_posPart u, h] with x hx hnonneg
    exact hx.trans (max_eq_left hnonneg)

/-- The positive part vanishes exactly for almost-everywhere nonpositive functions. -/
theorem posPart_eq_zero_iff (u : Lp ℝ p μ) :
    posPart u = 0 ↔ ∀ᵐ x ∂μ, u x ≤ 0 := by
  constructor
  · intro h
    have hpos := coeFn_posPart u
    rw [h] at hpos
    filter_upwards [hpos, coeFn_zero ℝ p μ] with x hx hz
    exact (le_max_left _ _).trans_eq (hx.symm.trans hz)
  · intro h
    apply Lp.ext
    filter_upwards [h, coeFn_posPart u, coeFn_zero ℝ p μ] with x hx hp hz
    exact hp.trans ((max_eq_right hx).trans hz.symm)

/-- Almost-everywhere order is equivalent to the vanishing positive part of the difference. -/
theorem posPart_sub_eq_zero_iff (u v : Lp ℝ p μ) :
    posPart (u - v) = 0 ↔ ∀ᵐ x ∂μ, u x ≤ v x := by
  rw [posPart_eq_zero_iff]
  apply Filter.eventually_congr
  filter_upwards [coeFn_sub u v] with x hx
  rw [hx]
  exact sub_nonpos

/-- Taking the positive part does not increase the `Lᵖ` norm. -/
theorem norm_posPart_le (u : Lp ℝ p μ) : ‖posPart u‖ ≤ ‖u‖ := by
  apply norm_le_norm_of_ae_le
  filter_upwards [coeFn_posPart u] with x hx
  rw [hx, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), Real.norm_eq_abs]
  exact max_le (le_abs_self _) (abs_nonneg _)

/-- Almost-everywhere nonnegativity is closed for convergence in `Lᵖ`. -/
theorem isClosed_nonneg_ae [Fact (1 ≤ p)] :
    IsClosed {u : Lp ℝ p μ | ∀ᵐ x ∂μ, 0 ≤ u x} := by
  have heq : {u : Lp ℝ p μ | ∀ᵐ x ∂μ, 0 ≤ u x} = {u | posPart u = u} := by
    ext u
    exact (posPart_eq_self_iff u).symm
  rw [heq]
  exact isClosed_eq continuous_posPart continuous_id

end MeasureTheory.Lp
