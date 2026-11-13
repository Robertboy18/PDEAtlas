/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# A normalized smooth pulse on the unit interval

The weight is the product `expNegInvGlue s * expNegInvGlue (1 - s)`.
Its positive Lebesgue integral normalizes it to a smooth probability density.
Reflection about `1 / 2` gives its first moment.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace PDE.Analysis.NormalizedPulse

/-- The product of the two flat glue functions at the endpoints of the unit interval. -/
def weight (s : ℝ) : ℝ :=
  expNegInvGlue s * expNegInvGlue (1 - s)

/-- The pulse weight is infinitely differentiable on the whole real line. -/
theorem contDiff_weight : ContDiff ℝ ∞ weight :=
  expNegInvGlue.contDiff.mul
    (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))

/-- The pulse weight is nonnegative everywhere. -/
theorem weight_nonneg (s : ℝ) : 0 ≤ weight s :=
  mul_nonneg (expNegInvGlue.nonneg s) (expNegInvGlue.nonneg (1 - s))

/-- The pulse weight is strictly positive inside the unit interval. -/
theorem weight_pos {s : ℝ} (hs : s ∈ Ioo 0 1) : 0 < weight s :=
  mul_pos (expNegInvGlue.pos_of_pos hs.1)
    (expNegInvGlue.pos_of_pos (sub_pos.mpr hs.2))

/-- The nonzero set of the pulse weight is exactly the open unit interval. -/
theorem support_weight : Function.support weight = Ioo 0 1 := by
  ext s
  change expNegInvGlue s * expNegInvGlue (1 - s) ≠ 0 ↔ 0 < s ∧ s < 1
  simp only [ne_eq, mul_eq_zero, expNegInvGlue.zero_iff_nonpos, not_or, not_le, sub_pos]

/-- The topological support of the pulse weight is the closed unit interval. -/
theorem tsupport_weight : tsupport weight = Icc 0 1 := by
  rw [tsupport, support_weight, closure_Ioo zero_ne_one]

/-- The pulse weight has compact support. -/
theorem hasCompactSupport_weight : HasCompactSupport weight := by
  change IsCompact (tsupport weight)
  rw [tsupport_weight]
  exact isCompact_Icc

/-- The pulse weight is Lebesgue integrable on the real line. -/
theorem integrable_weight : Integrable weight :=
  contDiff_weight.continuous.integrable_of_hasCompactSupport hasCompactSupport_weight

/-- Reflection about the midpoint preserves the pulse weight. -/
theorem weight_one_sub (s : ℝ) : weight (1 - s) = weight s := by
  simp only [weight, sub_sub_self, mul_comm]

/-- The Lebesgue mass of the pulse weight. -/
def mass : ℝ := ∫ s : ℝ, weight s

/-- The normalizing mass is strictly positive. -/
theorem mass_pos : 0 < mass := by
  have hmid : 0 < weight ((1 : ℝ) / 2) :=
    weight_pos ⟨half_pos zero_lt_one, half_lt_self zero_lt_one⟩
  exact integral_pos_of_integrable_nonneg_nonzero contDiff_weight.continuous
    integrable_weight weight_nonneg hmid.ne'

/-- The unit-mass pulse obtained by dividing the glue product by its Lebesgue mass. -/
def density (s : ℝ) : ℝ := weight s / mass

/-- The normalized pulse is infinitely differentiable on the whole real line. -/
theorem contDiff_density : ContDiff ℝ ∞ density :=
  contDiff_weight.div_const mass

/-- The normalized pulse is nonnegative everywhere. -/
theorem density_nonneg (s : ℝ) : 0 ≤ density s :=
  div_nonneg (weight_nonneg s) mass_pos.le

/-- The normalized pulse is strictly positive inside the unit interval. -/
theorem density_pos {s : ℝ} (hs : s ∈ Ioo 0 1) : 0 < density s :=
  div_pos (weight_pos hs) mass_pos

/-- Normalization preserves the exact nonzero set of the pulse. -/
theorem support_density : Function.support density = Ioo 0 1 := by
  calc
    Function.support density = Function.support weight := by
      ext s
      change weight s / mass ≠ 0 ↔ weight s ≠ 0
      exact ⟨fun h ↦ (div_ne_zero_iff.mp h).1, fun h ↦ div_ne_zero h mass_pos.ne'⟩
    _ = Ioo 0 1 := support_weight

/-- The normalized pulse has topological support exactly the closed unit interval. -/
theorem tsupport_density : tsupport density = Icc 0 1 := by
  rw [tsupport, support_density, closure_Ioo zero_ne_one]

/-- The normalized pulse has compact support. -/
theorem hasCompactSupport_density : HasCompactSupport density := by
  change IsCompact (tsupport density)
  rw [tsupport_density]
  exact isCompact_Icc

/-- The normalized pulse is Lebesgue integrable. -/
theorem integrable_density : Integrable density :=
  contDiff_density.continuous.integrable_of_hasCompactSupport hasCompactSupport_density

/-- The normalized pulse has Lebesgue integral one. -/
theorem integral_density : ∫ s : ℝ, density s = 1 := by
  change (∫ s : ℝ, weight s / mass) = 1
  rw [integral_div]
  exact div_self mass_pos.ne'

/-- Reflection about the midpoint preserves the normalized pulse. -/
theorem density_one_sub (s : ℝ) : density (1 - s) = density s := by
  simp only [density, weight_one_sub]

/-- The first-moment integrand of the normalized pulse is integrable. -/
theorem integrable_mul_density : Integrable (fun s : ℝ ↦ s * density s) :=
  (continuous_id.mul contDiff_density.continuous).integrable_of_hasCompactSupport
    (hasCompactSupport_density.mul_left (f := fun s : ℝ ↦ s))

/-- The normalized pulse has first moment one half. -/
theorem integral_mul_density : ∫ s : ℝ, s * density s = (1 : ℝ) / 2 := by
  have hreflect :=
    integral_sub_left_eq_self (fun s : ℝ ↦ s * density s) volume (1 : ℝ)
  simp only [density_one_sub, sub_mul, one_mul] at hreflect
  rw [integral_sub integrable_density integrable_mul_density, integral_density] at hreflect
  apply (eq_div_iff (two_ne_zero : (2 : ℝ) ≠ 0)).2
  rw [mul_two]
  exact (sub_eq_iff_eq_add.mp hreflect).symm

end PDE.Analysis.NormalizedPulse
