/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Oscillation of primitives of integrable functions

The difference between two values of an oriented primitive is an integral
over the interval between them. Its norm is bounded by the global integral
of the norm, with no ordering or support hypothesis.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.Analysis

/-- An integrable function has a primitive whose oscillation is bounded
by its global `L¹` norm. The base point and both endpoints are arbitrary. -/
theorem norm_intervalIntegral_sub_le_integral_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : Integrable f volume) (a x y : ℝ) :
    ‖(∫ s in a..x, f s) - ∫ s in a..y, f s‖ ≤ ∫ s, ‖f s‖ := by
  rw [intervalIntegral.integral_interval_sub_left hf.intervalIntegrable hf.intervalIntegrable]
  exact intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
    (setIntegral_le_integral hf.norm (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _))

/-- The primitive from negative infinity differs from any oriented primitive
by its value at the base point. -/
theorem integral_Iio_eq_intervalIntegral_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : Integrable f volume) (a x : ℝ) :
    (∫ s in Iio x, f s) = (∫ s in a..x, f s) + ∫ s in Iio a, f s := by
  have h := intervalIntegral.integral_Iic_sub_Iic
    (hf.integrableOn (s := Iic a)) (hf.integrableOn (s := Iic x))
  simp only [integral_Iic_eq_integral_Iio] at h
  exact eq_add_of_sub_eq h

/-- The primitive from negative infinity of an integrable function is
continuous, including at points where the integrand is discontinuous. -/
theorem continuous_integral_Iio
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : Integrable f volume) :
    Continuous (fun x : ℝ ↦ ∫ s in Iio x, f s) := by
  have heq : (fun x : ℝ ↦ ∫ s in Iio x, f s) =
      fun x ↦ (∫ s in (0 : ℝ)..x, f s) + ∫ s in Iio (0 : ℝ), f s :=
    funext (integral_Iio_eq_intervalIntegral_add hf 0)
  rw [heq]
  exact (hf.continuous_primitive 0).add continuous_const

/-- To the left of an almost-everywhere support interval, the primitive
from negative infinity is zero. Values at the endpoints do not matter. -/
theorem integral_Iio_eq_zero_of_ae_support_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b x : ℝ}
    (hsupport : ∀ᵐ y ∂volume, y ∉ Icc a b → f y = 0) (hx : x ≤ a) :
    (∫ y in Iio x, f y) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_of_ae hsupport, ae_restrict_mem measurableSet_Iio] with y hy hyx
  exact hy (fun hyab ↦ (not_lt_of_ge hyab.1) (hyx.trans_le hx))

/-- To the right of an almost-everywhere support interval, the tail
integral is zero. -/
theorem integral_Ioi_eq_zero_of_ae_support_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b x : ℝ}
    (hsupport : ∀ᵐ y ∂volume, y ∉ Icc a b → f y = 0) (hx : b ≤ x) :
    (∫ y in Ioi x, f y) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_of_ae hsupport, ae_restrict_mem measurableSet_Ioi] with y hy hyx
  exact hy (fun hyab ↦ (not_lt_of_ge hyab.2) (hx.trans_lt hyx))

/-- Beyond an almost-everywhere support interval, the primitive has reached
the total integral. No pointwise support representative is selected. -/
theorem integral_Iio_eq_integral_of_ae_support_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : Integrable f volume) {a b x : ℝ}
    (hsupport : ∀ᵐ y ∂volume, y ∉ Icc a b → f y = 0) (hx : b ≤ x) :
    (∫ y in Iio x, f y) = ∫ y, f y := by
  have h := intervalIntegral.integral_Iic_add_Ioi
    (hf.integrableOn (s := Iic x)) (hf.integrableOn (s := Ioi x))
  simpa only [integral_Iic_eq_integral_Iio,
    integral_Ioi_eq_zero_of_ae_support_Icc hsupport hx, add_zero] using h

/-- An integrable scalar function supported almost everywhere in a closed
interval has an actual globally minimizing primitive value in that interval. -/
theorem exists_isMinOn_integral_Iio_of_ae_support_Icc
    {f : ℝ → ℝ} (hf : Integrable f volume) {a b : ℝ} (hab : a ≤ b)
    (hsupport : ∀ᵐ y ∂volume, y ∉ Icc a b → f y = 0) :
    ∃ z ∈ Icc a b, ∀ x : ℝ, (∫ y in Iio z, f y) ≤ ∫ y in Iio x, f y := by
  obtain ⟨z, hz, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr hab) (continuous_integral_Iio hf).continuousOn
  refine ⟨z, hz, fun x ↦ ?_⟩
  rcases lt_trichotomy x a with hxa | rfl | hax
  · have h := hmin ⟨le_rfl, hab⟩
    simpa only [mem_ofPred_eq, integral_Iio_eq_zero_of_ae_support_Icc hsupport hxa.le,
      integral_Iio_eq_zero_of_ae_support_Icc hsupport le_rfl] using h
  · exact hmin ⟨le_rfl, hab⟩
  · by_cases hxb : x ≤ b
    · exact hmin ⟨hax.le, hxb⟩
    · have h := hmin ⟨hab, le_rfl⟩
      simpa only [mem_ofPred_eq,
        integral_Iio_eq_integral_of_ae_support_Icc hf hsupport (le_of_not_ge hxb),
        integral_Iio_eq_integral_of_ae_support_Icc hf hsupport le_rfl] using h

end PDE.Analysis
