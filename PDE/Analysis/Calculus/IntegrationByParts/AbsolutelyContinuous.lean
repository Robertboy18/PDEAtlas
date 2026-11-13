/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Compact testing of absolutely continuous functions

Absolute continuity on bounded intervals suffices for integration by parts
against a compactly supported C¹ test. On a half-line, the initial value
survives with the negative outward-normal sign.
-/

@[expose] public section

open MeasureTheory Set Function

namespace PDE.Analysis

/-- Compact testing of a locally absolutely continuous function on the real line. -/
theorem integral_deriv_mul_eq_neg_of_absolutelyContinuous
    {f φ : ℝ → ℝ} (hf : ∀ a b, AbsolutelyContinuousOnInterval f a b)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    (∫ x, deriv f x * φ x) = -(∫ x, f x * deriv φ x) := by
  obtain ⟨r, _hr, hs⟩ := hc.isBounded.subset_ball_lt (0 : ℝ) (0 : ℝ)
  rw [Real.ball_zero_eq_Ioo] at hs
  have hleft : support (fun x ↦ deriv f x * φ x) ⊆ Ioc (-r) r :=
    (support_mul_subset_right _ _).trans ((subset_tsupport φ).trans hs |>.trans
      Ioo_subset_Ioc_self)
  have hright : support (fun x ↦ f x * deriv φ x) ⊆ Ioc (-r) r :=
    (support_mul_subset_right _ _).trans
      (support_deriv_subset.trans hs |>.trans Ioo_subset_Ioc_self)
  have hends : φ (-r) = 0 ∧ φ r = 0 := by
    constructor
    · by_contra h
      exact (lt_irrefl (-r)) (hs (subset_tsupport φ h)).1
    · by_contra h
      exact (lt_irrefl r) (hs (subset_tsupport φ h)).2
  have hp := (hf (-r) r).integral_mul_deriv_eq_deriv_mul
    (hφ.contDiffOn.absolutelyContinuousOnInterval)
  rw [hends.1, hends.2, mul_zero, mul_zero, sub_self, zero_sub] at hp
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hleft,
    ← intervalIntegral.integral_eq_integral_of_support_subset hright]
  linarith

/-- Half-line compact testing retains the actual value at the finite boundary. -/
theorem integral_Ioi_deriv_mul_eq_of_absolutelyContinuous
    {f φ : ℝ → ℝ} (hf : ∀ a b, AbsolutelyContinuousOnInterval f a b)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (a : ℝ) :
    (∫ x in Ioi a, deriv f x * φ x) =
      -f a * φ a - ∫ x in Ioi a, f x * deriv φ x := by
  obtain ⟨r, hr, hs⟩ := hc.isBounded.subset_ball_lt (|a| + 1) (0 : ℝ)
  rw [Real.ball_zero_eq_Ioo] at hs
  have har : a ≤ r := by linarith [le_abs_self a]
  have hφr : φ r = 0 := by
    by_contra h
    exact (lt_irrefl r) (hs (subset_tsupport φ h)).2
  have hcut (k : ℝ → ℝ) (hk : support k ⊆ Ioo (-r) r) :
      (∫ x in Ioi a, k x) = ∫ x in a..r, k x := by
    rw [intervalIntegral.integral_of_le har]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      Ioc_subset_Ioi_self
    intro x hx
    by_contra h
    exact hx.2 ⟨hx.1, (hk h).2.le⟩
  rw [hcut _ ((support_mul_subset_right _ _).trans ((subset_tsupport φ).trans hs)),
    hcut _ ((support_mul_subset_right _ _).trans (support_deriv_subset.trans hs))]
  have hp := (hf a r).integral_mul_deriv_eq_deriv_mul
    (hφ.contDiffOn.absolutelyContinuousOnInterval)
  rw [hφr, mul_zero] at hp
  linarith

end PDE.Analysis
