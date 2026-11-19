/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Grönwall inequalities with a variable coefficient

For `k` continuous on `[a, b]` and of either sign, `e' ≤ k e` on `[a, b)` gives
`e(t) ≤ e(a) exp(∫ₐᵗ k)`, by the integrating factor `exp(-∫ₐᵗ k)`. For `k ≥ 0`,
applying this to the primitive majorant `δ + ∫ₐᵗ k e` turns the integral
inequality `e(t) ≤ δ + ∫ₐᵗ k e` into `e(t) ≤ δ exp(∫ₐᵗ k)`. Neither `e` nor `δ`
needs to be nonnegative.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set

namespace PDE.Analysis.Evolution

/-- Differential Grönwall with a continuous, possibly signed, time-dependent coefficient:
if `e' ≤ k e` on `[a, b)`, then `e(t) ≤ e(a) exp(∫ₐᵗ k)`. The derivatives are taken
within `[a, b]` at the points of `[a, b)`. -/
theorem le_mul_exp_integral_of_hasDerivWithinAt_le
    {e de k : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (he : ContinuousOn e (Icc a b)) (hk : ContinuousOn k (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt e (de t) (Icc a b) t)
    (hbound : ∀ t ∈ Ico a b, de t ≤ k t * e t) :
    ∀ t ∈ Icc a b, e t ≤ e a * Real.exp (∫ s in a..t, k s) := by
  let I : ℝ → ℝ := fun t ↦ ∫ s in a..t, k s
  have hI : ContinuousOn I (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      intervalIntegral.continuousOn_primitive_interval'
        (hk.intervalIntegrable_of_Icc hab) left_mem_uIcc
  have hId (t : ℝ) (ht : t ∈ Ico a b) :
      HasDerivWithinAt I (k t) (Icc a b) t := by
    have htI := Ico_subset_Icc_self ht
    let : Fact (t ∈ Icc a b) := ⟨htI⟩
    exact intervalIntegral.integral_hasDerivWithinAt_right
      ((hk.mono (Icc_subset_Icc_right ht.2.le)).intervalIntegrable_of_Icc ht.1)
      (hk.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hk t htI)
  let F : ℝ → ℝ := fun t ↦ e t * Real.exp (-I t)
  let dF : ℝ → ℝ := fun t ↦
    de t * Real.exp (-I t) + e t * (Real.exp (-I t) * -k t)
  have hFd (t : ℝ) (ht : t ∈ Ico a b) :
      HasDerivWithinAt F (dF t) (Ici t) t :=
    ((hd t ht).mul (hId t ht).neg.exp).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  have hFbound : ∀ t ∈ Icc a b, F t ≤ e a := by
    have h := le_gronwallBound_of_liminf_deriv_right_le
      (f := F) (f' := dF) (δ := e a) (K := 0) (ε := 0)
      (he.mul (Real.continuous_exp.comp_continuousOn hI.neg))
      (fun t ht _ hr ↦ (hFd t ht).liminf_right_slope_le hr)
      (by simp [F, I]) (fun t ht ↦ by
        have hs := mul_le_mul_of_nonneg_right (hbound t ht) (Real.exp_pos (-I t)).le
        dsimp [dF]
        nlinarith)
    simpa only [gronwallBound_ε0, zero_mul, Real.exp_zero, mul_one] using h
  intro t ht
  have h := hFbound t ht
  change e t * Real.exp (-I t) ≤ e a at h
  rw [Real.exp_neg, ← div_eq_mul_inv] at h
  exact (div_le_iff₀ (Real.exp_pos (I t))).mp h

/-- Integral Grönwall with a continuous nonnegative coefficient:
`e(t) ≤ δ + ∫ₐᵗ k(s)e(s) ds` implies `e(t) ≤ δ exp(∫ₐᵗ k)`.
No sign assumption is imposed on `e` or `δ`. -/
theorem le_mul_exp_integral_of_le_const_add_intervalIntegral
    {e k : ℝ → ℝ} {a b δ : ℝ} (hab : a ≤ b)
    (he : ContinuousOn e (Icc a b)) (hk : ContinuousOn k (Icc a b))
    (hk_nonneg : ∀ t ∈ Icc a b, 0 ≤ k t)
    (hbound : ∀ t ∈ Icc a b, e t ≤ δ + ∫ s in a..t, k s * e s) :
    ∀ t ∈ Icc a b, e t ≤ δ * Real.exp (∫ s in a..t, k s) := by
  let F : ℝ → ℝ := fun t ↦ δ + ∫ s in a..t, k s * e s
  have hke : ContinuousOn (fun t ↦ k t * e t) (Icc a b) := hk.mul he
  have hF : ContinuousOn F (Icc a b) := by
    exact continuousOn_const.add (by
      simpa only [uIcc_of_le hab] using
        intervalIntegral.continuousOn_primitive_interval'
          (hke.intervalIntegrable_of_Icc hab) left_mem_uIcc)
  have hFd (t : ℝ) (ht : t ∈ Ico a b) :
      HasDerivWithinAt F (k t * e t) (Icc a b) t := by
    have htI := Ico_subset_Icc_self ht
    let : Fact (t ∈ Icc a b) := ⟨htI⟩
    exact (intervalIntegral.integral_hasDerivWithinAt_right
      ((hke.mono (Icc_subset_Icc_right ht.2.le)).intervalIntegrable_of_Icc ht.1)
      (hke.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t)
      (hke t htI)).const_add δ
  have hmajorant := le_mul_exp_integral_of_hasDerivWithinAt_le hab hF hk hFd
    (fun t ht ↦ mul_le_mul_of_nonneg_left (hbound t (Ico_subset_Icc_self ht))
      (hk_nonneg t (Ico_subset_Icc_self ht)))
  intro t ht
  exact (hbound t ht).trans (by
    simpa only [F, intervalIntegral.integral_same, add_zero] using hmajorant t ht)

end PDE.Analysis.Evolution
