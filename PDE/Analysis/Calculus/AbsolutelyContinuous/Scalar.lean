/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Scalar comparison and powers of absolutely continuous curves

The fundamental theorem of calculus turns almost-everywhere derivative bounds
into bounds on increments. A positive monotone absolutely continuous curve can
be raised to any real power, including the negative powers used in blow-up arguments.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace PDE.Analysis

/-- An almost-everywhere lower bound on the derivative bounds the increment
of an absolutely continuous scalar curve. -/
theorem mul_sub_le_sub_of_ae_le_deriv
    {y : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hy : AbsolutelyContinuousOnInterval y a b)
    (hd : ∀ᵐ t ∂volume.restrict (Ioc a b), c ≤ deriv y t) :
    c * (b - a) ≤ y b - y a := by
  have h := intervalIntegral.integral_mono_ae_restrict hab
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ c) volume a b)
    hy.intervalIntegrable_deriv ((ae_restrict_congr_set Ioc_ae_eq_Icc).mp hd)
  rw [hy.integral_deriv_eq_sub, intervalIntegral.integral_const, smul_eq_mul] at h
  simpa only [mul_comm] using h

/-- A scalar absolutely continuous curve with nonnegative derivative almost
everywhere is monotone, including its endpoint traces. -/
theorem monotoneOn_of_absolutelyContinuous_of_ae_deriv_nonneg
    {y : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hy : AbsolutelyContinuousOnInterval y a b)
    (hd : ∀ᵐ t ∂volume.restrict (Ioc a b), 0 ≤ deriv y t) :
    MonotoneOn y (Icc a b) := by
  intro s hs t ht hst
  have hsub : uIcc s t ⊆ uIcc a b := by
    rw [uIcc_of_le hst, uIcc_of_le hab]
    exact Icc_subset_Icc hs.1 ht.2
  have hderiv : ∀ᵐ r ∂volume.restrict (Ioc s t), 0 ≤ deriv y r :=
    hd.filter_mono (MeasureTheory.ae_mono
      (Measure.restrict_mono_set _ (Ioc_subset_Ioc hs.1 ht.2)))
  have h := mul_sub_le_sub_of_ae_le_deriv hst (hy.mono hsub) hderiv
  simpa only [zero_mul, sub_nonneg] using h

/-- Any real power of a positive monotone absolutely continuous scalar curve
is absolutely continuous. Compactness keeps its values away from zero. -/
theorem absolutelyContinuous_rpow_of_pos_monotoneOn
    {y : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hy : AbsolutelyContinuousOnInterval y a b)
    (hm : MonotoneOn y (Icc a b)) (hpos : 0 < y a) (r : ℝ) :
    AbsolutelyContinuousOnInterval (fun t ↦ y t ^ r) a b := by
  have hsmooth : ContDiffOn ℝ 1 (fun s : ℝ ↦ s ^ r) (Icc (y a) (y b)) := by
    intro s hs
    exact (Real.contDiffAt_rpow_const_of_ne (hpos.trans_le hs.1).ne').contDiffWithinAt
  obtain ⟨K, hK⟩ := hsmooth.exists_lipschitzOnWith (by decide)
    (convex_Icc _ _) isCompact_Icc
  apply hK.comp_absolutelyContinuousOnInterval _ hy
  intro t ht
  rw [uIcc_of_le hab] at ht
  exact ⟨hm (left_mem_Icc.mpr hab) ht ht.1,
    hm ht (right_mem_Icc.mpr hab) ht.2⟩

end PDE.Analysis
