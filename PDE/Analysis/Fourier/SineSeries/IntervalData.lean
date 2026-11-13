/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import Mathlib.Analysis.PSeries
import CAS.ExactTactic
public import PDE.Analysis.Fourier.SineSeries.IntervalLp

/-!
# Sine reconstruction from interval smoothness

Two integrations by parts on `[0, 1]` give quadratic decay of the sine
coefficients of arbitrary `C²` data with zero endpoint values. Fourier completeness
then reconstructs the data. Smoothness is required only on the closed interval;
the odd reflection need only be continuous.
-/

@[expose] public section

namespace PDE.Analysis.Fourier.SineSeries

open MeasureTheory Set

/-- Twice integrating a sine coefficient by parts eliminates both boundary terms.
The second derivative is the iterated derivative within the closed interval. -/
theorem integral_sine_eq_neg_second_derivative {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ 2 g (Icc 0 1)) (hzero : g 0 = 0) (hone : g 1 = 0) (k : ℤ) :
    ((k : ℝ) * Real.pi) ^ 2 *
        (∫ x in (0 : ℝ)..1, g x * Real.sin ((k : ℝ) * Real.pi * x)) =
      -(∫ x in (0 : ℝ)..1, derivWithin (derivWithin g (Icc 0 1)) (Icc 0 1) x *
        Real.sin ((k : ℝ) * Real.pi * x)) := by
  let w : ℝ := (k : ℝ) * Real.pi
  let g' := derivWithin g (Icc 0 1)
  let g'' := derivWithin g' (Icc 0 1)
  have hg' : ContDiffOn ℝ 1 g' (Icc 0 1) :=
    hg.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  have hg'' : ContinuousOn g'' (Icc 0 1) :=
    hg'.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  have hd (x : ℝ) (hx : x ∈ uIcc (0 : ℝ) 1) :
      HasDerivWithinAt g (g' x) (uIcc 0 1) x := by
    rw [uIcc_of_le zero_le_one] at hx ⊢
    exact (hg.differentiableOn (by norm_num) x hx).hasDerivWithinAt
  have hd' (x : ℝ) (hx : x ∈ uIcc (0 : ℝ) 1) :
      HasDerivWithinAt g' (g'' x) (uIcc 0 1) x := by
    rw [uIcc_of_le zero_le_one] at hx ⊢
    exact (hg'.differentiableOn (by norm_num) x hx).hasDerivWithinAt
  have hi' : IntervalIntegrable g' volume 0 1 :=
    (show ContinuousOn g' (uIcc 0 1) from by
      simpa only [uIcc_of_le zero_le_one] using hg'.continuousOn).intervalIntegrable
  have hi'' : IntervalIntegrable g'' volume 0 1 :=
    (show ContinuousOn g'' (uIcc 0 1) from by
      simpa only [uIcc_of_le zero_le_one] using hg'').intervalIntegrable
  have hcos (x : ℝ) : HasDerivAt (fun y ↦ Real.cos (w * y))
      (-w * Real.sin (w * x)) x := by cas
  have hsin (x : ℝ) : HasDerivAt (fun y ↦ Real.sin (w * y))
      (w * Real.cos (w * x)) x := by cas
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    hd (fun x _ ↦ (hcos x).hasDerivWithinAt) hi'
    ((show Continuous (fun x ↦ -w * Real.sin (w * x)) from by fun_prop).intervalIntegrable 0 1)
  have hparts' := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    hd' (fun x _ ↦ (hsin x).hasDerivWithinAt) hi''
    ((show Continuous (fun x ↦ w * Real.cos (w * x)) from by fun_prop).intervalIntegrable 0 1)
  have hcomm (f : ℝ → ℝ) (v : ℝ → ℝ) (c : ℝ) :
      (fun x ↦ f x * (c * v x)) = fun x ↦ c * (f x * v x) := by
    funext x
    ring
  rw [hcomm, intervalIntegral.integral_const_mul] at hparts hparts'
  have hw : Real.sin w = 0 := Real.sin_int_mul_pi k
  simp only [mul_one, mul_zero, Real.sin_zero, hw, hzero, hone, zero_mul,
    zero_sub, sub_zero] at hparts hparts'
  change w ^ 2 * (∫ x in (0 : ℝ)..1, g x * Real.sin (w * x)) =
    -(∫ x in (0 : ℝ)..1, g'' x * Real.sin (w * x))
  calc
    _ = w * (∫ x in (0 : ℝ)..1, g' x * Real.cos (w * x)) := by
      have h := congrArg (fun z : ℝ ↦ -w * z) hparts
      nlinarith [h]
    _ = _ := hparts'

/-- The odd reflected function has summable complex Fourier coefficients, derived from
interval `C²` regularity and zero endpoint values. -/
theorem summable_fourierCoeff_oddIntervalMap {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ 2 g (Icc 0 1)) (hzero : g 0 = 0) (hone : g 1 = 0) :
    Summable (fourierCoeff (oddIntervalMap g hg.continuousOn hzero hone)) := by
  let g'' := derivWithin (derivWithin g (Icc 0 1)) (Icc 0 1)
  have hdc : ContDiffOn ℝ 1 (derivWithin g (Icc 0 1)) (Icc 0 1) :=
    hg.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hdc.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one (by norm_num))
  have hdecay (k : ℤ) (hk : k ≠ 0) :
      ‖fourierCoeff (oddIntervalMap g hg.continuousOn hzero hone) k‖ ≤
        (M / Real.pi ^ 2) * (1 / (k : ℝ) ^ 2) := by
    have hbound : ‖∫ x in (0 : ℝ)..1, g'' x * Real.sin ((k : ℝ) * Real.pi * x)‖ ≤ M := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := 1) (C := M)
        (f := fun x ↦ g'' x * Real.sin ((k : ℝ) * Real.pi * x)) ?_
      · simpa using h
      · intro x hx
        simp only [uIoc_of_le zero_le_one, mem_Ioc] at hx
        calc
          _ ≤ ‖g'' x‖ * 1 := by
            rw [norm_mul]
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            simpa only [Real.norm_eq_abs] using
              (Real.abs_sin_le_one ((k : ℝ) * Real.pi * x))
          _ ≤ M := by simpa only [mul_one] using hM x ⟨hx.1.le, hx.2⟩
    have hw : 0 < ((k : ℝ) * Real.pi) ^ 2 :=
      sq_pos_of_ne_zero (mul_ne_zero (Int.cast_ne_zero.mpr hk) Real.pi_ne_zero)
    have hparts := congrArg norm (integral_sine_eq_neg_second_derivative hg hzero hone k)
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), norm_neg] at hparts
    rw [fourierCoeff_oddIntervalMap, norm_mul, norm_neg, Complex.norm_I, one_mul,
      Complex.norm_real]
    calc
      _ ≤ M / ((k : ℝ) * Real.pi) ^ 2 := (le_div_iff₀ hw).mpr (by
        rw [mul_comm, hparts]
        exact hbound)
      _ = (M / Real.pi ^ 2) * (1 / (k : ℝ) ^ 2) := by ring
  apply ((Real.summable_one_div_int_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left
    (M / Real.pi ^ 2)).of_norm_bounded_eventually
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with k hk
  exact hdecay k hk

/-- Arbitrary interval `C²` Dirichlet data have absolutely summable sine coefficients. -/
theorem summable_norm_intervalCoefficient {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ 2 g (Icc 0 1)) (hzero : g 0 = 0) (hone : g 1 = 0) :
    Summable (fun n ↦ ‖intervalCoefficient g n‖) := by
  simpa only [coefficient_oddIntervalMap] using
    summable_norm_coefficient (summable_fourierCoeff_oddIntervalMap hg hzero hone)

/-- Fourier completeness reconstructs interval `C²` Dirichlet data from their sine
integrals. No Fourier expansion or summability is assumed. -/
theorem hasSum_intervalCoefficient_sineMode {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ 2 g (Icc 0 1)) (hzero : g 0 = 0) (hone : g 1 = 0)
    {x : ℝ} (hx : x ∈ Icc 0 1) :
    HasSum (fun n ↦ intervalCoefficient g n *
      PDE.Representations.intervalDirichletSineMode n x) (g x) := by
  simpa only [coefficient_oddIntervalMap, oddRealPart_oddIntervalMap hg.continuousOn hzero hone hx]
    using hasSum_coefficient_sineMode (summable_fourierCoeff_oddIntervalMap hg hzero hone) x

end PDE.Analysis.Fourier.SineSeries
