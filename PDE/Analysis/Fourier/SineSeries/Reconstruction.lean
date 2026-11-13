/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Fourier.AddCircle
public import PDE.Representations.SeparationOfVariables

/-!
# Recovering sine series from the Fourier basis

Pairing the positive and negative Fourier frequencies reconstructs the odd real part of
a continuous function of period two. Completeness comes from Mathlib's Fourier Hilbert
basis and its uniform reconstruction theorem.
-/

@[expose] public section

namespace PDE.Analysis.Fourier.SineSeries

open PDE.Representations

/-- The period `2` of the sine series is positive. -/
instance fact_zero_lt_two : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩

/-- The real sine coefficients of the odd real part of a function of period two.
The Fourier coefficients use normalized Haar measure, so positive and negative
frequencies contribute with opposite signs. -/
noncomputable def coefficient (f : C(AddCircle (2 : ℝ), ℂ)) (n : ℕ) : ℝ :=
  (fourierCoeff f (-(n.succ : ℤ))).im - (fourierCoeff f (n.succ : ℤ)).im

/-- Taking the odd real part of a complex periodic function produces real Dirichlet data. -/
noncomputable def oddRealPart (f : C(AddCircle (2 : ℝ), ℂ)) (x : ℝ) : ℝ :=
  ((f (x : AddCircle (2 : ℝ))).re - (f ((-x : ℝ) : AddCircle (2 : ℝ))).re) / 2

/-- Absolute summability passes from complex Fourier coefficients to real sine coefficients. -/
theorem summable_norm_coefficient {f : C(AddCircle (2 : ℝ), ℂ)}
    (hf : Summable (fourierCoeff f)) :
    Summable (fun n ↦ ‖coefficient f n‖) := by
  have hp : Summable (fun n : ℕ ↦ fourierCoeff f (n.succ : ℤ)) :=
    hf.comp_injective (by intro n m h; simpa using h)
  have hn : Summable (fun n : ℕ ↦ fourierCoeff f (-(n.succ : ℤ))) :=
    hf.comp_injective (by intro n m h; simpa using h)
  exact ((Complex.hasSum_im hn.hasSum).summable.sub
    (Complex.hasSum_im hp.hasSum).summable).norm

private theorem fourier_two_eq (n : ℤ) (x : ℝ) :
    fourier n (x : AddCircle (2 : ℝ)) =
      Complex.exp (((n : ℝ) * Real.pi * x : ℝ) * Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

private theorem odd_fourier_term (c : ℂ) (n : ℤ) (x : ℝ) :
    ((c * fourier n (x : AddCircle (2 : ℝ))).re -
        (c * fourier n ((-x : ℝ) : AddCircle (2 : ℝ))).re) / 2 =
      -c.im * Real.sin ((n : ℝ) * Real.pi * x) := by
  rw [fourier_two_eq, fourier_two_eq]
  simp only [Complex.mul_re, Complex.exp_re, Complex.exp_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, add_zero, mul_one, Real.exp_zero, one_mul,
    mul_neg, Real.cos_neg, Real.sin_neg]
  ring

/-- The sine series reconstructs the odd real part pointwise. Its convergence follows
from Fourier completeness and coefficient summability. -/
theorem hasSum_coefficient_sineMode {f : C(AddCircle (2 : ℝ), ℂ)}
    (hf : Summable (fourierCoeff f)) (x : ℝ) :
    HasSum (fun n ↦ coefficient f n * intervalDirichletSineMode n x) (oddRealPart f x) := by
  have hx := (Complex.hasSum_re
    ((has_pointwise_sum_fourier_series_of_summable hf (x : AddCircle (2 : ℝ))).sub
      (has_pointwise_sum_fourier_series_of_summable hf
        ((-x : ℝ) : AddCircle (2 : ℝ))))).div_const 2
  have hodd : HasSum (fun n : ℤ ↦ -(fourierCoeff f n).im *
      Real.sin ((n : ℝ) * Real.pi * x)) (oddRealPart f x) := by
    simpa only [smul_eq_mul, Complex.sub_re, odd_fourier_term, oddRealPart] using hx
  have hpair := (hasSum_nat_add_iff' 1).mpr hodd.nat_add_neg
  simpa only [Finset.sum_range_one, Nat.cast_zero, Int.cast_zero, neg_zero,
    zero_mul, Real.sin_zero, mul_zero, add_zero, zero_add, sub_zero, Nat.cast_add, Nat.cast_one,
    Int.cast_add, Int.cast_natCast, Int.cast_one, Int.cast_neg, neg_mul, Real.sin_neg,
    mul_neg, neg_neg, coefficient, intervalDirichletSineMode, Nat.cast_succ,
    sub_mul, sub_eq_add_neg, add_mul, add_comm] using hpair

end PDE.Analysis.Fourier.SineSeries
