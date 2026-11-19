/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import CAS.ExactTactic

/-!
# Explicit exponential majorants for polynomial weights

The exponential series bounds a monomial with an explicit factorial constant.
Allowing a shift in the polynomial and reserving part of the exponential decay gives
a bound useful for Gaussian tails after substituting `x = t²`. In the other direction,
`four_add_sq_add_le_two_add_exp_add_exp_neg` bounds `2 + eˢ + e⁻ˢ = 2 + 2 cosh s` below by its
Taylor polynomial of degree four.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

/-- A shifted polynomial times a decaying exponential has an explicit global bound.
Only the base of the polynomial, `b + x`, must be nonnegative. -/
theorem add_pow_mul_exp_neg_mul_le {b c x : ℝ} (hc : 0 < c)
    (hx : 0 ≤ b + x) (p : ℕ) :
    (b + x) ^ p * Real.exp (-c * x) ≤
      ((p.factorial : ℝ) / c ^ p) * Real.exp (c * b) := by
  have hfac : (0 : ℝ) < p.factorial := by exact_mod_cast Nat.factorial_pos p
  have hb := (div_le_iff₀ hfac).mp
    (Real.pow_div_factorial_le_exp (c * (b + x)) (mul_nonneg hc.le hx) p)
  have hp : 0 < c ^ p := pow_pos hc p
  calc
    _ = ((c * (b + x)) ^ p / c ^ p) * Real.exp (-c * x) := by
      rw [mul_pow, mul_div_cancel_left₀ _ hp.ne']
    _ ≤ (Real.exp (c * (b + x)) * p.factorial / c ^ p) * Real.exp (-c * x) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hb hp.le) (Real.exp_pos _).le
    _ = (p.factorial / c ^ p) *
        (Real.exp (c * (b + x)) * Real.exp (-c * x)) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      cas

/-- Any strict loss in the exponential rate absorbs a shifted polynomial, while leaving
an explicit decaying exponential on the right. No sign condition on `d` is needed. -/
theorem add_pow_mul_exp_neg_mul_le_exp {b c d x : ℝ} (hdc : d < c)
    (hx : 0 ≤ b + x) (p : ℕ) :
    (b + x) ^ p * Real.exp (-c * x) ≤
      ((p.factorial : ℝ) / (c - d) ^ p) * Real.exp ((c - d) * b) *
        Real.exp (-d * x) := by
  have hsplit : -c * x = -(c - d) * x + -d * x := by cas
  rw [hsplit, Real.exp_add, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (add_pow_mul_exp_neg_mul_le (sub_pos.mpr hdc) hx p) (Real.exp_pos _).le

/-- The degree-four Taylor polynomial bounds `2 + eˢ + e⁻ˢ` from below:
`4 + s² + s⁴/12 ≤ 2 + eˢ + e⁻ˢ`. -/
theorem four_add_sq_add_le_two_add_exp_add_exp_neg (s : ℝ) :
    4 + s ^ 2 + s ^ 4 / 12 ≤ 2 + Real.exp s + Real.exp (-s) := by
  have h := Summable.sum_le_tsum (Finset.range 3)
    (fun i _ ↦ div_nonneg
      (by rw [pow_mul]; exact pow_nonneg (sq_nonneg s) i) (Nat.cast_nonneg _))
    (Real.hasSum_cosh s).summable
  rw [← Real.cosh_eq_tsum] at h
  norm_num [Finset.sum_range_succ, Real.cosh_eq] at h
  linarith

end PDE.Analysis
