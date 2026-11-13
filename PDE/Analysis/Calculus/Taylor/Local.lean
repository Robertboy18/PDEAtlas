/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Taylor
import CAS.ExactTactic

/-!
# Local Taylor bounds from continuous derivatives

Compactness supplies the derivative bound on the unit interval. The unordered
interval in Taylor's theorem treats positive and negative increments together.
No bound on derivatives outside this interval is required.
-/

@[expose] public noncomputable section

open Set

namespace PDE.Analysis

/-- A continuous derivative of order `n + 1` gives a uniform Taylor remainder
bound for both signs of the increment from zero. -/
theorem exists_abs_sub_taylor_le_pow
    {f : ℝ → ℝ} {n : ℕ} (hf : ContDiff ℝ (n + 1) f) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u : ℝ, |u| ≤ 1 →
      |f u - taylorWithinEval f n (uIcc 0 u) 0 u| ≤ A * |u| ^ (n + 1) := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (hf.continuous_iteratedDeriv (n + 1) le_rfl).continuousOn
  refine ⟨max 0 B, le_max_left _ _, fun u hu ↦ ?_⟩
  by_cases hu0 : u = 0
  · simp [hu0]
  obtain ⟨z, hz, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := n) (Ne.symm hu0) hf.contDiffOn
  have hz' : z ∈ Icc (-1 : ℝ) 1 := by
    have hu' := abs_le.mp hu
    exact ⟨(le_min (by norm_num) hu'.1).trans hz.1.le,
      hz.2.le.trans (max_le (by norm_num) hu'.2)⟩
  have hb : |iteratedDeriv (n + 1) f z| ≤ max 0 B :=
    (hB z hz').trans (le_max_right _ _)
  rw [heq, abs_div, abs_mul, abs_pow, sub_zero,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (n + 1).factorial)]
  calc
    |iteratedDeriv (n + 1) f z| * |u| ^ (n + 1) / ↑(n + 1).factorial
        ≤ |iteratedDeriv (n + 1) f z| * |u| ^ (n + 1) :=
      div_le_self (mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _))
        (by exact_mod_cast Nat.succ_le_iff.mpr (Nat.factorial_pos (n + 1)))
    _ ≤ max 0 B * |u| ^ (n + 1) :=
      mul_le_mul_of_nonneg_right hb (pow_nonneg (abs_nonneg _) _)

/-- The first-order Taylor error is quadratic near zero. -/
theorem exists_abs_sub_linear_le_sq
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u : ℝ, |u| ≤ 1 →
      |f u - f 0 - deriv f 0 * u| ≤ A * u ^ 2 := by
  obtain ⟨A, hA, hbound⟩ := exists_abs_sub_taylor_le_pow (n := 1) hf
  refine ⟨A, hA, fun u hu ↦ ?_⟩
  by_cases hu0 : u = 0
  · simp [hu0]
  have hpoly : taylorWithinEval f 1 (uIcc 0 u) 0 u = f 0 + u * deriv f 0 := by
    rw [show (1 : ℕ) = 0 + 1 by rfl, taylorWithinEval_succ,
      taylor_within_zero_eval, iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_uIcc (Ne.symm hu0)) (hf.of_le (by norm_num)).contDiffAt
        left_mem_uIcc]
    simp only [Nat.factorial_zero, Nat.cast_one, Nat.cast_zero, zero_add, one_mul,
      inv_one, sub_zero, pow_one, smul_eq_mul, iteratedDeriv_one]
  have heq : f u - f 0 - deriv f 0 * u = f u - (f 0 + u * deriv f 0) := by cas
  simpa only [hpoly, ← heq, show 1 + 1 = 2 from rfl, sq_abs] using hbound u hu

/-- The second-order Taylor error is cubic near zero. Only continuity of the
third derivative on a compact interval is used to choose the constant. -/
theorem exists_abs_sub_quadratic_le_cube
    {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u : ℝ, |u| ≤ 1 →
      |f u - f 0 - deriv f 0 * u - deriv (deriv f) 0 / 2 * u ^ 2|
        ≤ A * |u| ^ 3 := by
  obtain ⟨A, hA, hbound⟩ := exists_abs_sub_taylor_le_pow (n := 2) hf
  refine ⟨A, hA, fun u hu ↦ ?_⟩
  by_cases hu0 : u = 0
  · simp [hu0]
  have hpoly : taylorWithinEval f 2 (uIcc 0 u) 0 u =
      f 0 + u * deriv f 0 + u ^ 2 / 2 * deriv (deriv f) 0 := by
    rw [taylorWithinEval_succ f 1,
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (Ne.symm hu0))
        (hf.of_le (by norm_num)).contDiffAt left_mem_uIcc,
      taylorWithinEval_succ f 0,
      taylor_within_zero_eval,
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (Ne.symm hu0))
        (hf.of_le (by norm_num)).contDiffAt left_mem_uIcc]
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, Nat.factorial_zero,
      Nat.factorial_one, Nat.cast_one, Nat.cast_zero, zero_add, one_mul, inv_one,
      sub_zero, pow_one, smul_eq_mul]
    cas
  have heq : f u - f 0 - deriv f 0 * u - deriv (deriv f) 0 / 2 * u ^ 2 =
      f u - (f 0 + u * deriv f 0 + u ^ 2 / 2 * deriv (deriv f) 0) := by cas
  simpa only [hpoly, ← heq] using hbound u hu

end PDE.Analysis
