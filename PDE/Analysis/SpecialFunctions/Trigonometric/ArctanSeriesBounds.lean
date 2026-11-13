/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Partial sums of the arctangent series

For `x ≥ 0` the partial sum `∑_{k<n} (-1)^k x^(2k+1) / (2k+1)` of the arctangent series is within
`x^(2n+1) / (2n+1)` of `arctan x` (`abs_arctan_sub_arctanPartialSum_le`): the difference is the
integral of `(-t²)^n / (1 + t²)` over `[0, x]`, by the geometric sum of `1 / (1 + t²)`.
-/

@[expose] public section

namespace Real

open intervalIntegral Finset

/-- The partial sum `∑_{k<n} (-1)^k x^(2k+1) / (2k+1)` of the arctangent series. -/
noncomputable def arctanPartialSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range n, (-1) ^ k * x ^ (2 * k + 1) / (2 * k + 1)

private theorem inv_one_add_sq_eq (n : ℕ) (t : ℝ) :
    (1 + t ^ 2)⁻¹ = ∑ k ∈ range n, (-1) ^ k * t ^ (2 * k) + (-t ^ 2) ^ n / (1 + t ^ 2) := by
  have hpos : (1 + t ^ 2) ≠ 0 := by positivity
  have hg := geom_sum_mul (-t ^ 2) n
  have hk : ∑ k ∈ range n, (-1) ^ k * t ^ (2 * k) = ∑ k ∈ range n, (-t ^ 2) ^ k :=
    sum_congr rfl fun k _ ↦ by rw [pow_mul, ← mul_pow, neg_one_mul]
  have hS : ∑ k ∈ range n, (-t ^ 2) ^ k = (1 - (-t ^ 2) ^ n) / (1 + t ^ 2) := by
    rw [eq_div_iff hpos]
    linear_combination -hg
  rw [hk, hS]
  field_simp
  ring

/-- `arctan x` minus the partial sum is the integral of `(-t²)^n / (1 + t²)` over `[0, x]`. -/
theorem arctan_sub_arctanPartialSum (n : ℕ) (x : ℝ) :
    arctan x - arctanPartialSum n x = ∫ t in (0 : ℝ)..x, (-t ^ 2) ^ n / (1 + t ^ 2) := by
  have hcont : ∀ k : ℕ, IntervalIntegrable (fun t : ℝ ↦ (-1 : ℝ) ^ k * t ^ (2 * k))
      MeasureTheory.volume 0 x := fun k ↦
    (continuous_const.mul (continuous_pow _)).intervalIntegrable _ _
  have hr : IntervalIntegrable (fun t : ℝ ↦ (-t ^ 2) ^ n / (1 + t ^ 2)) MeasureTheory.volume 0 x :=
    (Continuous.div ((continuous_pow 2).neg.pow n) (by fun_prop : Continuous fun t : ℝ ↦ 1 + t ^ 2)
      fun t ↦ by positivity).intervalIntegrable _ _
  have hs : IntervalIntegrable (fun t : ℝ ↦ ∑ k ∈ range n, (-1 : ℝ) ^ k * t ^ (2 * k))
      MeasureTheory.volume 0 x :=
    (continuous_finsetSum _ fun k _ ↦ continuous_const.mul (continuous_pow _)).intervalIntegrable
      _ _
  have h := integral_inv_one_add_sq (a := 0) (b := x)
  rw [arctan_zero, sub_zero] at h
  rw [← h, show (fun t : ℝ ↦ ((1 : ℝ) + t ^ 2)⁻¹) = fun t ↦
      ∑ k ∈ range n, (-1) ^ k * t ^ (2 * k) + (-t ^ 2) ^ n / (1 + t ^ 2) from
      funext (inv_one_add_sq_eq n), integral_add hs hr, integral_finsetSum fun k _ ↦ hcont k,
    arctanPartialSum]
  have hk : ∀ k ∈ range n, ∫ t in (0 : ℝ)..x, (-1 : ℝ) ^ k * t ^ (2 * k) =
      (-1) ^ k * x ^ (2 * k + 1) / (2 * k + 1) := fun k _ ↦ by
    rw [integral_const_mul, integral_pow]
    push_cast
    ring
  rw [sum_congr rfl hk]
  ring

/-- **The arctangent series with its remainder.** For `x ≥ 0`,
`|arctan x - ∑_{k<n} (-1)^k x^(2k+1) / (2k+1)| ≤ x^(2n+1) / (2n+1)`. -/
theorem abs_arctan_sub_arctanPartialSum_le {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    |arctan x - arctanPartialSum n x| ≤ x ^ (2 * n + 1) / (2 * n + 1) := by
  rw [arctan_sub_arctanPartialSum]
  have hb : ∫ t in (0 : ℝ)..x, t ^ (2 * n) = x ^ (2 * n + 1) / (2 * n + 1) := by
    rw [integral_pow]
    push_cast
    ring
  rw [← hb]
  refine (abs_integral_le_integral_abs hx).trans (integral_mono_on hx ?_ ?_ fun t ht ↦ ?_)
  · exact ((Continuous.div ((continuous_pow 2).neg.pow n)
      (by fun_prop : Continuous fun t : ℝ ↦ 1 + t ^ 2) fun t ↦ by positivity).abs
      ).intervalIntegrable _ _
  · exact (continuous_pow _).intervalIntegrable _ _
  · have h1 : 0 < 1 + t ^ 2 := by positivity
    rw [abs_div, abs_of_pos h1, abs_pow, abs_neg, abs_pow, abs_of_nonneg ht.1, ← pow_mul]
    exact div_le_self (pow_nonneg ht.1 _) (by nlinarith [sq_nonneg t])

end Real
