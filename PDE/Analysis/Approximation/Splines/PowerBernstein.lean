/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Bernstein coefficients of finite power polynomials

The binomial-ratio conversion preserves every finite power polynomial,
including degree zero. Nonnegativity and partition of unity then give
closed-interval bounds from its Bernstein coefficients.

## Main definitions

* `powerBernsteinCoefficients`: the coefficients of a power polynomial of degree at most `n` in
  the degree-`n` Bernstein basis.

## Main results

* `abs_sum_mul_bernstein_le`: if every Bernstein coefficient is at most `B` in absolute value,
  so is the polynomial on `[0, 1]`.
* `sum_choose_ratio_mul_bernstein`: `x ^ j = ∑_k (C(k, j) / C(n, j)) b_{n,k}(x)` for `j ≤ n`.
* `sum_powerBernsteinCoefficients`: the converted coefficients represent the original power
  polynomial.
* `abs_powerPolynomial_le`: a bound of every converted coefficient bounds the power polynomial on
  `[0, 1]`.
-/

@[expose] public noncomputable section

namespace CAS.Splines

open scoped BigOperators unitInterval

/-- For `j ≤ n`, the sum over `k ≤ n` of `f (k - j)` restricted to `j ≤ k` is the sum of `f` over `k
≤ n - j`. -/
private theorem sum_range_shift {M : Type*} [AddCommMonoid M]
    (n j : ℕ) (hj : j ≤ n) (f : ℕ → M) :
    (∑ k ∈ Finset.range (n + 1), if j ≤ k then f (k - j) else 0) =
      ∑ k ∈ Finset.range (n - j + 1), f k := by
  rw [show n + 1 = j + (n - j + 1) by omega, Finset.sum_range_add]
  have hz : (∑ k ∈ Finset.range j, if j ≤ k then f (k - j) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    exact ite_eq_right (Nat.not_le.mpr (Finset.mem_range.mp hk))
  rw [hz, zero_add]
  apply Finset.sum_congr rfl
  intro k _
  simp

/-- For `j ≤ k` and `j ≤ n`, `C(k, j) / C(n, j) · C(n, k) = C(n - j, k - j)`. -/
private theorem choose_ratio_mul (n j k : ℕ) (hj : j ≤ n) (hjk : j ≤ k) :
    ((k.choose j : ℝ) / (n.choose j : ℝ)) * (n.choose k : ℝ) =
      ((n - j).choose (k - j) : ℝ) := by
  have hn : (n.choose j : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hj).ne'
  have hm : (n.choose k : ℝ) * (k.choose j : ℝ) =
      (n.choose j : ℝ) * ((n - j).choose (k - j) : ℝ) := by
    exact_mod_cast Nat.choose_mul hjk
  rw [div_mul_eq_mul_div]
  apply (div_eq_iff hn).mpr
  simpa only [mul_comm] using hm

/-- For `j, k ≤ n`, `C(k, j) / C(n, j)` times the Bernstein polynomial `b_{n,k}` is `x^j
b_{n-j,k-j}` when `j ≤ k` and `0` otherwise. -/
private theorem ratio_mul_bernstein (n j k : ℕ) (hj : j ≤ n) (hk : k ≤ n) (x : I) :
    ((k.choose j : ℝ) / (n.choose j : ℝ)) * bernstein n k x =
      if j ≤ k then (x : ℝ) ^ j * bernstein (n - j) (k - j) x else 0 := by
  by_cases hjk : j ≤ k
  · rw [ite_eq_left hjk, bernstein_apply, bernstein_apply]
    have hp : (x : ℝ) ^ k = (x : ℝ) ^ j * (x : ℝ) ^ (k - j) := by
      calc
        _ = (x : ℝ) ^ (j + (k - j)) := congrArg _ (by omega)
        _ = _ := pow_add _ _ _
    have hq : n - k = (n - j) - (k - j) := by omega
    calc
      _ = (((k.choose j : ℝ) / (n.choose j : ℝ)) * (n.choose k : ℝ)) *
          (x : ℝ) ^ k * (1 - (x : ℝ)) ^ (n - k) := by ring
      _ = _ := by rw [choose_ratio_mul n j k hj hjk, hp, hq]; ring
  · simp [hjk, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hjk)]

/-- Bernstein coefficient bounds imply a continuum bound, with no point sampling. -/
theorem abs_sum_mul_bernstein_le {n : ℕ} (coefficients : Fin (n + 1) → ℝ)
    (B : ℝ) (x : I) (hcoeff : ∀ k, |coefficients k| ≤ B) :
    |∑ k, coefficients k * bernstein n k x| ≤ B := by
  calc
    |∑ k, coefficients k * bernstein n k x| ≤
        ∑ k, |coefficients k * bernstein n k x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |coefficients k| * bernstein n k x := by
      simp only [abs_mul, abs_of_nonneg bernstein_nonneg]
    _ ≤ ∑ k : Fin (n + 1), B * bernstein n k x := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right (hcoeff k) bernstein_nonneg
    _ = B := by rw [← Finset.mul_sum, bernstein.probability, mul_one]

/-- Every monomial up to degree `n` has the binomial-ratio Bernstein expansion. -/
theorem sum_choose_ratio_mul_bernstein (n : ℕ) (j : Fin (n + 1)) (x : I) :
    (∑ k : Fin (n + 1),
      ((k.val.choose j.val : ℝ) / (n.choose j.val : ℝ)) * bernstein n k x) =
      (x : ℝ) ^ j.val := by
  have hj : j.val ≤ n := Nat.le_of_lt_succ j.isLt
  simp_rw [ratio_mul_bernstein n j.val _ hj (Nat.le_of_lt_succ (Fin.isLt _)) x]
  rw [← Finset.sum_range (fun k : ℕ ↦
    if j.val ≤ k then (x : ℝ) ^ j.val * bernstein (n - j.val) (k - j.val) x else 0)]
  rw [sum_range_shift n j.val hj
    (fun k ↦ (x : ℝ) ^ j.val * bernstein (n - j.val) k x)]
  rw [Finset.sum_range, ← Finset.mul_sum, bernstein.probability, mul_one]

/-- Coefficients in the degree-`n` Bernstein basis, indexed from zero through `n`. -/
def powerBernsteinCoefficients {n : ℕ} (coefficients : Fin (n + 1) → ℝ)
    (k : Fin (n + 1)) : ℝ :=
  ∑ j, coefficients j * ((k.val.choose j.val : ℝ) / (n.choose j.val : ℝ))

/-- The finite binomial-ratio conversion represents exactly the original power polynomial. -/
theorem sum_powerBernsteinCoefficients {n : ℕ} (coefficients : Fin (n + 1) → ℝ)
    (x : I) :
    (∑ k, powerBernsteinCoefficients coefficients k * bernstein n k x) =
      ∑ j, coefficients j * (x : ℝ) ^ j.val := by
  unfold powerBernsteinCoefficients
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, sum_choose_ratio_mul_bernstein]

/-- A bound on every Bernstein coefficient holds on the whole closed unit interval. -/
theorem abs_powerPolynomial_le {n : ℕ} (coefficients : Fin (n + 1) → ℝ)
    (bound : ℝ) (x : I)
    (hcoeff : ∀ k, |powerBernsteinCoefficients coefficients k| ≤ bound) :
    |∑ j, coefficients j * (x : ℝ) ^ j.val| ≤ bound := by
  rw [← sum_powerBernsteinCoefficients]
  exact abs_sum_mul_bernstein_le _ bound x hcoeff

end CAS.Splines
