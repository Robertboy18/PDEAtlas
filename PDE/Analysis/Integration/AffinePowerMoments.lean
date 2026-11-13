/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.PowerBernstein
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Moments of polynomials in two affine coordinates

Integrals over `[a, b]` of products of powers of two affine coordinates, and `L¹` bounds of power
polynomials from their Bernstein coefficients (`CAS.Splines.powerBernsteinCoefficients`). For the
pieces of a B-spline the Bernstein coefficients are nonnegative and the bound is the integral
itself, while the sum of the absolute power coefficients can exceed it by a factor `2^n`.

## Main results

* `integral_affine_pow_mul_chart_pow`:
  `∫_a^b ((x - c)/h)^s ((x - a)/(b - a))^m dx = (b - a) ∑_{i ≤ s} C(s, i) α^{s-i} β^i/(m + i + 1)`
  with `α = (a - c)/h`, `β = (b - a)/h`.
* `integral_bernsteinPolynomial`: `∫_0^1 b_{n,k} = 1/(n + 1)`, from the antiderivative
  `∑_{j > k} b_{n+1,j}/(n + 1)`.
* `integral_abs_chart_polynomial_le`: `∫_a^b |∑_{m ≤ n} X_m ((x - a)/(b - a))^m| dx` is at most
  `(b - a) ∑_k |β_k|/(n + 1)` with the Bernstein coefficients `β_k` of `X`.
* `integral_affine_pow_mul_affine_pow`: the moments of two affine coordinates on any interval
  `[x₀, x₁]`.
* `integral_abs_chart_polynomial_le_of_subinterval`: the Bernstein bound on a subinterval
  `[x₀, x₁] ⊆ [a, b]` when every Bernstein coefficient is at most `B` in absolute value.
-/

@[expose] public section

noncomputable section

open Finset MeasureTheory Set Polynomial
open scoped Interval unitInterval

namespace PDE.Analysis

/-- **Moments in two affine coordinates.** -/
theorem integral_affine_pow_mul_chart_pow {a b : ℝ} (hab : a ≠ b) (c h : ℝ) (s m : ℕ) :
    ∫ x in a..b, ((x - c) / h) ^ s * ((x - a) / (b - a)) ^ m =
      (b - a) * ∑ i ∈ range (s + 1), (s.choose i : ℝ) * ((a - c) / h) ^ (s - i) *
        ((b - a) / h) ^ i / (m + i + 1) := by
  have hw : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hsub := intervalIntegral.smul_integral_comp_add_mul
    (f := fun x : ℝ ↦ ((x - c) / h) ^ s * ((x - a) / (b - a)) ^ m) (a := 0) (b := 1) (b - a) a
  simp only [mul_zero, add_zero, mul_one, add_sub_cancel, smul_eq_mul] at hsub
  rw [← hsub]
  congr 1
  have hpt : ∀ u : ℝ, ((a + (b - a) * u - c) / h) ^ s * ((a + (b - a) * u - a) / (b - a)) ^ m =
      ∑ i ∈ range (s + 1), (s.choose i : ℝ) * ((a - c) / h) ^ (s - i) * ((b - a) / h) ^ i *
        u ^ (i + m) := by
    intro u
    have h1 : (a + (b - a) * u - a) / (b - a) = u := by field_simp; ring
    have h2 : (a + (b - a) * u - c) / h = (b - a) / h * u + (a - c) / h := by ring
    rw [h1, h2, add_pow, sum_mul]
    apply sum_congr rfl
    intro i _
    rw [mul_pow, pow_add]
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_finsetSum fun i _ ↦
    Continuous.intervalIntegrable (by fun_prop) 0 1]
  apply sum_congr rfl
  intro i _
  rw [intervalIntegral.integral_const_mul, integral_pow, one_pow, zero_pow (Nat.succ_ne_zero _),
    sub_zero]
  push_cast
  ring

/-- `∫_0^1 b_{n,k} = 1/(n + 1)` for `k ≤ n`. -/
theorem integral_bernsteinPolynomial (n k : ℕ) (hk : k ≤ n) :
    ∫ x in (0 : ℝ)..1, (bernsteinPolynomial ℝ n k).eval x = 1 / (n + 1) := by
  set G : ℝ[X] := ∑ j ∈ Finset.Ico (k + 1) (n + 2), bernsteinPolynomial ℝ (n + 1) j with hG
  have hderiv : Polynomial.derivative G = (n + 1 : ℝ[X]) * bernsteinPolynomial ℝ n k := by
    rw [hG, Polynomial.derivative_sum]
    have hsum : ∀ j ∈ Finset.Ico (k + 1) (n + 2),
        Polynomial.derivative (bernsteinPolynomial ℝ (n + 1) j) =
        (n + 1 : ℝ[X]) * (bernsteinPolynomial ℝ n (j - 1) - bernsteinPolynomial ℝ n j) := by
      intro j hj
      obtain ⟨hj1, _⟩ := Finset.mem_Ico.mp hj
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [bernsteinPolynomial.derivative_succ]
      push_cast
      simp
    rw [sum_congr rfl hsum, ← mul_sum]
    congr 1
    have htel : ∀ N, k ≤ N → ∑ j ∈ Finset.Ico (k + 1) (N + 2),
        (bernsteinPolynomial ℝ n (j - 1) - bernsteinPolynomial ℝ n j) =
          bernsteinPolynomial ℝ n k - bernsteinPolynomial ℝ n (N + 1) := by
      intro N hN
      induction N, hN using Nat.le_induction with
      | base => simp
      | succ N hN ih =>
        rw [sum_Ico_succ_top (by omega), ih]
        simp
    rw [htel n hk, bernsteinPolynomial.eq_zero_of_lt ℝ (by omega : n < n + 1), sub_zero]
  have hint : ∫ x in (0 : ℝ)..1, (bernsteinPolynomial ℝ n k).eval x =
      (G.eval 1 - G.eval 0) / (n + 1) := by
    have hne : (n + 1 : ℝ) ≠ 0 := by positivity
    rw [eq_div_iff hne, ← intervalIntegral.integral_mul_const,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x ↦ G.eval x)]
    · intro x _
      have := G.hasDerivAt x
      rw [hderiv] at this
      simpa [mul_comm] using this
    · exact ((bernsteinPolynomial ℝ n k).continuous.mul continuous_const).intervalIntegrable 0 1
  rw [hint, hG, Polynomial.eval_finsetSum, Polynomial.eval_finsetSum]
  simp only [bernsteinPolynomial.eval_at_1, bernsteinPolynomial.eval_at_0]
  rw [sum_eq_single (n + 1) (fun j _ hj ↦ by simp [hj]) (fun h ↦ (h (by simp; omega)).elim)]
  rw [sum_eq_zero (fun j hj ↦ by
    have := (Finset.mem_Ico.mp hj).1
    simp [show j ≠ 0 by omega])]
  simp

/-- **The Bernstein `L¹` bound** of a power polynomial in the chart `u = (x - a)/(b - a)`. -/
theorem integral_abs_chart_polynomial_le {a b : ℝ} (hab : a < b) {n : ℕ}
    (X : Fin (n + 1) → ℝ) :
    ∫ x in a..b, |∑ j, X j * ((x - a) / (b - a)) ^ j.val| ≤
      (b - a) * (∑ k, |CAS.Splines.powerBernsteinCoefficients X k|) / (n + 1) := by
  have hw : 0 < b - a := sub_pos.mpr hab
  have hsub := intervalIntegral.smul_integral_comp_add_mul
    (f := fun x : ℝ ↦ |∑ j, X j * ((x - a) / (b - a)) ^ j.val|) (a := 0) (b := 1) (b - a) a
  simp only [mul_zero, add_zero, mul_one, add_sub_cancel, smul_eq_mul] at hsub
  rw [← hsub, mul_div_assoc]
  gcongr
  have hu : ∀ u : ℝ, (a + (b - a) * u - a) / (b - a) = u := fun u ↦ by field_simp; ring
  simp_rw [hu]
  set B : ℝ → ℝ := fun u ↦ ∑ k : Fin (n + 1),
    |CAS.Splines.powerBernsteinCoefficients X k| * (bernsteinPolynomial ℝ n k).eval u
  have hle : ∀ u ∈ Icc (0 : ℝ) 1, |∑ j, X j * u ^ j.val| ≤ B u := by
    intro u hu
    have h := CAS.Splines.sum_powerBernsteinCoefficients X ⟨u, hu⟩
    simp only at h
    rw [← h]
    refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    apply sum_congr rfl
    intro k _
    rw [abs_mul, abs_of_nonneg (bernstein_nonneg (x := ⟨u, hu⟩))]
    rfl
  have hB : ∫ u in (0 : ℝ)..1, B u = (∑ k, |CAS.Splines.powerBernsteinCoefficients X k|) /
      (n + 1) := by
    simp only [B]
    rw [intervalIntegral.integral_finsetSum fun k _ ↦
      Continuous.intervalIntegrable (by fun_prop) 0 1, sum_div]
    apply sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_const_mul,
      integral_bernsteinPolynomial n k (Nat.le_of_lt_succ k.isLt)]
    ring
  rw [← hB]
  refine intervalIntegral.integral_mono_on zero_le_one ?_ ?_ hle
  · exact Continuous.intervalIntegrable (by fun_prop) 0 1
  · exact Continuous.intervalIntegrable (by simp only [B]; fun_prop) 0 1

/-- **Moments of two affine coordinates on any interval**: with `x = x₀ + (x₁ - x₀) u`,
`∫_{x₀}^{x₁} ((x - c)/h)^s ((x - a)/w)^m dx` is `(x₁ - x₀)` times
`∑_{i ≤ s} ∑_{k ≤ m} C(s, i) α^{s-i} β^i C(m, k) γ^{m-k} δ^k/(i + k + 1)` with
`α = (x₀ - c)/h`, `β = (x₁ - x₀)/h`, `γ = (x₀ - a)/w`, `δ = (x₁ - x₀)/w`. -/
theorem integral_affine_pow_mul_affine_pow {x₀ x₁ : ℝ} (c h a w : ℝ) (s m : ℕ) :
    ∫ x in x₀..x₁, ((x - c) / h) ^ s * ((x - a) / w) ^ m =
      (x₁ - x₀) * ∑ i ∈ range (s + 1), ∑ k ∈ range (m + 1),
        (s.choose i : ℝ) * ((x₀ - c) / h) ^ (s - i) * ((x₁ - x₀) / h) ^ i *
          ((m.choose k : ℝ) * ((x₀ - a) / w) ^ (m - k) * ((x₁ - x₀) / w) ^ k) /
            (i + k + 1) := by
  have hsub := intervalIntegral.smul_integral_comp_add_mul
    (f := fun x : ℝ ↦ ((x - c) / h) ^ s * ((x - a) / w) ^ m) (a := 0) (b := 1) (x₁ - x₀) x₀
  simp only [mul_zero, add_zero, mul_one, add_sub_cancel, smul_eq_mul] at hsub
  rw [← hsub]
  congr 1
  have hpt : ∀ u : ℝ, ((x₀ + (x₁ - x₀) * u - c) / h) ^ s * ((x₀ + (x₁ - x₀) * u - a) / w) ^ m =
      ∑ i ∈ range (s + 1), ∑ k ∈ range (m + 1),
        (s.choose i : ℝ) * ((x₀ - c) / h) ^ (s - i) * ((x₁ - x₀) / h) ^ i *
          ((m.choose k : ℝ) * ((x₀ - a) / w) ^ (m - k) * ((x₁ - x₀) / w) ^ k) * u ^ (i + k) := by
    intro u
    have h2 : (x₀ + (x₁ - x₀) * u - c) / h = (x₁ - x₀) / h * u + (x₀ - c) / h := by ring
    have h3 : (x₀ + (x₁ - x₀) * u - a) / w = (x₁ - x₀) / w * u + (x₀ - a) / w := by ring
    rw [h2, h3, add_pow, add_pow, sum_mul]
    apply sum_congr rfl
    intro i _
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    rw [mul_pow, mul_pow, pow_add]
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_finsetSum fun i _ ↦
    Continuous.intervalIntegrable (by fun_prop) 0 1]
  apply sum_congr rfl
  intro i _
  rw [intervalIntegral.integral_finsetSum fun k _ ↦
    Continuous.intervalIntegrable (by fun_prop) 0 1]
  apply sum_congr rfl
  intro k _
  rw [intervalIntegral.integral_const_mul, integral_pow, one_pow, zero_pow (Nat.succ_ne_zero _),
    sub_zero]
  push_cast
  ring

/-- **The Bernstein sup bound on a subinterval**: if every Bernstein coefficient of `X` is at most
`B` in absolute value, the chart polynomial on `[x₀, x₁] ⊆ [a, b]` integrates in absolute value to
at most `(x₁ - x₀) B`. -/
theorem integral_abs_chart_polynomial_le_of_subinterval {a b x₀ x₁ : ℝ} (hab : a < b)
    (h0 : a ≤ x₀) (h01 : x₀ ≤ x₁) (h1 : x₁ ≤ b) {n : ℕ} (X : Fin (n + 1) → ℝ) (B : ℝ)
    (hB : ∀ k, |CAS.Splines.powerBernsteinCoefficients X k| ≤ B) :
    ∫ x in x₀..x₁, |∑ j, X j * ((x - a) / (b - a)) ^ j.val| ≤ (x₁ - x₀) * B := by
  have hw : 0 < b - a := sub_pos.mpr hab
  have hpt : ∀ x ∈ Icc x₀ x₁, |∑ j, X j * ((x - a) / (b - a)) ^ j.val| ≤ B := by
    intro x hx
    have hu : (x - a) / (b - a) ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (by linarith [hx.1]) hw.le
      · rw [div_le_one hw]; linarith [hx.2]
    exact CAS.Splines.abs_powerPolynomial_le X B ⟨_, hu⟩ hB
  calc ∫ x in x₀..x₁, |∑ j, X j * ((x - a) / (b - a)) ^ j.val|
      ≤ ∫ x in x₀..x₁, B := intervalIntegral.integral_mono_on h01
        (Continuous.intervalIntegrable (by fun_prop) _ _) intervalIntegrable_const hpt
    _ = (x₁ - x₀) * B := by rw [intervalIntegral.integral_const, smul_eq_mul]

end PDE.Analysis
