/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.GagliardoNirenberg.Adjacent
public import PDE.Spaces.Sobolev.Inequalities.GagliardoNirenberg.Exponents
public import PDE.Spaces.Sobolev.Inequalities.GagliardoNirenberg.FiniteRecursion
public import PDE.Spaces.Sobolev.Calculus.Differentiation.ClassicalHigherOrder

/-!
# Interpolation of compactly supported spatial derivatives

For a compactly supported `C^k` function, every mixed derivative of order
`j ≤ k` has its `L^{2k/j}` norm bounded by a constant times the sum of the
`L∞` norm of the function and the largest `L²` norm of its order-`k`
derivatives. The constant is independent of the function and its support.

The proof takes a maximum over the finite family of derivative words and
uses integration by parts and the finite adjacent-order recursion. There is
no restriction relating the spatial dimension to the derivative order.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory
open scoped ENNReal

namespace SobolevSpace.GagliardoNirenberg

variable {n : ℕ} [NeZero n]

/-- The largest interpolation norm among the spatial derivatives of a fixed order. -/
def maxDerivativeLpNorm (k j : ℕ) (u : ℝ^n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun α : Fin j → Fin n ↦
      lpNorm (iteratedPartialDeriv (List.ofFn α) u) (derivativeExponent k j) volume)

theorem lpNorm_iteratedPartialDeriv_le_max (k : ℕ) (u : ℝ^n → ℝ)
    (α : List (Fin n)) :
    lpNorm (iteratedPartialDeriv α u) (derivativeExponent k α.length) volume ≤
      maxDerivativeLpNorm k α.length u := by
  simpa only [maxDerivativeLpNorm, List.ofFn_get] using
    (Finset.le_sup'
      (fun β : Fin α.length → Fin n ↦
        lpNorm (iteratedPartialDeriv (List.ofFn β) u)
          (derivativeExponent k α.length) volume)
      (Finset.mem_univ α.get))

theorem maxDerivativeLpNorm_nonneg (k j : ℕ) (u : ℝ^n → ℝ) :
    0 ≤ maxDerivativeLpNorm k j u := by
  obtain ⟨α, _, hα⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty :
    (Finset.univ : Finset (Fin j → Fin n)).Nonempty)
    (fun α ↦ lpNorm (iteratedPartialDeriv (List.ofFn α) u)
      (derivativeExponent k j) volume)
  rw [maxDerivativeLpNorm, hα]
  exact lpNorm_nonneg

@[simp]
theorem maxDerivativeLpNorm_zero (k : ℕ) (u : ℝ^n → ℝ) :
    maxDerivativeLpNorm k 0 u = lpNorm u ∞ volume := by
  simp [maxDerivativeLpNorm, List.ofFn_zero, iteratedPartialDeriv]

omit [NeZero n] in
private theorem hasLineDerivAt_iteratedPartialDeriv {k : ℕ} {u : ℝ^n → ℝ}
    (hu : ContDiff ℝ k u) (α : List (Fin n)) (hα : α.length < k) (i : Fin n)
    (x : ℝ^n) :
    HasLineDerivAt ℝ (iteratedPartialDeriv α u) (iteratedPartialDeriv (i :: α) u x)
      x (EuclideanSpace.single i 1) := by
  have hd := (PDE.contDiff_iteratedPartialDeriv_of_le hu α hα.le).differentiable
    (by exact_mod_cast (show k - α.length ≠ 0 by omega)) x
  exact hd.hasFDerivAt.hasLineDerivAt _

/-- The largest mixed-derivative norms satisfy the adjacent-order recursion. -/
theorem maxDerivativeLpNorm_sq_le {k j : ℕ} {u : ℝ^n → ℝ}
    (hu : ContDiff ℝ k u) (huc : HasCompactSupport u) (hj : 0 < j) (hjk : j < k) :
    maxDerivativeLpNorm k j u ^ 2 ≤
      (2 * (k : ℝ)) * maxDerivativeLpNorm k (j - 1) u *
        maxDerivativeLpNorm k (j + 1) u := by
  have hk : 0 < k := hj.trans hjk
  have hcont (β : List (Fin n)) (hβ : β.length ≤ k) :
      Continuous (iteratedPartialDeriv β u) :=
    (PDE.contDiff_iteratedPartialDeriv_of_le hu β hβ).continuous
  obtain ⟨α, _, hα⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty :
    (Finset.univ : Finset (Fin j → Fin n)).Nonempty)
    (fun α ↦ lpNorm (iteratedPartialDeriv (List.ofFn α) u)
      (derivativeExponent k j) volume)
  have hlen : (List.ofFn α).length = j := List.length_ofFn
  generalize heq : List.ofFn α = β at hlen
  cases β with
  | nil => simp only [List.length_nil] at hlen; omega
  | cons i β =>
    have hβ : β.length = j - 1 := by simp only [List.length_cons] at hlen; omega
    have : ENNReal.HolderTriple (derivativeExponent k (j - 1))
        (derivativeExponent k (j + 1)) (ENNReal.ofReal ((2 * (k : ℝ) / j) / 2)) :=
      derivativeExponent_holder hk hj
    have hest := lpNorm_derivative_sq_le
      (μ := (volume : Measure (ℝ^n))) (direction := EuclideanSpace.single i 1)
      (q := derivativeExponent k (j - 1)) (r := derivativeExponent k (j + 1))
      (two_lt_derivative_exponent hj hjk)
      (hcont β (by omega)) (hcont (i :: β) (by simp only [List.length_cons]; omega))
      (hcont (i :: i :: β) (by simp only [List.length_cons]; omega))
      (huc.iteratedPartialDeriv β) (huc.iteratedPartialDeriv (i :: β))
      (huc.iteratedPartialDeriv (i :: i :: β))
      (hasLineDerivAt_iteratedPartialDeriv hu β (by omega) i)
      (hasLineDerivAt_iteratedPartialDeriv hu (i :: β)
        (by simp only [List.length_cons]; omega) i)
    have hlo : lpNorm (iteratedPartialDeriv β u) (derivativeExponent k (j - 1)) volume ≤
        maxDerivativeLpNorm k (j - 1) u := by
      simpa only [hβ] using lpNorm_iteratedPartialDeriv_le_max k u β
    have hhi : lpNorm (iteratedPartialDeriv (i :: i :: β) u)
        (derivativeExponent k (j + 1)) volume ≤ maxDerivativeLpNorm k (j + 1) u := by
      have hlen' : (i :: i :: β).length = j + 1 := by
        simp only [List.length_cons]
        omega
      simpa only [hlen'] using lpNorm_iteratedPartialDeriv_le_max k u (i :: i :: β)
    have hcoeff0 : 0 ≤ 2 * (k : ℝ) / j - 1 := by
      have := two_lt_derivative_exponent hj hjk
      linarith
    have hcoeff : 2 * (k : ℝ) / j - 1 ≤ 2 * k := by
      have hj' : 1 ≤ (j : ℝ) := by exact_mod_cast hj
      have hk' : 0 ≤ (k : ℝ) := by positivity
      have hdiv := div_le_self (show 0 ≤ 2 * (k : ℝ) by positivity) hj'
      linarith
    rw [maxDerivativeLpNorm, hα, heq, derivativeExponent_eq_of_pos hk hj]
    calc
      _ ≤ _ := hest
      _ ≤ (2 * (k : ℝ) / j - 1) * maxDerivativeLpNorm k (j - 1) u *
          maxDerivativeLpNorm k (j + 1) u :=
        mul_le_mul (mul_le_mul_of_nonneg_left hlo hcoeff0) hhi lpNorm_nonneg
          (mul_nonneg hcoeff0 (maxDerivativeLpNorm_nonneg _ _ _))
      _ ≤ _ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoeff (maxDerivativeLpNorm_nonneg _ _ _))
          (maxDerivativeLpNorm_nonneg _ _ _)

/-- Uniform interpolation for every mixed derivative through a prescribed finite
order. The lower endpoint is the bounded value of the function, and the upper
endpoint consists only of its square-integrable top derivatives. -/
theorem exists_constant_lpNorm_iteratedPartialDeriv_le (k : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ u : ℝ^n → ℝ,
      ContDiff ℝ k u → HasCompactSupport u →
      ∀ α : List (Fin n), α.length ≤ k →
        lpNorm (iteratedPartialDeriv α u) (derivativeExponent k α.length) volume ≤
          A * (lpNorm u ∞ volume + maxDerivativeLpNorm k k u) := by
  obtain ⟨A, hA, hrec⟩ := exists_constant_of_adjacent_sq_le
    (show 0 ≤ 2 * (k : ℝ) by positivity) k
  refine ⟨A, hA, ?_⟩
  intro u hu huc α hα
  have hbound := hrec (fun j ↦ maxDerivativeLpNorm k j u)
    (fun j _ ↦ maxDerivativeLpNorm_nonneg k j u)
    (fun j hj hjk ↦ maxDerivativeLpNorm_sq_le hu huc hj hjk) α.length hα
  simpa only [maxDerivativeLpNorm_zero] using
    (lpNorm_iteratedPartialDeriv_le_max k u α).trans hbound

end SobolevSpace.GagliardoNirenberg
