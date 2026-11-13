/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Recursion in the degree of a formal power series

A coupled coefficient equation has a unique solution when its coefficient of
degree `n` depends only on coefficients of smaller degrees. The coefficient
ring may itself be a ring of formal power series: recursion in one distinguished
variable then determines all coefficients in the other variables simultaneously.
-/

@[expose] public section

namespace PowerSeries

variable {ι R : Type*} [CommRing R]

/-- A strictly triangular system of coefficient equations has a unique formal solution. -/
theorem existsUnique_coeff_eq_of_depend_lt
    (F : ℕ → (ι → PowerSeries R) → ι → R)
    (hF : ∀ n u v,
      (∀ j k, k < n → coeff k (u j) = coeff k (v j)) → F n u = F n v) :
    ∃! u : ι → PowerSeries R, ∀ n j, coeff n (u j) = F n u j := by
  classical
  let a : ℕ → ι → R := Nat.strongRec fun n rec ↦
    F n (fun j ↦ mk fun k ↦ if h : k < n then rec k h j else 0)
  let u : ι → PowerSeries R := fun j ↦ mk fun n ↦ a n j
  have ha (n : ℕ) : a n = F n u := by
    rw [show a n = F n (fun j ↦ mk fun k ↦ if k < n then a k j else 0) from
      Nat.strongRec_eq _ n]
    apply hF
    intro j k hk
    simp [u, hk]
  have hu (n : ℕ) (j : ι) : coeff n (u j) = F n u j := by
    simpa [u] using congrFun (ha n) j
  refine ⟨u, hu, ?_⟩
  intro v hv
  have hvu (n : ℕ) : ∀ j, coeff n (v j) = coeff n (u j) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j
      rw [hv, hu]
      exact congrFun (hF n v u fun i k hk ↦ ih k hk i) j
  funext j
  exact ext fun n ↦ hvu n j

variable [Algebra ℚ R]

/-- A formal differential system has a unique solution when each coefficient of its
right-hand side depends only on coefficients of the unknown through that degree. -/
theorem existsUnique_derivative_eq_of_coeff_depend_le
    (F : (ι → PowerSeries R) → ι → PowerSeries R) (a : ι → R)
    (hF : ∀ n u v,
      (∀ j k, k ≤ n → coeff k (u j) = coeff k (v j)) →
        ∀ j, coeff n (F u j) = coeff n (F v j)) :
    ∃! u : ι → PowerSeries R,
      (∀ j, constantCoeff (u j) = a j) ∧ ∀ j, derivative (u j) = F u j := by
  let G : ℕ → (ι → PowerSeries R) → ι → R
    | 0, _ => a
    | n + 1, u => fun j ↦ (n + 1 : ℚ)⁻¹ • coeff n (F u j)
  have hG (n : ℕ) (u v : ι → PowerSeries R)
      (h : ∀ j k, k < n → coeff k (u j) = coeff k (v j)) : G n u = G n v := by
    cases n with
    | zero => rfl
    | succ n =>
      funext j
      exact congrArg ((n + 1 : ℚ)⁻¹ • ·)
        (hF n u v (fun i k hk ↦ h i k (Nat.lt_succ_iff.mpr hk)) j)
  have hD (u : PowerSeries R) (n : ℕ) :
      coeff n (derivative u) = (n + 1 : ℚ) • coeff (n + 1) u := by
    rw [coeff_derivative, show (n + 1 : ℚ) = ((n + 1 : ℕ) : ℚ) by simp,
      Nat.cast_smul_eq_nsmul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_comm]
  have hne (n : ℕ) : (n + 1 : ℚ) ≠ 0 := by positivity
  have heq (u : ι → PowerSeries R) :
      (∀ n j, coeff n (u j) = G n u j) ↔
        (∀ j, constantCoeff (u j) = a j) ∧ ∀ j, derivative (u j) = F u j := by
    constructor
    · intro h
      refine ⟨fun j ↦ by simpa [G] using h 0 j, fun j ↦ ?_⟩
      apply ext
      intro n
      rw [hD, h (n + 1), show G (n + 1) u j = _ from rfl,
        smul_smul, mul_inv_cancel₀ (hne n), one_smul]
    · rintro ⟨hzero, hderiv⟩ n j
      cases n with
      | zero => simpa [G] using hzero j
      | succ n =>
        have h := congrArg (coeff n) (hderiv j)
        rw [hD] at h
        have h := congrArg ((n + 1 : ℚ)⁻¹ • ·) h
        simpa [G, smul_smul, inv_mul_cancel₀ (hne n)] using h
  obtain ⟨u, hu, huniq⟩ := existsUnique_coeff_eq_of_depend_lt G hG
  exact ⟨u, (heq u).mp hu, fun v hv ↦ huniq v ((heq v).mpr hv)⟩

end PowerSeries
