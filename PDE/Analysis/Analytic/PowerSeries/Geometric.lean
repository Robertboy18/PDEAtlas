/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.Nonnegative

/-!
# A multivariable geometric coefficient majorant

The inverse of `ρ - ∑ Xᵢ` has nonnegative coefficients. Its coefficient recurrence
shows that every coefficient of degree `n` is at least `ρ⁻¹ ^ (n + 1)`.
This lower bound is sufficient for analytic majorants and avoids a separate
multinomial coefficient formula.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace MvPowerSeries

variable {σ : Type*} [Fintype σ]

/-- The multivariable geometric denominator has a nonnegative formal inverse. -/
theorem coeff_inv_C_sub_sum_X_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (a : σ →₀ ℕ) :
    0 ≤ coeff a (C ρ - ∑ i : σ, X i)⁻¹ := by
  classical
  apply coeff_inv_nonneg_of_nonpos _ (by simpa using hρ) _ a
  intro b hb
  simp only [map_sub, coeff_C, ite_eq_right hb, zero_sub, map_sum]
  apply neg_nonpos.mpr
  apply Finset.sum_nonneg
  intro i hi
  simp only [coeff_X]
  split_ifs <;> norm_num

/-- Each geometric coefficient dominates the pure geometric term of the same degree. -/
theorem inv_pow_le_coeff_inv_C_sub_sum_X {ρ : ℝ} (hρ : 0 < ρ) (a : σ →₀ ℕ) :
    ρ⁻¹ ^ (a.sum (fun _ ↦ id) + 1) ≤ coeff a (C ρ - ∑ i : σ, X i)⁻¹ := by
  classical
  let G : MvPowerSeries σ ℝ := C ρ - ∑ i : σ, X i
  have hG : constantCoeff G ≠ 0 := by simpa [G] using hρ.ne'
  have hpos : ∀ a, 0 ≤ coeff a G⁻¹ := coeff_inv_C_sub_sum_X_nonneg hρ.le
  change ρ⁻¹ ^ (a.sum (fun _ ↦ id) + 1) ≤ coeff a G⁻¹
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    by_cases ha : a = 0
    · subst a
      simp [G, coeff_zero_eq_constantCoeff]
    obtain ⟨i, hi⟩ : ∃ i, 0 < a i := by
      by_contra h
      apply ha
      ext i
      have := not_exists.mp h i
      simpa using Nat.eq_zero_of_not_pos this
    have hsingle : Finsupp.single i 1 ≤ a := by
      simpa using (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (ne_of_gt hi)))
    let b := a - Finsupp.single i 1
    have hba : Finsupp.single i 1 + b = a := add_tsub_cancel_of_le hsingle
    have hlt : b < a := by
      apply lt_of_le_of_ne tsub_le_self
      intro h
      have := congrArg (fun e : σ →₀ ℕ ↦ e i) h
      simp only [Finsupp.tsub_apply, Finsupp.single_eq_same] at this
      omega
    have hdegree : a.sum (fun _ ↦ id) = b.sum (fun _ ↦ id) + 1 := by
      rw [← hba]
      simp [Finsupp.sum_add_index, add_comm]
    have heq := congrArg (coeff a) (G.mul_inv_cancel hG)
    simp only [G, sub_mul, Finset.sum_mul, map_sub, map_sum, coeff_C_mul,
      coeff_one, ite_eq_right ha] at heq
    have hstep : coeff b G⁻¹ ≤ ρ * coeff a G⁻¹ := by
      calc
        coeff b G⁻¹ = coeff a (X i * G⁻¹) := by
          rw [← hba]
          simp only [X, coeff_add_monomial_mul, one_mul]
        _ ≤ ∑ j : σ, coeff a (X j * G⁻¹) := by
          apply Finset.single_le_sum _ (Finset.mem_univ i)
          intro j hj
          apply coeff_mul_nonneg _ hpos
          intro e
          simp only [coeff_X]
          split_ifs <;> norm_num
        _ = ρ * coeff a G⁻¹ := (sub_eq_zero.mp heq).symm
    apply (mul_le_mul_iff_of_pos_right hρ).mp
    calc
      ρ⁻¹ ^ (a.sum (fun _ ↦ id) + 1) * ρ = ρ⁻¹ ^ (b.sum (fun _ ↦ id) + 1) := by
        rw [hdegree, pow_succ, mul_assoc, inv_mul_cancel₀ hρ.ne', mul_one]
      _ ≤ coeff b G⁻¹ := ih b hlt
      _ ≤ coeff a G⁻¹ * ρ := by simpa only [mul_comm] using hstep

end MvPowerSeries
