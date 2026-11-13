/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.Catalan
public import Mathlib.Basic.Real.Basic

/-!
# Nonnegative formal series

Products and admissible scalar substitutions preserve nonnegative coefficients.
The recursive formula for an inverse also proves positivity when the constant
term is nonnegative and every other coefficient is nonpositive.
-/

@[expose] public section

open scoped BigOperators

namespace MvPowerSeries

variable {σ : Type*}

/-- Products of series with nonnegative coefficients have nonnegative coefficients. -/
theorem coeff_mul_nonneg {f g : MvPowerSeries σ ℝ}
    (hf : ∀ a, 0 ≤ coeff a f) (hg : ∀ a, 0 ≤ coeff a g) (a : σ →₀ ℕ) :
    0 ≤ coeff a (f * g) := by
  classical
  rw [coeff_mul]
  exact Finset.sum_nonneg fun b hb ↦ mul_nonneg (hf b.1) (hg b.2)

/-- Natural powers preserve nonnegative coefficients. -/
theorem coeff_pow_nonneg {f : MvPowerSeries σ ℝ}
    (hf : ∀ a, 0 ≤ coeff a f) (n : ℕ) (a : σ →₀ ℕ) :
    0 ≤ coeff a (f ^ n) := by
  classical
  induction n generalizing a with
  | zero => simp only [pow_zero, coeff_one]; split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ]
    exact coeff_mul_nonneg (fun a ↦ ih a) hf a

/-- The inverse recursion preserves positivity when all nonconstant coefficients
of the denominator are nonpositive. The totalized inverse also covers zero constant term. -/
theorem coeff_inv_nonneg_of_nonpos (f : MvPowerSeries σ ℝ)
    (h₀ : 0 ≤ constantCoeff f) (hf : ∀ a ≠ 0, coeff a f ≤ 0) (a : σ →₀ ℕ) :
    0 ≤ coeff a f⁻¹ := by
  classical
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    rw [coeff_inv]
    split_ifs with ha
    · exact inv_nonneg.mpr h₀
    · apply mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (inv_nonneg.mpr h₀))
      apply Finset.sum_nonpos
      intro b hb
      split_ifs with hba
      · have hb' := Finset.mem_antidiagonal.mp hb
        have hb₁ : b.1 ≠ 0 := by
          intro hz
          have : b.2 = a := by simpa [hz] using hb'
          exact (ne_of_lt hba) this
        exact mul_nonpos_of_nonpos_of_nonneg (hf b.1 hb₁) (ih b.2 hba)
      · exact le_rfl

/-- The Catalan root uses the nonnegative branch when its input coefficients are nonnegative. -/
theorem coeff_quadraticRoot_nonneg (a b : MvPowerSeries σ ℝ)
    (ha₀ : constantCoeff a = 0) (ha : ∀ e, 0 ≤ coeff e a) (hb : ∀ e, 0 ≤ coeff e b)
    (e : σ →₀ ℕ) : 0 ≤ coeff e (quadraticRoot a b) := by
  classical
  apply coeff_mul_nonneg ha _ e
  intro k
  have hba : PowerSeries.HasSubst (b * a) :=
    .of_constantCoeff_zero (by simp [ha₀])
  rw [PowerSeries.coeff_subst hba]
  apply finsum_nonneg
  intro n
  simp only [PowerSeries.coeff_map, PowerSeries.catalanSeries_coeff,
    smul_eq_mul]
  change 0 ≤ (catalan n : ℝ) * coeff k ((b * a) ^ n)
  exact mul_nonneg (by positivity)
    (coeff_pow_nonneg (fun e ↦ coeff_mul_nonneg hb ha e) n k)

end MvPowerSeries
