/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Commutators with the singular radial derivative

The Leibniz rule expands derivatives of `c r⁻¹ f'` at every nonzero radius.
Removing its principal row gives the commutator. The coefficient is arbitrary;
the radial Laplacian in dimension `n` uses `c = n - 1`.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.Radial

/-- Leibniz expansion for the singular radial derivative with arbitrary
coefficient and derivative order. -/
theorem iteratedDeriv_const_inv_mul_deriv
    (c : ℝ) (a : ℕ) (f : ℝ → ℝ) {r : ℝ} (hr : r ≠ 0)
    (hf : ContDiffAt ℝ (a + 1) f r) :
    iteratedDeriv a (fun s : ℝ ↦ c * s⁻¹ * deriv f s) r =
      c * ∑ q ∈ Finset.range (a + 1),
        (a.choose q : ℝ) *
          (((-1 : ℝ) ^ q * q.factorial * r ^ (-1 - (q : ℤ))) *
            iteratedDeriv (a - q + 1) f r) := by
  have hinv : ContDiffAt ℝ a (fun s : ℝ ↦ s⁻¹) r :=
    contDiffAt_inv ℝ hr
  have hderiv : ContDiffAt ℝ a (deriv f) r :=
    hf.derivWithin (by simp)
  have hproduct := iteratedDeriv_mul (n := a) hinv hderiv
  rw [show (fun s : ℝ ↦ c * s⁻¹ * deriv f s) =
      fun s : ℝ ↦ c * (s⁻¹ * deriv f s) by funext s; ring]
  rw [iteratedDeriv_const_mul_field]
  change c * iteratedDeriv a ((fun s : ℝ ↦ s⁻¹) * deriv f) r = _
  rw [hproduct]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  have hinvFormula :
      iteratedDeriv q (fun s : ℝ ↦ s⁻¹) r =
        (-1 : ℝ) ^ q * q.factorial * r ^ (-1 - (q : ℤ)) := by
    rw [iteratedDeriv_eq_iterate]
    exact iter_deriv_inv q r
  rw [hinvFormula, iteratedDeriv_succ']
  ring

/-- The commutator consists of exactly the nonprincipal Leibniz rows. Each
additional derivative of `r⁻¹` contributes one further inverse power of `r`. -/
theorem iteratedDeriv_radialSingularPart_commutator
    (c : ℝ) (a : ℕ) (f : ℝ → ℝ) {r : ℝ} (hr : r ≠ 0)
    (hf : ContDiffAt ℝ (a + 1) f r) :
    iteratedDeriv a (fun s : ℝ ↦ c * s⁻¹ * deriv f s) r -
        c * r⁻¹ * iteratedDeriv (a + 1) f r =
      ∑ q ∈ Finset.range a,
        c * (a.choose (q + 1) : ℝ) * (-1 : ℝ) ^ (q + 1) *
          ((q + 1).factorial : ℝ) * r ^ (-((q + 2 : ℕ) : ℤ)) *
            iteratedDeriv (a - (q + 1) + 1) f r := by
  rw [iteratedDeriv_const_inv_mul_deriv c a f hr hf, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.factorial_zero, Nat.cast_one, pow_zero,
    one_mul, Nat.cast_zero, sub_zero, zpow_neg, zpow_one, Nat.sub_zero]
  rw [mul_add, ← mul_assoc c r⁻¹, add_sub_cancel_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  have hexp : (-1 - ((q + 1 : ℕ) : ℤ)) = -((q + 2 : ℕ) : ℤ) := by omega
  rw [hexp, zpow_neg]
  ring

end PDE.Elliptic.Radial
