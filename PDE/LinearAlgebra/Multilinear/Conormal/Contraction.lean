/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.LinearAlgebra.Multilinear.Conormal
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Detecting a conormal tensor by contraction

A linear contraction whose symbol is nonzero detects a pure conormal tensor.
Pairing coordinate observations with the same normal monomials gives a sum of
squares, so one nonzero monomial suffices.
-/

@[expose] public section

namespace MultilinearMap

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]
  {m : ℕ}

/-- A nonzero symbol makes a contraction injective on the line of conormal
tensors. -/
theorem eq_zero_of_conormal_contraction_eq_zero
    (A : MultilinearMap ℝ (fun _ : Fin m ↦ E) ℝ)
    (ℓ : E →ₗ[ℝ] ℝ) {c : ℝ}
    (hA : ∀ v, A v = (∏ i, ℓ (v i)) * c)
    (d : ι → Fin m → E) (a : ι → ℝ)
    (hsymbol : ∑ α, a α * ∏ i, ℓ (d α i) ≠ 0)
    (hcontract : ∑ α, a α * A (d α) = 0) : A = 0 := by
  have hc : c = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hsymbol
    rw [Finset.sum_mul]
    simpa only [hA, mul_assoc] using hcontract
  ext v
  simp [hA, hc]

/-- Contracting a conormal tensor against its own normal monomials detects it: the
scalar factor is the sum of squares `∑ α, (∏ i, ℓ (d α i))²`, which is positive once
one monomial is nonzero. -/
theorem eq_zero_of_conormal_normal_sum_eq_zero
    (A : MultilinearMap ℝ (fun _ : Fin m ↦ E) ℝ)
    (ℓ : E →ₗ[ℝ] ℝ) {c : ℝ}
    (hA : ∀ v, A v = (∏ i, ℓ (v i)) * c)
    (d : ι → Fin m → E)
    (hnonzero : ∃ α, (∏ i, ℓ (d α i)) ≠ 0)
    (htrace : ∑ α, A (d α) * ∏ i, ℓ (d α i) = 0) : A = 0 := by
  apply A.eq_zero_of_conormal_contraction_eq_zero ℓ hA d (fun α ↦ ∏ i, ℓ (d α i))
  · apply ne_of_gt
    obtain ⟨α, hα⟩ := hnonzero
    exact Finset.sum_pos' (fun _ _ ↦ mul_self_nonneg _)
      ⟨α, Finset.mem_univ _, mul_self_pos.mpr hα⟩
  · simpa only [mul_comm] using htrace

end MultilinearMap
