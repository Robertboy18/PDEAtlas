/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.TensorHornerDerivatives

/-!
# Derivative tensors with fixed-size zero padding

The shifted derivative table may retain the original tensor dimensions
when coefficients beyond the differentiated degree are replaced by zero.
The identities include empty tensors and arbitrary derivative orders.

## Main results

* `sum_range_add_lt`: a sum over `range (n - a)` is the sum over `range n` with the terms
  `i + a ≥ n` replaced by zero.
* `tensorHornerValue_derivative_eq_padded_sum`: the value of `tensorDerivativeCoefficients` is the
  sum over the original dimensions of the shifted falling-factorial coefficients, padded with zeros.
-/

@[expose] public section

namespace CAS.Splines

open scoped BigOperators

/-- A double sum over `Fin nx × Fin ny` is the double sum over `range nx × range ny`. -/
private theorem sum_fin_tensor_eq_sum_range {M : Type*} [AddCommMonoid M]
    (nx ny : ℕ) (f : ℕ → ℕ → M) :
    (∑ i : Fin nx, ∑ j : Fin ny, f i.val j.val) =
      ∑ i ∈ Finset.range nx, ∑ j ∈ Finset.range ny, f i j := by
  rw [← Finset.sum_range (fun i ↦ ∑ j : Fin ny, f i j.val)]
  exact Finset.sum_congr rfl fun i _ ↦ (Finset.sum_range (f i)).symm

/-- A truncated range can be padded with zeros to the original range. -/
theorem sum_range_add_lt {M : Type*} [AddCommMonoid M] (n a : ℕ) (f : ℕ → M) :
    (∑ i ∈ Finset.range n, if i + a < n then f i else 0) =
      ∑ i ∈ Finset.range (n - a), f i := by
  calc
    _ = ∑ i ∈ Finset.range (n - a), if i + a < n then f i else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.sub_le n a))
      intro i _ hi
      have hi' : ¬ i + a < n := by
        simp only [Finset.mem_range] at hi
        omega
      exact ite_eq_right hi'
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i + a < n := by
        simp only [Finset.mem_range] at hi
        omega
      exact ite_eq_left hi'

/-- Zero padding leaves every mixed derivative tensor's real value unchanged. -/
theorem tensorHornerValue_derivative_eq_padded_sum (nx ny : ℕ) (c : ℕ → ℕ → ℚ)
    (a b : ℕ) (x y : ℝ) :
    tensorHornerValue (tensorDerivativeCoefficients nx ny c a b) x y =
      ∑ i : Fin nx, ∑ j : Fin ny,
        (if i.val + a < nx ∧ j.val + b < ny then
          (c (i.val + a) (j.val + b) : ℝ) *
            ((i.val + a).descFactorial a : ℝ) * ((j.val + b).descFactorial b : ℝ)
        else 0) * x ^ i.val * y ^ j.val := by
  rw [tensorDerivativeCoefficients, tensorHornerValue_tensorCoefficients]
  simp only [Rat.cast_mul, Rat.cast_natCast]
  rw [sum_fin_tensor_eq_sum_range nx ny (fun i j ↦
    (if i + a < nx ∧ j + b < ny then
      (c (i + a) (j + b) : ℝ) * ((i + a).descFactorial a : ℝ) *
        ((j + b).descFactorial b : ℝ) else 0) * x ^ i * y ^ j)]
  simp only [ite_and, ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp_rw [sum_range_add_lt]

end CAS.Splines
