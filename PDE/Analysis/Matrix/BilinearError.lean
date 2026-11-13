/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Chebyshev

/-!
# Perturbation of bilinear forms with bounded kernels

For a kernel `ν` with `|ν| ≤ 1`, the bilinear form `∑_{i,j<q} φ_i ψ_j ν_{ij}` changes under
perturbations of the two vectors and of the kernel by at most
`‖φ - φ'‖₁ ‖ψ‖₁ + ‖φ'‖₁ ‖ψ - ψ'‖₁ + ε ‖φ'‖₁ ‖ψ'‖₁` (`abs_bilinear_sub_le`), the kernel error `ε`
being needed only on the pairs where `φ'_i ψ'_j ≠ 0`. With `‖x‖₁² ≤ q ‖x‖₂²`
(`sum_abs_le_sqrt`) the ℓ¹ norms of the approximations follow from square sums.
-/

@[expose] public section

namespace PDE.Analysis

open Finset

/-- **Perturbation of a bilinear form.** -/
theorem abs_bilinear_sub_le {q : ℕ} (φ ψ φ' ψ' : ℕ → ℝ) (ν ν' : ℕ → ℕ → ℝ) {ε : ℝ}
    (hν : ∀ i < q, ∀ j < q, |ν i j| ≤ 1)
    (hνν : ∀ i < q, ∀ j < q, φ' i * ψ' j ≠ 0 → |ν i j - ν' i j| ≤ ε) (hε : 0 ≤ ε) :
    |∑ i ∈ range q, ∑ j ∈ range q, φ i * ψ j * ν i j -
        ∑ i ∈ range q, ∑ j ∈ range q, φ' i * ψ' j * ν' i j| ≤
      (∑ i ∈ range q, |φ i - φ' i|) * (∑ j ∈ range q, |ψ j|) +
        (∑ i ∈ range q, |φ' i|) * (∑ j ∈ range q, |ψ j - ψ' j|) +
        ε * ((∑ i ∈ range q, |φ' i|) * (∑ j ∈ range q, |ψ' j|)) := by
  have hpt : ∀ i < q, ∀ j < q, |φ i * ψ j * ν i j - φ' i * ψ' j * ν' i j| ≤
      |φ i - φ' i| * |ψ j| + |φ' i| * |ψ j - ψ' j| + ε * (|φ' i| * |ψ' j|) := by
    intro i hi j hj
    have e : φ i * ψ j * ν i j - φ' i * ψ' j * ν' i j =
        (φ i - φ' i) * ψ j * ν i j + φ' i * (ψ j - ψ' j) * ν i j +
          φ' i * ψ' j * (ν i j - ν' i j) := by ring
    rw [e]
    have h1 : |(φ i - φ' i) * ψ j * ν i j| ≤ |φ i - φ' i| * |ψ j| := by
      rw [abs_mul, abs_mul]
      exact mul_le_of_le_one_right (by positivity) (hν i hi j hj)
    have h2 : |φ' i * (ψ j - ψ' j) * ν i j| ≤ |φ' i| * |ψ j - ψ' j| := by
      rw [abs_mul, abs_mul]
      exact mul_le_of_le_one_right (by positivity) (hν i hi j hj)
    have h3 : |φ' i * ψ' j * (ν i j - ν' i j)| ≤ ε * (|φ' i| * |ψ' j|) := by
      by_cases h0 : φ' i * ψ' j = 0
      · rw [h0, zero_mul, abs_zero]; positivity
      · rw [abs_mul, show ε * (|φ' i| * |ψ' j|) = |φ' i * ψ' j| * ε by rw [abs_mul]; ring]
        exact mul_le_mul_of_nonneg_left (hνν i hi j hj h0) (abs_nonneg _)
    exact (abs_add_three _ _ _).trans (by linarith)
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i ∈ range q, |∑ j ∈ range q, φ i * ψ j * ν i j - ∑ j ∈ range q, φ' i * ψ' j * ν' i j|
      ≤ ∑ i ∈ range q, ∑ j ∈ range q, (|φ i - φ' i| * |ψ j| + |φ' i| * |ψ j - ψ' j| +
          ε * (|φ' i| * |ψ' j|)) := sum_le_sum fun i hi ↦ by
        rw [← sum_sub_distrib]
        exact (abs_sum_le_sum_abs _ _).trans
          (sum_le_sum fun j hj ↦ hpt i (mem_range.mp hi) j (mem_range.mp hj))
    _ = _ := by
        simp only [sum_add_distrib, ← mul_sum, ← sum_mul]

/-- `‖x‖₁ ≤ √(q ‖x‖₂²)`. -/
theorem sum_abs_le_sqrt {q : ℕ} (x : ℕ → ℝ) :
    ∑ i ∈ range q, |x i| ≤ √(q * ∑ i ∈ range q, x i ^ 2) := by
  apply Real.le_sqrt_of_sq_le
  have h := sq_sum_le_card_mul_sum_sq (s := range q) (f := fun i ↦ |x i|)
  simp only [card_range, sq_abs] at h
  exact h

end PDE.Analysis
