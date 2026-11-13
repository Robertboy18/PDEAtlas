/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigLaurent

/-!
# The two parts of a Laurent row

A row symmetric about its middle has no sine series and an antisymmetric one no cosine series
(`laurentSin_eq_zero_of_symm`, `laurentCos_eq_zero_of_anti`); both series of a row are bounded by
its `ℓ¹` norm, also for differences (`abs_laurentSin_sub_le'`, `abs_laurentCos_sub_le'`).
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Finset

/-- Reflecting the index of a sum over `range (2 T + 1)` about `T` does not change it. -/
theorem sum_reflect_window (T : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ range (2 * T + 1), f (2 * T - i) = ∑ i ∈ range (2 * T + 1), f i := by
  rw [← sum_range_reflect f (2 * T + 1)]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [show 2 * T + 1 - 1 - i = 2 * T - i by omega]

theorem laurentSin_eq_zero_of_symm {T : ℕ} {φ : ℕ → ℝ} (h : IsLaurentSymm T φ) (θ : ℝ) :
    laurentSin T φ θ = 0 := by
  have e1 := (sum_reflect_window T fun i ↦ φ i * Real.sin (((i : ℝ) - T) * θ)).symm
  have e2 : ∑ i ∈ range (2 * T + 1), φ (2 * T - i) * Real.sin ((((2 * T - i : ℕ) : ℝ) - T) * θ) =
      -∑ i ∈ range (2 * T + 1), φ i * Real.sin (((i : ℝ) - T) * θ) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun i hi ↦ ?_
    have hi' := mem_range.mp hi
    rw [h i hi', Nat.cast_sub (by omega), show (((2 * T : ℕ) : ℝ) - i - T) * θ =
      -(((i : ℝ) - T) * θ) by push_cast; ring, Real.sin_neg]
    ring
  have e : laurentSin T φ θ = -laurentSin T φ θ := by
    unfold laurentSin
    exact e1.trans e2
  linarith

theorem laurentCos_eq_zero_of_anti {T : ℕ} {φ : ℕ → ℝ} (h : IsLaurentAnti T φ) (θ : ℝ) :
    laurentCos T φ θ = 0 := by
  have e1 := (sum_reflect_window T fun i ↦ φ i * Real.cos (((i : ℝ) - T) * θ)).symm
  have e2 : ∑ i ∈ range (2 * T + 1), φ (2 * T - i) * Real.cos ((((2 * T - i : ℕ) : ℝ) - T) * θ) =
      -∑ i ∈ range (2 * T + 1), φ i * Real.cos (((i : ℝ) - T) * θ) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun i hi ↦ ?_
    have hi' := mem_range.mp hi
    rw [h i hi', Nat.cast_sub (by omega), show (((2 * T : ℕ) : ℝ) - i - T) * θ =
      -(((i : ℝ) - T) * θ) by push_cast; ring, Real.cos_neg]
    ring
  have e : laurentCos T φ θ = -laurentCos T φ θ := by
    unfold laurentCos
    exact e1.trans e2
  linarith

theorem abs_laurentCos_sub_le' (T : ℕ) (φ ψ : ℕ → ℝ) (θ : ℝ) :
    |laurentCos T φ θ - laurentCos T ψ θ| ≤ ∑ i ∈ range (2 * T + 1), |φ i - ψ i| := by
  unfold laurentCos
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ ↦ ?_)
  rw [← sub_mul, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

theorem abs_laurentSin_sub_le' (T : ℕ) (φ ψ : ℕ → ℝ) (θ : ℝ) :
    |laurentSin T φ θ - laurentSin T ψ θ| ≤ ∑ i ∈ range (2 * T + 1), |φ i - ψ i| := by
  unfold laurentSin
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ ↦ ?_)
  rw [← sub_mul, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)

end PDE.Analysis
