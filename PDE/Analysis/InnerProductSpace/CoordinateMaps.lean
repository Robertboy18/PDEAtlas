/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Norms of maps through finitely many coordinates

For vectors `q₁, …, qₙ` of a real inner product space `E` and `φ₁, …, φₙ` of another one `V`,
the map `g ↦ ∑ⱼ ⟪qⱼ, g⟫ φⱼ` factors through the coordinates `⟪qⱼ, g⟫`. A matrix `Z` with
`‖∑ⱼ aⱼ qⱼ‖² ≤ ∑ₖ (∑ⱼ Zⱼₖ aⱼ)²` for every `a` (the Gram matrix of the `qⱼ` below `Z Zᵀ`) moves the
whole estimate to the combined vectors `ψₖ = ∑ⱼ Zⱼₖ φⱼ`: if `∑ₖ ⟪ψₖ, v⟫² ≤ γ² ‖v‖²` for every
`v`, the map has norm at most `γ` (`norm_sum_inner_smul_le`). The condition on the `ψₖ` follows
from `‖∑ₖ yₖ ψₖ‖² ≤ γ² |y|²` for every `y` (`sum_inner_sq_le_of_norm_sum_smul_le`), the bound of
the Gram matrix of the `ψₖ`.
-/

@[expose] public section

namespace PDE.Analysis

open Finset
open scoped RealInnerProductSpace

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]

/-- A vector `x` with `‖x‖² ≤ γ ‖x‖ C` has `‖x‖ ≤ γ C`. -/
private theorem le_of_sq_le_mul {x γ C : ℝ} (hx : 0 ≤ x) (hγ : 0 ≤ γ) (hC : 0 ≤ C)
    (h : x ^ 2 ≤ γ * x * C) : x ≤ γ * C := by
  rcases hx.eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · nlinarith

/-- **The adjoint bound of a Gram bound.** If `‖∑ₖ yₖ ψₖ‖² ≤ γ² |y|²` for every `y`, then
`∑ₖ ⟪ψₖ, v⟫² ≤ γ² ‖v‖²` for every `v`. -/
theorem sum_inner_sq_le_of_norm_sum_smul_le {m : ℕ} (ψ : Fin m → V) {γ : ℝ} (hγ : 0 ≤ γ)
    (h : ∀ y : Fin m → ℝ, ‖∑ k, y k • ψ k‖ ^ 2 ≤ γ ^ 2 * ∑ k, y k ^ 2) (v : V) :
    ∑ k, ⟪ψ k, v⟫ ^ 2 ≤ γ ^ 2 * ‖v‖ ^ 2 := by
  set y : Fin m → ℝ := fun k ↦ ⟪ψ k, v⟫
  set S := ∑ k, y k ^ 2
  have hS : 0 ≤ S := sum_nonneg fun _ _ ↦ sq_nonneg _
  have hdot : S = ⟪∑ k, y k • ψ k, v⟫ := by
    rw [sum_inner]
    exact sum_congr rfl fun k _ ↦ by rw [real_inner_smul_left, sq]
  have hnorm : ‖∑ k, y k • ψ k‖ ≤ γ * √S := by
    have h1 := h y
    rw [← Real.sqrt_le_sqrt_iff (by positivity), Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_mul (by positivity), Real.sqrt_sq hγ] at h1
    exact h1
  have hsq : √S ^ 2 ≤ γ * √S * ‖v‖ := by
    have e : √S ^ 2 = ⟪∑ k, y k • ψ k, v⟫ := by rw [Real.sq_sqrt hS]; exact hdot
    rw [e]
    calc ⟪∑ k, y k • ψ k, v⟫ ≤ ‖∑ k, y k • ψ k‖ * ‖v‖ := real_inner_le_norm _ _
      _ ≤ γ * √S * ‖v‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
  have h2 := le_of_sq_le_mul (Real.sqrt_nonneg S) hγ (norm_nonneg v) hsq
  have h3 : S ≤ (γ * ‖v‖) ^ 2 := by
    rw [← Real.sq_sqrt hS]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
  rw [mul_pow] at h3
  exact h3

/-- **A map through finitely many coordinates.** If `‖∑ⱼ aⱼ qⱼ‖² ≤ ∑ₖ (∑ⱼ Zⱼₖ aⱼ)²` for every
`a` and the combined vectors `ψₖ = ∑ⱼ Zⱼₖ φⱼ` satisfy `∑ₖ ⟪ψₖ, v⟫² ≤ γ² ‖v‖²` for every `v`,
then `‖∑ⱼ ⟪qⱼ, g⟫ φⱼ‖ ≤ γ ‖g‖`. -/
theorem norm_sum_inner_smul_le {n m : ℕ} (q : Fin n → E) (φ : Fin n → V) (Z : Fin n → Fin m → ℝ)
    {γ : ℝ} (hγ : 0 ≤ γ) (hq : ∀ a : Fin n → ℝ, ‖∑ j, a j • q j‖ ^ 2 ≤ ∑ k, (∑ j, Z j k * a j) ^ 2)
    (hφ : ∀ v : V, ∑ k, ⟪∑ j, Z j k • φ j, v⟫ ^ 2 ≤ γ ^ 2 * ‖v‖ ^ 2) (g : E) :
    ‖∑ j, ⟪q j, g⟫ • φ j‖ ≤ γ * ‖g‖ := by
  set w := ∑ j, ⟪q j, g⟫ • φ j
  set a : Fin n → ℝ := fun j ↦ ⟪φ j, w⟫
  have hw : ‖w‖ ^ 2 = ⟪∑ j, a j • q j, g⟫ := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    conv_lhs => rw [show w = ∑ j, ⟪q j, g⟫ • φ j from rfl]
    rw [sum_inner]
    exact sum_congr rfl fun j _ ↦ by
      rw [real_inner_smul_left, real_inner_smul_left]
      ring
  have hZ : ∑ k, (∑ j, Z j k * a j) ^ 2 = ∑ k, ⟪∑ j, Z j k • φ j, w⟫ ^ 2 := by
    refine sum_congr rfl fun k _ ↦ ?_
    rw [sum_inner]
    simp only [real_inner_smul_left, a]
  have hqa : ‖∑ j, a j • q j‖ ≤ γ * ‖w‖ := by
    have h1 := (hq a).trans (hZ ▸ hφ w)
    rw [← Real.sqrt_le_sqrt_iff (by positivity), Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_mul (by positivity), Real.sqrt_sq hγ, Real.sqrt_sq (norm_nonneg _)] at h1
    exact h1
  have hsq : ‖w‖ ^ 2 ≤ γ * ‖w‖ * ‖g‖ := by
    rw [hw]
    calc ⟪∑ j, a j • q j, g⟫ ≤ ‖∑ j, a j • q j‖ * ‖g‖ := real_inner_le_norm _ _
      _ ≤ γ * ‖w‖ * ‖g‖ := mul_le_mul_of_nonneg_right hqa (norm_nonneg _)
  exact le_of_sq_le_mul (norm_nonneg w) hγ (norm_nonneg g) hsq

end PDE.Analysis
