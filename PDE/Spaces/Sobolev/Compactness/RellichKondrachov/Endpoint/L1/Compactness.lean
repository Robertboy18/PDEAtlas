/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.Endpoint.L1.GridApproximation
public import PDE.Spaces.Sobolev.Compactness.Rellich.Topology

/-!
# Compactness from bounded support and translation control in L1

A bounded family of `L¹` functions with a common bounded support and a common
linear translation modulus is totally bounded. The proof uses the finite-rank
grid averages and their explicit approximation error. No Sobolev extension,
atlas, boundary trace, or dimension hypothesis enters.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace.RellichKondrachov

open MeasureTheory Set
open scoped ENNReal Topology

variable {n : ℕ}

/-- Bounded support and a uniform linear translation modulus make a bounded
family in global `L¹` totally bounded, by finite-rank grid approximation. -/
theorem totallyBounded_L1_of_bounded_support_translation
    (S : Set (DerivLp n 1 Set.univ)) (hS : Bornology.IsBounded S)
    (R C : ℝ) (hC : 0 ≤ C)
    (hsupport : ∀ f ∈ S, ∀ᵐ x ∂volume,
      x ∉ Metric.ball (0 : ℝ^n) R → f x = 0)
    (htrans : ∀ f ∈ S, ∀ h : ℝ^n,
      ‖Rellich.translateLp 1 h f - f‖ ≤ ‖h‖ * C) :
    TotallyBounded S := by
  apply Rellich.totallyBounded_of_uniform_compact_approximation S hS
  intro ε hε
  let A : ℝ := (2 : ℝ) ^ n * √n * C
  have hA : 0 ≤ A := mul_nonneg
    (mul_nonneg (pow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)) hC
  let δ : ℝ := ε / (A + 1)
  have hden : 0 < A + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  refine ⟨euclideanGridAverageL1 δ R,
    euclideanGridAverageL1.isCompactOperator δ R, ?_⟩
  intro f hf
  have hsupp :
      ∀ᵐ x ∂volume, x ∉ ⋃ k ∈ Rellich.euclideanGridIndicesForBall (n := n) δ R,
          Rellich.euclideanGridCell (n := n) δ k → f x = 0 := by
    filter_upwards [hsupport f hf] with x hx hxGrid
    apply hx
    intro hxBall
    exact hxGrid (Rellich.ball_subset_iUnion_euclideanGridCell hδ hxBall)
  calc
    ‖euclideanGridAverageL1 δ R f - f‖ ≤
        (2 : ℝ) ^ n * √n * δ * C :=
      euclideanGridAverageL1.norm_sub_le hδ hC R f hsupp (htrans f hf)
    _ = A * δ := by dsimp [A]; ring
    _ < (A + 1) * δ := mul_lt_mul_of_pos_right (by linarith) hδ
    _ = ε := by dsimp [δ]; field_simp

end SobolevSpace.GraphSpace.RellichKondrachov
