/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic.Positivity.Finset

/-!
# Quadratic remainders of finite-rank reconstructions

A Gram bound controls the coefficients `⟪qⱼ, u⟫` in their Euclidean norm.
For a reconstruction `G u = ∑ⱼ ⟪qⱼ, u⟫ φⱼ` and bounded operators `Dⱼ`,
the remainder `∑ⱼ ⟪qⱼ, u⟫ Dⱼ (u + G u)` has a quadratic bound in `‖u‖`.
Separate bounds on the operators and their pairwise basis interactions give
the constant `M₃` in (4.28) of Hou, Wang and Yang.
No linear independence or completeness is needed.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 4.3, (4.28).
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public section

namespace PDE.Analysis

open scoped BigOperators RealInnerProductSpace
open Matrix

variable {ι H E : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Cauchy--Schwarz for finite coefficient families with supplied squared budgets. -/
theorem sum_abs_mul_le_of_sq_le (c d : ι → ℝ) {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hc : ∑ i, c i ^ 2 ≤ C ^ 2) (hd : ∑ i, d i ^ 2 ≤ D ^ 2) :
    ∑ i, |c i| * |d i| ≤ C * D := by
  apply (sq_le_sq₀ (by positivity) (mul_nonneg hC hD)).mp
  calc
    (∑ i, |c i| * |d i|) ^ 2 ≤ (∑ i, c i ^ 2) * (∑ i, d i ^ 2) := by
      simpa only [sq_abs] using
        Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) Finset.univ
          (fun i ↦ |c i|) (fun i ↦ |d i|)
    _ ≤ C ^ 2 * D ^ 2 := by gcongr
    _ = (C * D) ^ 2 := (mul_pow C D 2).symm

/-- A bound on the Gram quadratic form bounds all analysis coefficients. -/
theorem sum_sq_inner_le_of_gram_le (q : ι → H) {g : ℝ} (hg : 0 ≤ g)
    (hgram : ∀ c : ι → ℝ,
      c ⬝ᵥ (Matrix.gram ℝ q) *ᵥ c ≤ g * ∑ i, c i ^ 2) (u : H) :
    ∑ i, ⟪q i, u⟫ ^ 2 ≤ g * ‖u‖ ^ 2 := by
  let c : ι → ℝ := fun i ↦ ⟪q i, u⟫
  let s : H := ∑ i, c i • q i
  have hnorm : ‖s‖ ^ 2 ≤ g * ∑ i, c i ^ 2 := by
    have hid : c ⬝ᵥ (Matrix.gram ℝ q) *ᵥ c = ‖s‖ ^ 2 := by
      simpa [s] using Matrix.star_dotProduct_gram_mulVec q c c
    simpa only [hid] using hgram c
  have hinner : ⟪s, u⟫ = ∑ i, c i ^ 2 := by
    simp only [s, sum_inner, real_inner_smul_left, c, pow_two]
  have hcs := abs_real_inner_le_norm s u
  rw [hinner, abs_of_nonneg (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)] at hcs
  have hsumsq : (∑ i, c i ^ 2) ^ 2 ≤ g * (∑ i, c i ^ 2) * ‖u‖ ^ 2 := by
    calc
      _ ≤ (‖s‖ * ‖u‖) ^ 2 :=
        (sq_le_sq₀ (by positivity) (by positivity)).mpr hcs
      _ = ‖s‖ ^ 2 * ‖u‖ ^ 2 := mul_pow _ _ _
      _ ≤ (g * ∑ i, c i ^ 2) * ‖u‖ ^ 2 := by gcongr
  change ∑ i, c i ^ 2 ≤ g * ‖u‖ ^ 2
  by_cases hzero : ∑ i, c i ^ 2 = 0
  · simpa only [hzero] using mul_nonneg hg (sq_nonneg ‖u‖)
  · have hpos : 0 < ∑ i, c i ^ 2 :=
      lt_of_le_of_ne (Finset.sum_nonneg fun i _ ↦ sq_nonneg _) (Ne.symm hzero)
    nlinarith only [hsumsq, hpos]

/-- Operator and pairwise interaction budgets give the sharp finite-rank
quadratic remainder bound. The coefficient budget can come from a Gram certificate. -/
theorem norm_finiteRank_remainder_le (c : ι → ℝ) (φ : ι → H)
    (D : ι → H →L[ℝ] E) (u : H) {C A B : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hc : ∑ i, c i ^ 2 ≤ C ^ 2 * ‖u‖ ^ 2)
    (hD : ∑ i, ‖D i‖ ^ 2 ≤ A ^ 2)
    (hinteraction : ∑ i, ∑ j, ‖D j (φ i)‖ ^ 2 ≤ B ^ 2) :
    ‖∑ j, c j • D j (u + ∑ i, c i • φ i)‖ ≤
      (C * A + C ^ 2 * B) * ‖u‖ ^ 2 := by
  have hlinear : ∑ j, |c j| * ‖D j‖ ≤ C * ‖u‖ * A := by
    simpa only [abs_norm] using sum_abs_mul_le_of_sq_le c (fun j ↦ ‖D j‖)
      (mul_nonneg hC (norm_nonneg _)) hA (by simpa only [mul_pow] using hc) hD
  have hquadratic : ∑ i, ∑ j, |c i * c j| * ‖D j (φ i)‖ ≤
      (C * ‖u‖) ^ 2 * B := by
    have hpair : ∑ ij : ι × ι, (c ij.1 * c ij.2) ^ 2 ≤ ((C * ‖u‖) ^ 2) ^ 2 := by
      have h := mul_self_le_mul_self (Finset.sum_nonneg fun i _ ↦ sq_nonneg _) hc
      simpa only [Fintype.sum_prod_type, mul_pow, pow_two, Finset.sum_mul,
        Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using h
    simpa only [Fintype.sum_prod_type, abs_norm] using
      sum_abs_mul_le_of_sq_le (fun ij : ι × ι ↦ c ij.1 * c ij.2)
        (fun ij ↦ ‖D ij.2 (φ ij.1)‖) (sq_nonneg _) hB hpair
        (by simpa only [Fintype.sum_prod_type] using hinteraction)
  have hsplit : (∑ j, c j • D j (u + ∑ i, c i • φ i)) =
      (∑ j, c j • D j u) + ∑ i, ∑ j, (c i * c j) • D j (φ i) := by
    simp only [map_add, map_sum, map_smul, smul_add, Finset.sum_add_distrib,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [hsplit]
  calc
    _ ≤ ‖∑ j, c j • D j u‖ + ‖∑ i, ∑ j, (c i * c j) • D j (φ i)‖ :=
      norm_add_le _ _
    _ ≤ (∑ j, |c j| * ‖D j‖) * ‖u‖ +
        ∑ i, ∑ j, |c i * c j| * ‖D j (φ i)‖ := by
      apply add_le_add
      · calc
          _ ≤ ∑ j, ‖c j • D j u‖ := norm_sum_le _ _
          _ ≤ ∑ j, |c j| * (‖D j‖ * ‖u‖) := by
            simp only [norm_smul, Real.norm_eq_abs]
            exact Finset.sum_le_sum fun j _ ↦
              mul_le_mul_of_nonneg_left ((D j).le_opNorm u) (abs_nonneg _)
          _ = _ := by simp only [Finset.sum_mul, mul_assoc]
      · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦
          (norm_sum_le _ _).trans_eq (by simp only [norm_smul, Real.norm_eq_abs]))
    _ ≤ (C * ‖u‖ * A) * ‖u‖ + (C * ‖u‖) ^ 2 * B := by gcongr
    _ = (C * A + C ^ 2 * B) * ‖u‖ ^ 2 := by ring

/-- A Gram quadratic-form certificate and finite basis bounds control the
nonlinear reconstruction in the original Hilbert norm. -/
theorem norm_finiteRank_remainder_le_of_gram_le (q φ : ι → H)
    (D : ι → H →L[ℝ] E) (u : H) {g A B : ℝ}
    (hg : 0 ≤ g) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hgram : ∀ c : ι → ℝ,
      c ⬝ᵥ (Matrix.gram ℝ q) *ᵥ c ≤ g * ∑ i, c i ^ 2)
    (hD : ∑ i, ‖D i‖ ^ 2 ≤ A ^ 2)
    (hinteraction : ∑ i, ∑ j, ‖D j (φ i)‖ ^ 2 ≤ B ^ 2) :
    ‖∑ j, ⟪q j, u⟫ • D j (u + ∑ i, ⟪q i, u⟫ • φ i)‖ ≤
      (Real.sqrt g * A + g * B) * ‖u‖ ^ 2 := by
  simpa only [Real.sq_sqrt hg] using norm_finiteRank_remainder_le
    (fun j ↦ ⟪q j, u⟫) φ D u (Real.sqrt_nonneg g) hA hB
    (by simpa only [Real.sq_sqrt hg] using sum_sq_inner_le_of_gram_le q hg hgram u)
    hD hinteraction

end PDE.Analysis
