/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import PDE.Analysis.Calculus.LocalExtension.Cubic.Rescaling

import CAS.ExactTactic

/-!
# Derivative bounds for a cubic correction in a fixed coordinate

The scalar rescaling is composed with a fixed state coordinate and multiplied by
a fixed vector field. Mathlib's higher derivative estimates control both
operations. The resulting bound is linear in the shrinking parameter, including
the full second Fréchet derivative.

The coordinate, vector field, and their derivative bounds are fixed before the
shrinking parameter is chosen. No bound on the value of the coordinate is needed.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace PDE.Analysis

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A cubic scalar cutoff remains small through two derivatives after composition
with a fixed coordinate and multiplication by a fixed vector field. All bounds
on the coordinate and vector field are pointwise at `x`; uniform hypotheses give
the same estimate on the whole state space. -/
theorem norm_iteratedFDeriv_cubicRescale_comp_smul_le
    {φ : ℝ → ℝ} {m : E → ℝ} {A : E → V} {C D ε : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hm : ContDiff ℝ 2 m) (hA : ContDiff ℝ 2 A)
    (hD : 1 ≤ D) (hε : 0 < ε) (hεone : ε ≤ 1)
    (hφ0 : ∀ s, ‖φ s‖ ≤ C)
    (hφ1 : ∀ s, ‖deriv φ s‖ ≤ C)
    (hφ2 : ∀ s, ‖deriv (deriv φ) s‖ ≤ C)
    (x : E)
    (hmBound : ∀ i, 1 ≤ i → i ≤ 2 → ‖iteratedFDeriv ℝ i m x‖ ≤ D)
    (hABound : ∀ i, i ≤ 2 → ‖iteratedFDeriv ℝ i A x‖ ≤ D)
    {n : ℕ} (hn : n ≤ 2) :
    ‖iteratedFDeriv ℝ n (fun y ↦ cubicRescale φ ε (m y) • A y) x‖ ≤
      8 * D ^ 3 * C * ε := by
  have hC : 0 ≤ C := (norm_nonneg (φ 0)).trans (hφ0 0)
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hg : ContDiff ℝ 2 (cubicRescale φ ε) := contDiff_cubicRescale hφ ε
  have hK : 0 ≤ 2 * D ^ 2 * C * ε := by positivity
  have hscalar (i : ℕ) (hi : i ≤ 2) :
      ‖iteratedFDeriv ℝ i (cubicRescale φ ε ∘ m) x‖ ≤
        2 * D ^ 2 * C * ε := by
    have hiOrder : (i : ℕ∞ω) ≤ 2 := by exact_mod_cast hi
    have hinner (j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) :
        ‖iteratedFDeriv ℝ j m x‖ ≤ D ^ j := by
      have hj2 : j ≤ 2 := hji.trans hi
      refine (hmBound j hj hj2).trans ?_
      interval_cases j
      · simp only [pow_one, le_refl]
      · have hpow : D ≤ D ^ 2 := by cas using [hD]
        exact hpow
    have hcomp := norm_iteratedFDeriv_comp_le hg hm hiOrder x
      (fun j hj ↦ norm_iteratedFDeriv_cubicRescale_le
        hφ hε hεone hφ0 hφ1 hφ2 (hj.trans hi) (m x)) hinner
    refine hcomp.trans ?_
    interval_cases i
    · norm_num only [Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul, mul_one]
      have hfactor : 1 ≤ 2 * D ^ 2 := by cas using [hD]
      calc
        C * ε = 1 * (C * ε) := (one_mul _).symm
        _ ≤ (2 * D ^ 2) * (C * ε) :=
          mul_le_mul_of_nonneg_right hfactor (mul_nonneg hC hε.le)
        _ = 2 * D ^ 2 * C * ε := by cas
    · norm_num only [Nat.factorial_one, Nat.cast_one, pow_one, one_mul]
      cas using [hC, hε, hD]
    · norm_num only [Nat.factorial_succ, Nat.factorial_one, Nat.cast_mul,
        Nat.cast_ofNat, Nat.cast_one, mul_one]
      cas
  have hnOrder : (n : ℕ∞ω) ≤ 2 := by exact_mod_cast hn
  refine (norm_iteratedFDeriv_smul_le (hg.comp hm) hA x hnOrder).trans ?_
  calc
    ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (cubicRescale φ ε ∘ m) x‖ *
          ‖iteratedFDeriv ℝ (n - i) A x‖
        ≤ ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * (2 * D ^ 2 * C * ε) * D := by
      apply Finset.sum_le_sum
      intro i hi
      have hi2 : i ≤ 2 := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hn
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hscalar i hi2) (Nat.cast_nonneg _))
        (hABound (n - i) ((Nat.sub_le n i).trans hn))
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hK)
    _ ≤ 8 * D ^ 3 * C * ε := by
      interval_cases n
      · norm_num [Finset.sum_range_succ]
        cas using [hC, hε, hD]
      · norm_num [Finset.sum_range_succ]
        cas using [hC, hε, hD]
      · norm_num [Finset.sum_range_succ]
        cas

end PDE.Analysis
