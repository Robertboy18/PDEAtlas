/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.FDeriv.PartialDeriv.HigherNormSq
public import PDE.Analysis.Calculus.AnalyticDerivativeBounds

/-!
# Analyticity from factorial bounds on coordinate norms

## Motivation

When do bounds on the coordinate norms of the derivatives of a smooth function on `ℝ^n` make it
real-analytic?

## The idea

A function is real-analytic near a point as soon as its derivatives of order `i` are at most
`i! M Kⁱ` on a ball. For the operator norm of `iteratedFDeriv` this is
`PDE.Analysis.analyticAt_iff_exists_norm_iteratedFDeriv_le`. The coordinate norm controls the
operator norm up to the factor `√(n^i)`, which only changes the rate `K`, so the same criterion
holds for coordinate norms. The bound of order zero is free: a continuous function is bounded on
a smaller closed ball.

## Main results

* `analyticAt_of_iteratedCoordinateNorm_le`: a function that is smooth on a ball around `x₀`,
  with `|Dⁱf| ≤ i! M Kⁱ` there in the coordinate norm for all `i ≥ 1`, is analytic at `x₀`.
  All dimensions, all real Banach targets.

## Relations

The proof is `norm_iteratedFDeriv_le_sqrt_mul_iteratedCoordinateNorm` followed by
`PDE.Analysis.analyticAt_iff_exists_norm_iteratedFDeriv_le`. The harmonic case
`LaplacianEquation.IsHarmonicPDE.analyticOnNhd` bounds operator norms directly.

## What stays open

The converse (an analytic function has such bounds) is not stated for coordinate norms here.
-/

@[expose] public noncomputable section

open Metric Set
open scoped ContDiff Topology NNReal

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace PDE

/-- **Analyticity from factorial bounds on coordinate norms.** Let `f` be smooth on the ball of
radius `r` around `x₀`, and suppose `|Dⁱf(x)| ≤ i! M Kⁱ` in the coordinate norm for all `i ≥ 1`
and all `x` in the ball. Then `f` is real-analytic at `x₀`. The coordinate norm bounds the
operator norm of the derivative up to `√(n^i)`, and the Taylor series converges. -/
theorem analyticAt_of_iteratedCoordinateNorm_le [CompleteSpace F] {f : ℝ^n → F} {x₀ : ℝ^n}
    {r M K : ℝ} (hr : 0 < r) (hf : ContDiffOn ℝ ∞ f (ball x₀ r))
    (hb : ∀ i, 1 ≤ i → ∀ x ∈ ball x₀ r, iteratedCoordinateNorm i f x ≤ i.factorial * M * K ^ i) :
    AnalyticAt ℝ f x₀ := by
  -- a bound for `f` itself on a smaller closed ball
  have hsub : closedBall x₀ (r / 2) ⊆ ball x₀ r := closedBall_subset_ball (by linarith)
  obtain ⟨S, hS⟩ := (isCompact_closedBall x₀ (r / 2)).exists_bound_of_continuousOn
    (hf.continuousOn.mono hsub)
  -- constants for the operator norms
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = |M| + |S| := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  obtain ⟨K', hK'def⟩ : ∃ K' : ℝ, K' = ((n : ℝ) + 1) * |K| + 1 := ⟨_, rfl⟩
  have hK'0 : 0 < K' := by rw [hK'def]; positivity
  have hball : ball x₀ (r / 2) ⊆ ball x₀ r := ball_subset_ball (by linarith)
  -- the bounds on the operator norms
  have hbound : ∀ k : ℕ, ∀ y ∈ ball x₀ (r / 2),
      ‖iteratedFDeriv ℝ k f y‖ ≤ (k.factorial : ℝ) * C * K' ^ k := by
    intro k y hy
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have hy' : y ∈ closedBall x₀ (r / 2) := ball_subset_closedBall hy
      have h1 : |S| ≤ C := by rw [hCdef]; linarith [abs_nonneg M]
      simpa [norm_iteratedFDeriv_zero] using ((hS y hy').trans (le_abs_self S)).trans h1
    have hyr : y ∈ ball x₀ r := hball hy
    have hfy : ContDiffAt ℝ k f y :=
      (hf.contDiffAt (isOpen_ball.mem_nhds hyr)).of_le (by exact_mod_cast le_top)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    -- `√(n^k) ≤ (n + 1)^k`
    have hsqrt : √((n : ℝ) ^ k) ≤ ((n : ℝ) + 1) ^ k := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      have h1 : (n : ℝ) ^ k ≤ ((n : ℝ) + 1) ^ k := pow_le_pow_left₀ hn (by linarith) k
      have h2 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ k := one_le_pow₀ (by linarith)
      nlinarith
    have hfac : (0 : ℝ) ≤ k.factorial := Nat.cast_nonneg _
    have hMK : (k.factorial : ℝ) * M * K ^ k ≤ k.factorial * |M| * |K| ^ k := by
      have h1 : M * K ^ k ≤ |M| * |K| ^ k := by
        rw [← abs_pow, ← abs_mul]
        exact le_abs_self _
      calc (k.factorial : ℝ) * M * K ^ k = k.factorial * (M * K ^ k) := by ring
        _ ≤ k.factorial * (|M| * |K| ^ k) := mul_le_mul_of_nonneg_left h1 hfac
        _ = _ := by ring
    have hcoord : iteratedCoordinateNorm k f y ≤ k.factorial * |M| * |K| ^ k :=
      (hb k hk y hyr).trans hMK
    have hK'le : ((n : ℝ) + 1) * |K| ≤ K' := by rw [hK'def]; linarith
    calc ‖iteratedFDeriv ℝ k f y‖
        ≤ √((n : ℝ) ^ k) * iteratedCoordinateNorm k f y :=
          norm_iteratedFDeriv_le_sqrt_mul_iteratedCoordinateNorm k hfy
      _ ≤ ((n : ℝ) + 1) ^ k * (k.factorial * |M| * |K| ^ k) :=
          mul_le_mul hsqrt hcoord (iteratedCoordinateNorm_nonneg k f y) (by positivity)
      _ = k.factorial * |M| * (((n : ℝ) + 1) * |K|) ^ k := by rw [mul_pow]; ring
      _ ≤ k.factorial * C * K' ^ k := by
          have h1 : |M| ≤ C := by rw [hCdef]; linarith [abs_nonneg S]
          have h2 : (((n : ℝ) + 1) * |K|) ^ k ≤ K' ^ k :=
            pow_le_pow_left₀ (by positivity) hK'le k
          exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hfac) h2 (by positivity)
            (by positivity)
  exact PDE.Analysis.analyticAt_iff_exists_norm_iteratedFDeriv_le.mpr
    ⟨r / 2, by linarith, hf.mono hball, C, K', hC0, hK'0, hbound⟩

end PDE
