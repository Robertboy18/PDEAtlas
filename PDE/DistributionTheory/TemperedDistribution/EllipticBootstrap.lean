/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TemperedDistribution.Sobolev

/-!
# Integer regularity for the massive Laplacian

An L² distribution solving `(1 - Δ)u = g` gains two derivatives beyond the
integer Sobolev order of `g`. The bootstrap starts at order zero and uses the
whole-space Bessel regularity theorem at each step. Higher regularity of `u`
is a conclusion.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal SchwartzMap Laplacian

namespace TemperedDistribution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {u : 𝓢'(E, F)}

/-- An order-zero solution of the massive Laplace equation gains two orders
beyond any integer regularity of its load. The target is any complex Hilbert space. -/
theorem MemSobolev.add_two_of_sub_laplacian (hu : MemSobolev 0 2 u) (k : ℕ)
    (hg : MemSobolev (k : ℝ) 2 (u - Δ u)) :
    MemSobolev ((k : ℝ) + 2) 2 u := by
  induction k with
  | zero =>
      simp only [Nat.cast_zero] at hg ⊢
      have hΔ : MemSobolev 0 2 (Δ u) := by
        simpa only [sub_sub_cancel] using hu.sub hg
      exact hu.add_two_of_laplacian hΔ
  | succ k ih =>
      have hg' : MemSobolev (k : ℝ) 2 (u - Δ u) :=
        hg.mono (show (k : ℝ) ≤ (k.succ : ℝ) by exact_mod_cast Nat.le_succ k)
      have hu' : MemSobolev ((k + 1 : ℕ) : ℝ) 2 u :=
        (ih hg').mono (show ((k + 1 : ℕ) : ℝ) ≤ (k : ℝ) + 2 by
          push_cast
          linarith)
      have hΔ : MemSobolev ((k + 1 : ℕ) : ℝ) 2 (Δ u) := by
        simpa only [sub_sub_cancel] using hu'.sub hg
      exact hu'.add_two_of_laplacian hΔ

end TemperedDistribution
