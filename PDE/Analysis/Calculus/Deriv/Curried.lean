/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Partial derivatives of a function of two real variables

For `G : ℝ → ℝ → ℝ`, `derivX G x y` differentiates `G` in its first variable along the horizontal
line through `(x, y)` and `derivY G x y` in its second variable along the vertical line. Their
iterates are one-variable iterated derivatives (`derivX_iterate_apply`, `derivY_iterate_apply`).
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

/-- The derivative in the first variable along horizontal lines. -/
def derivX (G : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := deriv (fun t ↦ G t y) x

/-- The derivative in the second variable along vertical lines. -/
def derivY (G : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := deriv (fun t ↦ G x t) y

/-- The iterates of `derivY` are iterated derivatives along vertical lines. -/
theorem derivY_iterate_apply (G : ℝ → ℝ → ℝ) (j : ℕ) (x y : ℝ) :
    (derivY^[j] G) x y = iteratedDeriv j (G x) y := by
  induction j generalizing y with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', iteratedDeriv_succ]
    simp only [derivY]
    congr 1
    funext t
    exact ih t

/-- The iterates of `derivX` are iterated derivatives along horizontal lines. -/
theorem derivX_iterate_apply (G : ℝ → ℝ → ℝ) (i : ℕ) (x y : ℝ) :
    (derivX^[i] G) x y = iteratedDeriv i (fun t ↦ G t y) x := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', iteratedDeriv_succ]
    simp only [derivX]
    congr 1
    funext t
    exact ih t

end PDE.Analysis
