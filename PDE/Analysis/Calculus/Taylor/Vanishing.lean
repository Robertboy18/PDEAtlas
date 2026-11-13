/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Vanishing to high order from a bounded top derivative

If the derivatives of orders `j < n` of a `Cⁿ` function vanish at the origin and the `n`-th
derivative is bounded by `δ` on a star-convex set around the origin, then on that set the
derivative of order `j` is at most `δ ‖y‖^(n - j)`. The proof is the mean value inequality on the
segment from `0`, applied from the top order down; no Taylor polynomial is formed, so the
constants are the crude ones (`1` instead of `1/(n - j)!`).

## Main results

* `PDE.Analysis.norm_iteratedFDeriv_le_mul_pow_of_vanishing`: the bound for every `j ≤ n`.
* `PDE.Analysis.norm_le_mul_pow_of_vanishing`, `PDE.Analysis.norm_fderiv_le_mul_pow_of_vanishing`:
  the cases `j = 0` and `j = 1`.
-/

@[expose] public section

open Set

namespace PDE.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Vanishing to order `n` from a bounded `n`-th derivative.** If `f` is `Cⁿ`, its derivatives
of order `j < n` vanish at `0`, and `‖Dⁿ f‖ ≤ δ` on a set `S` star-convex at `0`, then
`‖Dʲ f(y)‖ ≤ δ ‖y‖^(n - j)` for `y ∈ S` and `j ≤ n`. -/
theorem norm_iteratedFDeriv_le_mul_pow_of_vanishing {f : E → F} {n : ℕ} (hf : ContDiff ℝ n f)
    {S : Set E} (hS : StarConvex ℝ 0 S) (h0 : ∀ j < n, iteratedFDeriv ℝ j f 0 = 0) {δ : ℝ}
    (hδ : ∀ z ∈ S, ‖iteratedFDeriv ℝ n f z‖ ≤ δ) {j : ℕ} (hj : j ≤ n) {y : E} (hy : y ∈ S) :
    ‖iteratedFDeriv ℝ j f y‖ ≤ δ * ‖y‖ ^ (n - j) := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ y hy)
  suffices key : ∀ k ≤ n, ∀ y ∈ S, ‖iteratedFDeriv ℝ (n - k) f y‖ ≤ δ * ‖y‖ ^ k by
    have := key (n - j) (Nat.sub_le n j) y hy
    rwa [Nat.sub_sub_self hj] at this
  intro k
  induction k with
  | zero => intro _ z hz; simpa using hδ z hz
  | succ k ih =>
    intro hk z hz
    set i := n - (k + 1) with hi
    have hin : i < n := by omega
    have hi1 : i + 1 = n - k := by omega
    have hseg : segment ℝ 0 z ⊆ S := hS.segment_subset hz
    have hdiff : ∀ w ∈ segment ℝ 0 z, HasFDerivWithinAt (iteratedFDeriv ℝ i f)
        (fderiv ℝ (iteratedFDeriv ℝ i f) w) (segment ℝ 0 z) w := fun w _ ↦
      ((hf.differentiable_iteratedFDeriv (by exact_mod_cast hin)) w).hasFDerivAt.hasFDerivWithinAt
    have hbound : ∀ w ∈ segment ℝ 0 z, ‖fderiv ℝ (iteratedFDeriv ℝ i f) w‖ ≤ δ * ‖z‖ ^ k := by
      intro w hw
      rw [norm_fderiv_iteratedFDeriv, hi1]
      refine (ih (by omega) w (hseg hw)).trans ?_
      gcongr
      obtain ⟨a, b, ha, hb, hab, rfl⟩ := hw
      simp only [smul_zero, zero_add, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
      exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
    have hmv := (convex_segment (0 : E) z).norm_image_sub_le_of_norm_hasFDerivWithin_le hdiff
      hbound (left_mem_segment ℝ 0 z) (right_mem_segment ℝ 0 z)
    rw [h0 i hin, sub_zero, sub_zero] at hmv
    calc ‖iteratedFDeriv ℝ i f z‖ ≤ δ * ‖z‖ ^ k * ‖z‖ := hmv
      _ = δ * ‖z‖ ^ (k + 1) := by ring

/-- The case `j = 0` of `norm_iteratedFDeriv_le_mul_pow_of_vanishing`: `‖f y‖ ≤ δ ‖y‖ⁿ`. -/
theorem norm_le_mul_pow_of_vanishing {f : E → F} {n : ℕ} (hf : ContDiff ℝ n f)
    {S : Set E} (hS : StarConvex ℝ 0 S) (h0 : ∀ j < n, iteratedFDeriv ℝ j f 0 = 0) {δ : ℝ}
    (hδ : ∀ z ∈ S, ‖iteratedFDeriv ℝ n f z‖ ≤ δ) {y : E} (hy : y ∈ S) :
    ‖f y‖ ≤ δ * ‖y‖ ^ n := by
  simpa using norm_iteratedFDeriv_le_mul_pow_of_vanishing hf hS h0 hδ (Nat.zero_le n) hy

/-- The case `j = 1` of `norm_iteratedFDeriv_le_mul_pow_of_vanishing`:
`‖Df(y)‖ ≤ δ ‖y‖^(n - 1)`. -/
theorem norm_fderiv_le_mul_pow_of_vanishing {f : E → F} {n : ℕ} (hf : ContDiff ℝ n f)
    (hn : 1 ≤ n) {S : Set E} (hS : StarConvex ℝ 0 S) (h0 : ∀ j < n, iteratedFDeriv ℝ j f 0 = 0)
    {δ : ℝ} (hδ : ∀ z ∈ S, ‖iteratedFDeriv ℝ n f z‖ ≤ δ) {y : E} (hy : y ∈ S) :
    ‖fderiv ℝ f y‖ ≤ δ * ‖y‖ ^ (n - 1) := by
  rw [← norm_iteratedFDeriv_one]
  exact norm_iteratedFDeriv_le_mul_pow_of_vanishing hf hS h0 hδ hn hy

end PDE.Analysis
