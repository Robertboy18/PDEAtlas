/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Smoothness across a Sobolev scale

A time derivative may lose spatial orders. If a compatible family of continuous
curves satisfies such derivative identities at every order, with smooth source
maps, induction gives all time derivatives at every fixed order. No single
Banach space is required to contain the vector field without loss.
-/

@[expose] public section

open Set

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

/-- Right or two-sided derivative identities on a uniquely differentiable
set give all time derivatives simultaneously across a scale. -/
theorem contDiffOn_scale_of_hasDerivWithinAt {E : ℕ → Type*} [∀ j, NormedAddCommGroup (E j)]
    [∀ j, NormedSpace ℝ (E j)] {s : Set ℝ} (hs : UniqueDiffOn ℝ s) (next : ℕ → ℕ) (u : ∀ j, ℝ → E j)
    (F : ∀ j, E (next j) → E j) (hu : ∀ j, ContinuousOn (u j) s)
    (hF : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (F j))
    (hd : ∀ j, ∀ t ∈ s, HasDerivWithinAt (u j) (F j (u (next j) t)) s t) :
    ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (u j) s := by
  have hfinite : ∀ r : ℕ, ∀ j, ContDiffOn ℝ r (u j) s := by
    intro r
    induction r with
    | zero =>
      exact fun j ↦ contDiffOn_zero.mpr (hu j)
    | succ r ih =>
      intro j
      rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_derivWithin hs]
      refine ⟨fun t ht ↦ (hd j t ht).differentiableWithinAt, by simp, ?_⟩
      have hcomp : ContDiffOn ℝ r (fun t ↦ F j (u (next j) t)) s :=
        ((hF j).of_le (by simp)).comp_contDiffOn (ih (next j))
      exact hcomp.congr (fun t ht ↦ (hd j t ht).derivWithin (hs t ht))
  exact fun j ↦ contDiffOn_infty.mpr (fun r ↦ hfinite r j)

/-- A smooth equation on a scale of normed spaces gives smooth time dependence
at every level, even when each derivative uses a strictly higher level. -/
theorem contDiffOn_scale_of_hasDerivAt {E : ℕ → Type*} [∀ j, NormedAddCommGroup (E j)]
    [∀ j, NormedSpace ℝ (E j)] {s : Set ℝ} (hs : IsOpen s) (next : ℕ → ℕ) (u : ∀ j, ℝ → E j)
    (F : ∀ j, E (next j) → E j) (hu : ∀ j, ContinuousOn (u j) s)
    (hF : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (F j))
    (hd : ∀ j, ∀ t ∈ s, HasDerivAt (u j) (F j (u (next j) t)) t) :
    ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (u j) s :=
  contDiffOn_scale_of_hasDerivWithinAt hs.uniqueDiffOn next u F hu hF
    (fun j t ht ↦ (hd j t ht).hasDerivWithinAt)

end PDE.Hyperbolic.NonlinearWave.Cauchy
