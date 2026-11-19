/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.HolderInterpolation
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import PDE.Analysis.Calculus.HalfSpaceGluing
import PDE.Analysis.Calculus.FaaDiBrunoBounds

/-!
# Continuity in a parameter of derivatives with uniform Hölder bounds

Let `f s`, `s ∈ I`, be `C^n` within the closed upper half-plane `H̄ = {y | 0 ≤ y 1}`, with its
derivatives within `H̄` of the orders `1 ≤ j ≤ n` `α`-Hölder on `H̄` with a constant `M`
independent of `s`, `α > 0`. If `f s` depends continuously on `s` uniformly on `H̄`, so does every
derivative of order at most `n`. Each order follows from the order below by the interpolation
`exists_norm_le_of_halfPlane`.

## Main results

* `uniform_iteratedFDerivWithin_of_holder`: every derivative within `H̄` of order at most `n` of
  `f s` depends continuously on `s` uniformly on `H̄`.
-/

@[expose] public section

open Set

namespace PDE.Analysis

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Continuity in a parameter of the derivatives.** If the maps `f s`, `s ∈ I`, are `C^n` within
the closed half-plane, their derivatives of the orders `1 ≤ j ≤ n` are `α`-Hölder on it with a
common constant `M`, `α > 0`, and the values are continuous in `s` uniformly on the closed
half-plane, then so are the derivatives of order at most `n`. -/
theorem uniform_iteratedFDerivWithin_of_holder {f : ℝ → ℝ^2 → F} {I : Set ℝ} {n : ℕ} {α M : ℝ}
    (hα : 0 < α) (hM : 0 ≤ M) (hf : ∀ s ∈ I, ContDiffOn ℝ n (f s) H̄)
    (hH : ∀ s ∈ I, ∀ j, 1 ≤ j → j ≤ n → ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ j (f s) H̄ y - iteratedFDerivWithin ℝ j (f s) H̄ z‖ ≤
        M * ‖y - z‖ ^ α)
    (h0 : ∀ t ∈ I, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ I, |s - t| < δ → ∀ y : ℝ^2, 0 ≤ y 1 →
      ‖f s y - f t y‖ ≤ ε) :
    ∀ j ≤ n, ∀ t ∈ I, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ I, |s - t| < δ → ∀ y : ℝ^2, 0 ≤ y 1 →
      ‖iteratedFDerivWithin ℝ j (f s) H̄ y - iteratedFDerivWithin ℝ j (f t) H̄ y‖ ≤ ε := by
  have hU := uniqueDiffOn_coordinateHalfSpace (n := 2) 1
  intro j
  induction j with
  | zero =>
    intro _ t ht ε hε
    obtain ⟨δ, hδ, h⟩ := h0 t ht ε hε
    refine ⟨δ, hδ, fun s hs hst y hy ↦ ?_⟩
    rw [iteratedFDerivWithin_zero_eq_comp, iteratedFDerivWithin_zero_eq_comp, Function.comp_apply,
      Function.comp_apply, ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]
    exact h s hs hst y hy
  | succ j ih =>
    intro hjn t ht ε hε
    obtain ⟨η, hη, hlem⟩ := exists_norm_le_of_halfPlane
      (F := ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ ℝ^2) F) (M := 2 * M) (by positivity) hα hε
    obtain ⟨δ, hδ, hδη⟩ := ih (by omega) t ht η hη
    refine ⟨δ, hδ, fun s hs hst y hy ↦ ?_⟩
    have hds : DifferentiableOn ℝ (iteratedFDerivWithin ℝ j (f s) H̄) H̄ :=
      (hf s hs).differentiableOn_iteratedFDerivWithin (by exact_mod_cast (by omega : j < n)) hU
    have hdt : DifferentiableOn ℝ (iteratedFDerivWithin ℝ j (f t) H̄) H̄ :=
      (hf t ht).differentiableOn_iteratedFDerivWithin (by exact_mod_cast (by omega : j < n)) hU
    rw [← norm_fderivWithin_iteratedFDerivWithin_sub]
    refine hlem (fun z ↦ iteratedFDerivWithin ℝ j (f s) H̄ z - iteratedFDerivWithin ℝ j (f t) H̄ z)
      (fun z ↦ fderivWithin ℝ (iteratedFDerivWithin ℝ j (f s) H̄) H̄ z -
        fderivWithin ℝ (iteratedFDerivWithin ℝ j (f t) H̄) H̄ z)
      (fun z hz ↦ (hds z hz).hasFDerivWithinAt.sub (hdt z hz).hasFDerivWithinAt)
      (fun z hz ↦ hδη s hs hst z hz) (fun z z' hz hz' ↦ ?_) y hy
    have h1 := hH s hs (j + 1) (by omega) hjn z z' hz hz'
    have h2 := hH t ht (j + 1) (by omega) hjn z z' hz hz'
    rw [← norm_fderivWithin_iteratedFDerivWithin_sub] at h1 h2
    set A := fderivWithin ℝ (iteratedFDerivWithin ℝ j (f s) H̄) H̄ z -
      fderivWithin ℝ (iteratedFDerivWithin ℝ j (f s) H̄) H̄ z'
    set B := fderivWithin ℝ (iteratedFDerivWithin ℝ j (f t) H̄) H̄ z -
      fderivWithin ℝ (iteratedFDerivWithin ℝ j (f t) H̄) H̄ z'
    have hAB : fderivWithin ℝ (iteratedFDerivWithin ℝ j (f s) H̄) H̄ z -
          fderivWithin ℝ (iteratedFDerivWithin ℝ j (f t) H̄) H̄ z -
        (fderivWithin ℝ (iteratedFDerivWithin ℝ j (f s) H̄) H̄ z' -
          fderivWithin ℝ (iteratedFDerivWithin ℝ j (f t) H̄) H̄ z') = A - B := by
      simp only [A, B]; abel
    rw [hAB]
    have h3 := norm_sub_le A B
    linarith

end PDE.Analysis
