/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.SpaceTime.Gradient.Basic
import PDE.FDeriv.Calculus
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Regularity of spatial gradients

Spacetime coordinate zero is time. Taking the gradient in the remaining coordinates
loses one finite differentiability order and preserves smoothness. The local and open-set
statements use ambient derivatives, so openness is explicit in the latter.
-/

@[expose] public section

open PDE

set_option linter.missingDocs true

namespace PDE

/-- A spatial gradient loses one finite order of local differentiability. -/
theorem contDiffAt_spatialGradient {n m : ℕ} {v : ℝ^(n + 1) → ℝ}
    {x : ℝ^(n + 1)} (hv : ContDiffAt ℝ (m + 1) v x) :
    ContDiffAt ℝ m (spatialGradient v) x := by
  apply (contDiffAt_piLp 2).mpr
  intro i
  simpa only [spatialGradient_apply] using contDiffAt_partialDeriv m hv i.succ

/-- A spatial gradient loses one finite differentiability order on an open set. -/
theorem contDiffOn_spatialGradient {n m : ℕ} {v : ℝ^(n + 1) → ℝ}
    {Ω : Set (ℝ^(n + 1))} (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ (m + 1) v Ω) :
    ContDiffOn ℝ m (spatialGradient v) Ω := by
  exact hΩ.contDiffOn_iff.mpr fun _ hx ↦
    contDiffAt_spatialGradient (hv.contDiffAt (hΩ.mem_nhds hx))

/-- The spatial gradient of a globally `C^(m+1)` field is `C^m`. -/
theorem contDiff_spatialGradient_of_succ {n m : ℕ} {v : ℝ^(n + 1) → ℝ}
    (hv : ContDiff ℝ (m + 1) v) : ContDiff ℝ m (spatialGradient v) := by
  apply (contDiff_piLp 2).mpr
  intro i
  simpa only [spatialGradient_apply] using
    contDiff_partialDeriv_of_succ (i := i.succ) hv

/-- The spatial gradient of a smooth spacetime scalar field is smooth. -/
theorem contDiff_top_spatialGradient {n : ℕ} {v : ℝ^(n + 1) → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) : ContDiff ℝ (⊤ : ℕ∞) (spatialGradient v) := by
  apply (contDiff_piLp 2).mpr
  intro i
  simpa only [spatialGradient_apply] using contDiff_top_partialDeriv (i := i.succ) hv

end PDE
