/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.SmoothMaximalExistence

import CAS.ExactTactic

/-!
# A smooth wave with reaction `r³ - r`

For smooth compactly supported data on `ℝ³` and the reaction `f(r) = r³ - r`, which is
not globally Lipschitz, the maximal existence theorem `exists_maximal_smooth_wave` gives
a time `L > 0` and a solution of `□u + f(u) = 0` that is smooth on `0 ≤ t < L` and
attains both initial data.
-/

@[expose] public noncomputable section

open PDE.Common Set
open scoped ENNReal

namespace PDE.Examples.Cauchy

open PDE.Hyperbolic.NonlinearWave.Cauchy WaveEquation

/-- Smooth compact data give a smooth solution on `[0, L)` for the reaction `r³ - r`. -/
example (g h : ℝ^3 → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) :
    ∃ L : ℝ≥0∞, 0 < L ∧ ∃ u : ℝ^4 → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) u {p | 0 ≤ p 0 ∧ ENNReal.ofReal (p 0) < L} ∧
      (∀ y, u (timeSpaceCons 0 y) = g y) ∧
      (∀ y, HasDerivWithinAt (fun t ↦ u (timeSpaceCons t y)) (h y) (Ici 0) 0) ∧
      (∀ t : ℝ, 0 < t → ENNReal.ofReal t < L → ∀ y : ℝ^3,
        waveOperator u (timeSpaceCons t y) +
          ((u (timeSpaceCons t y)) ^ 3 - u (timeSpaceCons t y)) = 0) := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun r : ℝ ↦ r ^ 3 - r) := by fun_prop
  have hf0 : (fun r : ℝ ↦ r ^ 3 - r) 0 = 0 := by cas
  obtain ⟨L, hL, u, hu, hug, huh, hwave, _, _⟩ :=
    exists_maximal_smooth_wave hs hf0 g h hg hh hgc hhc
  exact ⟨L, hL, u, hu, hug, huh, hwave⟩

end PDE.Examples.Cauchy
