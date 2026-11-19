/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.ConvolutionSpace.SpatialDerivatives
public import PDE.Parabolic.Heat.ConvolutionSpace.JointSmoothness

/-!
# Continuous second spatial derivatives of heat evolution

The joint smoothness theorem gives more regularity than the classical heat equation needs.
Restricting to a fixed positive time gives the `C²` spatial statement used by the equation
and the Cole–Hopf transform. Explicit formulas for these derivatives are in
`SpatialDerivatives`.
-/

@[expose] public section

namespace HeatEquation

variable {n : ℕ}

/-- Heat evolution of bounded continuous data has `C²` spatial slices at every positive time.
This is a restriction of its joint smoothness in time and space. -/
theorem contDiff_initialValueSolution_space
    (g : ℝ^n → ℝ) (t : ℝ) (ht : 0 < t)
    (hg : Continuous g) (hgb : ∃ M, ∀ y, |g y| ≤ M) :
    ContDiff ℝ 2 (fun x ↦ initialValueSolution (n := n) g x t) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hslice := (contDiffAt_initialValueSolution_timeSpace g x t ht hg hgb).comp x
    (contDiffAt_const.prodMk contDiffAt_id)
  exact hslice.of_le (by simp)

end HeatEquation
