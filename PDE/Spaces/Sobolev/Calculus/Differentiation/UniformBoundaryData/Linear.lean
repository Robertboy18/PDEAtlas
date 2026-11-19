/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Gradient

/-!
# Linearity of the completed gradient

The continuous closure gradient respects the arithmetic of classical
closure data. Equality in the open domain determines the boundary values.
-/

@[expose] public section

open scoped Gradient

namespace SobolevSpace.ContDiffUpToBoundary

open Set

/-- The completed gradient commutes with subtraction on the whole closure. -/
theorem completedGradient_sub {n : ℕ} {Ω : Set (ℝ^n)} {f g : ℝ^n → ℝ}
    (hf : ContDiffUpToBoundary 1 f Ω) (hg : ContDiffUpToBoundary 1 g Ω)
    (hopen : IsOpen Ω) :
    EqOn (hf.sub hg hopen).completedGradient
      (fun x ↦ hf.completedGradient x - hg.completedGradient x) (closure Ω) := by
  apply (hf.sub hg hopen).completedGradient_eqOn
    (hf.continuous_completedGradient.sub hg.continuous_completedGradient).continuousOn
  intro x hx
  change hf.completedGradient x - hg.completedGradient x =
    ∇ (fun y ↦ f y - g y) x
  rw [hf.completedGradient_eq_gradient hx, hg.completedGradient_eq_gradient hx]
  have hdf := (hf.contDiffOn.contDiffAt (hopen.mem_nhds hx)).differentiableAt one_ne_zero
  have hdg := (hg.contDiffOn.contDiffAt (hopen.mem_nhds hx)).differentiableAt one_ne_zero
  simp only [gradient, fderiv_fun_sub hdf hdg, map_sub]

end SobolevSpace.ContDiffUpToBoundary
