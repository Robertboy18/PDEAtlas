/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.StreamFunction

/-!
# Addition of planar stream velocities

Differentiability at the evaluation point suffices to add the two rotated
gradients. Global smoothness of either stream is unnecessary.

## Main results

* `planarStreamVelocity_add`: the velocity of a sum of streams is the sum of the velocities at
  every point where both streams are differentiable.
-/

@[expose] public noncomputable section

namespace IncompressibleFlow

/-- The velocity of a sum of streams is the sum of velocities wherever both are differentiable. -/
theorem planarStreamVelocity_add {ψ χ : ℝ^2 → ℝ} {x : ℝ^2}
    (hψ : DifferentiableAt ℝ ψ x) (hχ : DifferentiableAt ℝ χ x) :
    planarStreamVelocity (fun y ↦ ψ y + χ y) x =
      planarStreamVelocity ψ x + planarStreamVelocity χ x := by
  ext i
  fin_cases i <;> simp [planarStreamVelocity, PDE.partialDeriv_add hψ hχ, add_comm]

end IncompressibleFlow
