/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.Incompressible.StreamFunction

/-!
# The norm of the velocity of a planar stream function

`IncompressibleFlow.norm_planarStreamVelocity_eq` states
`‖planarStreamVelocity ψ x‖ = ‖fderiv ℝ ψ x‖` for every `ψ : ℝ² → ℝ` and every point `x`; no
regularity of `ψ` is assumed. The velocity `(-∂₁ψ, ∂₀ψ)` is the gradient turned by a right angle, so
it has the norm of the gradient (`IncompressibleFlow.norm_planarStreamVelocity`), and the gradient
has the norm of the derivative.

This is the form that turns a bound of `fderiv ℝ ψ` into a bound of the velocity. BlowupZoo uses it
in the velocity estimates near the wall of the cylinder, in the local theory of its boundary blowup.
-/

@[expose] public section

noncomputable section

namespace IncompressibleFlow

set_option linter.missingDocs true

/-- The velocity of a planar stream function has the norm of its derivative:
`‖planarStreamVelocity ψ x‖ = ‖fderiv ℝ ψ x‖` for every `ψ : ℝ^2 → ℝ` and every point `x`. No
regularity of `ψ` is assumed. It turns a bound of the derivative of a stream function into a
bound of its velocity. Proof: `norm_planarStreamVelocity` gives the norm of the gradient, which
is the norm of the derivative. -/
theorem norm_planarStreamVelocity_eq (ψ : ℝ^2 → ℝ) (x : ℝ^2) :
    ‖planarStreamVelocity ψ x‖ = ‖fderiv ℝ ψ x‖ := by
  rw [norm_planarStreamVelocity]
  simp [gradient]

end IncompressibleFlow
