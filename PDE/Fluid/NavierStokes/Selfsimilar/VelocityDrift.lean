/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv

/-!
# The self-similar drift

The stationary self-similar equation contains the drift `U + x · ∇U` of the velocity. It is the
generator of the dilations `a ↦ a U(a ·)`.
-/

@[expose] public noncomputable section

namespace NavierStokes.SpectralProfile

/-- The velocity plus its Euler derivative, in Cartesian variables. -/
def velocityDrift (U : ℝ^3 → ℝ^3) (x : ℝ^3) : ℝ^3 := U x + fderiv ℝ U x x

end NavierStokes.SpectralProfile
