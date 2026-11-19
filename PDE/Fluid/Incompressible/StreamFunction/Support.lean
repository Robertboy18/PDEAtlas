/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.StreamFunction
import PDE.FDeriv.PartialDeriv.Support

/-!
# Support and constant amplitudes of planar stream velocities

Coordinate differentiation preserves compact support and commutes with
constant amplitudes, including for the total derivative on arbitrary functions.

## Main results

* `hasCompactSupport_planarStreamVelocity`: a compactly supported stream has a compactly supported
  velocity.
* `planarStreamVelocity_const_mul`: multiplying the stream by a constant multiplies its velocity by
  the same constant.
-/

@[expose] public noncomputable section

namespace IncompressibleFlow

/-- A compactly supported stream generates a compactly supported velocity. -/
theorem hasCompactSupport_planarStreamVelocity {ψ : ℝ^2 → ℝ}
    (hψ : HasCompactSupport ψ) :
    HasCompactSupport (planarStreamVelocity ψ) := by
  apply HasCompactSupport.intro hψ.isCompact
  intro x hx
  ext i
  fin_cases i <;>
    simp [planarStreamVelocity, PDE.partialDeriv_eq_zero_of_notMem_tsupport _ hx]

/-- A constant stream amplitude multiplies the reconstructed velocity by that amplitude. -/
theorem planarStreamVelocity_const_mul (ψ : ℝ^2 → ℝ) (a : ℝ) (x : ℝ^2) :
    planarStreamVelocity (fun y ↦ a * ψ y) x = a • planarStreamVelocity ψ x := by
  have hp (i : Fin 2) :
      (∂[i] (fun y ↦ a * ψ y)) x = a * (∂[i] ψ) x :=
    PDE.partialDeriv_const_smul a
  ext i
  fin_cases i <;> simp [planarStreamVelocity, hp, smul_eq_mul]

end IncompressibleFlow
