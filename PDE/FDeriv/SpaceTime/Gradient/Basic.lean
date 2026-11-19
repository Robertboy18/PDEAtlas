/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import PDE.FDeriv.PartialDeriv
import PDE.FDeriv.Operators

/-!
# Coordinate helpers for space-time splits

Spacetime is `ℝ^(n + 1)`, with coordinate `0` for time and coordinates
`i.succ` for space. We define the spatial gradient of a scalar field through
the projection `PDE.Common.spatialPartCLM`.
-/

@[expose] public section

open scoped Gradient

namespace PDE

/-- Spatial gradient of a function (excluding time derivative). -/
noncomputable def spatialGradient {n : ℕ} (u : ℝ^(n + 1) → ℝ)
    (x : ℝ^(n + 1)) : ℝ^n :=
  PDE.Common.spatialPartCLM n (∇ u x)

/-- The `i`th spatial-gradient component is spacetime coordinate derivative
`i.succ`; the time coordinate `0` does not appear. -/
@[simp]
theorem spatialGradient_apply {n : ℕ} (u : ℝ^(n + 1) → ℝ)
    (x : ℝ^(n + 1)) (i : Fin n) :
    spatialGradient u x i = (∂[i.succ] u) x := by
  simp [spatialGradient, PDE.Common.spatialPartCLM_apply,
    gradient_apply_eq_partialDeriv]

end PDE
