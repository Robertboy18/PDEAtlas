/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Real

/-!
# Notation for real whole-space Hilbert Sobolev spaces

With `open scoped Sobolev`, write `H^{s}(ℝ^n; ℝ)` for the real subspace
`HsSpaceReal n s`. This notation is available for every real order `s`.

Mathlib's `BesselPotentialSpace` scope retains `H^{s}(ℝ^n)` for the complex space.
The semicolon makes the real subspace explicit, following the shared Sobolev
notation for scalar fields.
-/

@[expose] public section

/-- The real Hilbert Sobolev space on Euclidean space, with explicit scalar field. -/
scoped[Sobolev] notation "H^{" s "}(" "ℝ^" n "; " "ℝ" ")" =>
  SobolevSpace.Fractional.HsSpaceReal n s
