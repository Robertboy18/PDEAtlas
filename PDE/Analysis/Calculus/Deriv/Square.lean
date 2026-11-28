/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# The derivative of the square

`PDE.Analysis.hasDerivAt_sq` states that `s ↦ s ^ 2` has derivative `2 * x` at every real `x`.
Mathlib's `hasDerivAt_pow 2 x` gives the derivative as `↑2 * x ^ (2 - 1)`; proofs that differentiate
`r ^ 2 * f r` or `f (r ^ 2)` want the form `2 * x`, and one call of `simp` gets it.

The lemma was a private lemma of `PDE.Analysis.SpecialFunctions.SphericalBessel.WeakSolution` before
the modules listed in `NOTICE` came to the library. One of them, `PDE.Analysis.Calculus.Deriv`, had
a copy with the same statement under the same name; the copy is removed, and both modules use this
lemma. It is public in a module of its own because a module under the license of the library does
not import a module of `NOTICE`.

The import of `Mathlib.Topology.Algebra.Module.ModuleTopology` is there for the statement: with it,
instance search finds the same instance of `ContinuousSMul ℝ ℝ` as in `PDE.Analysis.Calculus.Deriv`,
where the removed copy stood, so `PDE.Analysis.hasDerivAt_sq` is the same term for the projects that
use it.
-/

@[expose] public section

namespace PDE.Analysis

/-- The derivative of `s ↦ s²`: the function `s ↦ s ^ 2` on `ℝ` has derivative `2 * x` at every
real `x`. -/
theorem hasDerivAt_sq (x : ℝ) : HasDerivAt (fun s : ℝ ↦ s ^ 2) (2 * x) x := by
  simpa using hasDerivAt_pow 2 x

end PDE.Analysis
