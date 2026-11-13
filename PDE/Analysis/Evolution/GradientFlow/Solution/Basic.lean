/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Subdifferential.Basic
public import PDE.Analysis.Evolution.Time.WeakDerivative.Basic

/-!
# The weak class for subdifferential gradient flows

For `I : H → EReal` on a real inner product space, `IsSubgradientFlow I u g` says
that `u` is a weak solution of `u' ∈ -∂I(u)` on `t > 0` with velocity `g`: `u` is
continuous on `[0, ∞)`, `g ∈ L^∞((0, ∞); H)` is the weak time derivative of `u` on
`(0, ∞)`, and `-g(t) ∈ ∂I(u(t))` for almost every `t > 0`, where
`v ∈ ∂I(x)` means `I x + ⟪v, w - x⟫ ≤ I w` for all `w`. The initial value is not
part of the structure. Requiring `g` to be a weak derivative excludes singular
continuous paths, whose pointwise derivative vanishes almost everywhere.
-/

@[expose] public section

open MeasureTheory Set PDE.Analysis.Convex
open scoped ENNReal

namespace PDE.Analysis.Evolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The continuous weak class in which the Hilbert subdifferential flow is unique.
The initial value is specified separately, so contraction can compare different data. -/
structure IsSubgradientFlow (I : H → EReal) (u g : ℝ → H) : Prop where
  /-- Continuity includes the value at zero. -/
  continuousOn : ContinuousOn u (Ici 0)
  /-- The velocity has one uniform essential bound on the entire half-line. -/
  velocity_memLp : MemLp g ∞ (volume.restrict (Ioi 0))
  /-- Velocity means distributional differentiation, with local Bochner integrability. -/
  weakDerivative : HasWeakTimeDerivativeOn (Ioi 0) u g
  /-- The negative velocity is a subgradient almost everywhere. -/
  inclusion : ∀ᵐ t ∂volume.restrict (Ioi 0), -g t ∈ subdifferential I (u t)

end PDE.Analysis.Evolution
