/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.Distribution
public import PDE.Common.Euclidean
public import PDE.Notation.PartialDerivative

/-!
# Differential notation for ordinary distributions

For unrestricted-order distributions, `Δ T` is Mathlib's canonical distributional
Laplacian. On Euclidean domains, `∂[i] T` differentiates in the coordinate direction
`EuclideanSpace.single i 1`. Both operators return distributions on the same open domain.
Finite-order distributions continue to use operators with explicit output orders.

## Implementation notes

Declarations about Mathlib's `Distribution` type live in its singular namespace
`Distribution`. The plural `Distributions` is only Mathlib's notation scope, opened by
`open scoped Distributions` for `𝓓(Ω, F)` and `𝓓'(Ω, F)`.
-/

@[expose] public section

open TopologicalSpace
open scoped Distributions

namespace Distribution

/-- The canonical Laplacian on ordinary distributions. -/
noncomputable instance instLaplacian
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    {Ω : Opens E} :
    Laplacian 𝓓'(Ω, F) 𝓓'(Ω, F) where
  laplacian := LineDeriv.laplacianCLM ℝ E 𝓓'(Ω, F)

/-- Coordinate derivatives of ordinary distributions on Euclidean domains. -/
noncomputable instance instPartialDerivative
    {n : ℕ} {Ω : Opens (ℝ^n)}
    {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] :
    PDE.PartialDerivative n 𝓓'(Ω, F) 𝓓'(Ω, F) where
  partialDeriv i := LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ))

public meta section

open Lean PrettyPrinter.Delaborator SubExpr

/-- Display an applied coordinate derivative of an unrestricted-order ordinary distribution.
Unapplied operators, other directions, and other distribution carriers keep their names. -/
@[delab app.LineDeriv.lineDerivOp]
def delabPartialDeriv : Delab := whenPPOption getPPNotation do
  guard <| !(← getPPOption getPPExplicit)
  let e ← getExpr
  guard <| e.getAppNumArgs == 6
  guard <| (e.getArg! 3).isAppOf ``instLineDerivTopENat
  let direction := e.getArg! 4
  guard <| direction.isAppOf ``EuclideanSpace.single && direction.getAppNumArgs == 6
  guard <| (direction.getArg! 0).isAppOf ``Fin
  guard <| (direction.getArg! 1).isConstOf ``Real
  let one := direction.getArg! 5
  guard <| one.isAppOf ``OfNat.ofNat && one.getAppNumArgs == 3
  guard <| (one.getArg! 1).rawNatLit? == some 1
  let ofNat := one.getArg! 2
  guard <| ofNat.isAppOf ``One.toOfNat1 && ofNat.getAppNumArgs == 2
  guard <| (ofNat.getArg! 1).isConstOf ``Real.instOne
  let i ← withNaryArg 4 <| withNaryArg 4 delab
  let T ← withAppArg delab
  `(∂[$i] $T)

end

end Distribution
