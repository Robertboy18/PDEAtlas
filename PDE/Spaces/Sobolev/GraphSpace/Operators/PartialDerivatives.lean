/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Slicing.HigherOrder

/-!
# Weak partial derivatives in Sobolev notation

The expression `∂[i] u` is the weak partial
derivative of `u`, viewed in the Sobolev space of one lower order. It uses
the derivative-word operator, so no representative is chosen anew.
-/

@[expose] public noncomputable section

open PDE (partialDeriv)

open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set ℝ^n}

/-- The weak partial derivative as a map lowering the Sobolev order by one. -/
def partialDerivCLM (i : Fin n) : W^{k + 1,p}(Ω) →L[ℝ] W^{k,p}(Ω) :=
  derivativeWordCLM [i] (by simp [Nat.add_comm])

/-- Weak partial derivatives for the shared `∂[i] u` notation. -/
instance instPartialDerivative :
    PDE.PartialDerivative n (W^{k + 1,p}(Ω)) (W^{k,p}(Ω)) where
  partialDeriv i u := partialDerivCLM i u

/-- Weak partial derivatives of zero-boundary graphs take values in the ambient graph. -/
instance instPartialDerivativeWkp0SpaceOn :
    PDE.PartialDerivative n (W₀^{k + 1,p}(Ω)) (W^{k,p}(Ω)) where
  partialDeriv i u := partialDerivCLM i (u : W^{k + 1,p}(Ω))

/-- The dispatch projection applies the bounded weak partial-derivative operator. -/
@[simp] theorem partialDerivative_eq (i : Fin n) (u : W^{k + 1,p}(Ω)) :
    PDE.PartialDerivative.partialDeriv i u = partialDerivCLM i u :=
  rfl

/-- A weak partial derivative has norm bounded by the original Sobolev norm. -/
theorem norm_partialDeriv_le (i : Fin n) (u : W^{k + 1,p}(Ω)) :
    ‖∂[i] u‖ ≤ ‖u‖ :=
  norm_derivativeWordCLM_apply_le [i] _ u

public meta section

open Lean PrettyPrinter.Delaborator SubExpr

/-- Display an applied weak derivative, leaving the unapplied bounded map visible. -/
@[delab app.DFunLike.coe]
def delabPartialDeriv : Delab := whenPPOption getPPNotation do
  guard <| !(← getPPOption getPPExplicit)
  let e ← getExpr
  guard <| e.getAppNumArgs == 6
  guard <| (e.getArg! 4).isAppOf ``partialDerivCLM
  let i ← withNaryArg 4 <| withAppArg delab
  let u ← withAppArg delab
  `(∂[$i] $u)

end

end SobolevSpace.GraphSpace
