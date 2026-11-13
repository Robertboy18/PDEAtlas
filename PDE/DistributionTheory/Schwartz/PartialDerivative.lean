/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import PDE.FDeriv.PartialDeriv

/-!
# Coordinate derivatives of Schwartz functions

Coordinate differentiation preserves Schwartz space through Mathlib's bundled
directional derivative. Coercing the result to a function agrees with LeanPDE's
classical coordinate derivative, so the same notation supports both operations.
-/

@[expose] public noncomputable section

open PDE

namespace SchwartzMap

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Coordinate differentiation in Schwartz space, using Mathlib's directional derivative. -/
instance instPartialDerivative :
    PDE.PartialDerivative n 𝓢(ℝ^n, F) 𝓢(ℝ^n, F) where
  partialDeriv i := LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ))

/-- The bundled Schwartz derivative is the classical derivative after coercion to functions. -/
@[simp] theorem coe_partialDeriv (i : Fin n) (φ : 𝓢(ℝ^n, F)) :
    ⇑(∂[i] φ) = ∂[i] (φ : ℝ^n → F) := by
  funext x
  exact lineDerivOp_apply_eq_fderiv (EuclideanSpace.single i 1) φ x

/-- A finite word of bundled coordinate derivatives agrees with the ordinary
iterated derivative of the underlying Schwartz function. -/
theorem coe_iteratedLineDerivOp (α : List (Fin n)) (φ : 𝓢(ℝ^n, F)) :
    ⇑(LineDeriv.iteratedLineDerivOp
      (fun j : Fin α.length ↦ EuclideanSpace.single (α.get j) (1 : ℝ)) φ) =
        iteratedPartialDeriv α (φ : ℝ^n → F) := by
  induction α with
  | nil => rfl
  | cons i α ih =>
    change ⇑(∂[i] (LineDeriv.iteratedLineDerivOp
      (fun j : Fin α.length ↦ EuclideanSpace.single (α.get j) (1 : ℝ)) φ)) =
        ∂[i] (iteratedPartialDeriv α (φ : ℝ^n → F))
    rw [coe_partialDeriv, ih]

public meta section

open Lean PrettyPrinter.Delaborator SubExpr

/-- Display coordinate differentiation in Schwartz space without losing the real
scalar type of its direction. Other directional derivatives keep their names. -/
@[delab app.LineDeriv.lineDerivOp]
def delabPartialDeriv : Delab := whenPPOption getPPNotation do
  guard <| !(← getPPOption getPPExplicit)
  let e ← getExpr
  guard <| e.getAppNumArgs == 6
  guard <| (e.getArg! 3).isAppOf ``instLineDeriv
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
  let φ ← withAppArg delab
  `(∂[$i] $φ)

end

end SchwartzMap
