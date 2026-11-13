/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import PDE.Symbolic.Continuum.IntervalEval.MixedValidity

/-!
# Domain checks for mixed partial derivatives on a box

A nonlinear two-coordinate expression uses a third coordinate as an exact
translation parameter. A certified rational box supplies the domain conditions
for its mixed physical
derivative. The resulting theorem identifies that derivative with the evaluated
symbolic expression throughout the box.
-/

@[expose] public section

namespace PDE.Examples.MixedDomainReplay

open CAS.Verified CAS.Continuum

/-- A small exact box containing nonzero physical and translation coordinates. -/
def coordinateRange : RationalInterval :=
  .ofBounds 0 (1 / 4) (by norm_num)

attribute [inherit_doc coordinateRange] coordinateRange.eq_1

/-- All three coordinates range independently over the same rational interval. -/
def domain : Set (ℝ^3) :=
  {x | ∀ i, coordinateRange.MemReal (x i)}

attribute [inherit_doc domain] domain.eq_1

/-- The registry receives only the exact coordinate box and its membership proof. -/
def registry : RationalInterval.CertifiedEvalRegistry domain (fun x i ↦ x i) :=
  .ofEnvironment (fun _ ↦ coordinateRange) (fun _x hx i ↦ hx i)

attribute [inherit_doc registry] registry.eq_1

/-- Inverse hyperbolic sine, written with log and sqrt as `log (x + sqrt (1 + x ^ 2))`. -/
def inverseHyperbolic (expr : Expr (Fin 3)) : Expr (Fin 3) :=
  .log (.add expr (.sqrt (.add (.nat 1) (.pow expr 2))))

attribute [inherit_doc inverseHyperbolic] inverseHyperbolic.eq_1

/-- A product with two nonlinear physical coordinates and an exact axial parameter. -/
def translatedProduct : Expr (Fin 3) :=
  .mul (inverseHyperbolic (.var 0))
    (inverseHyperbolic (.add (.var 1) (.var 2)))

attribute [inherit_doc translatedProduct] translatedProduct.eq_1

/-- Both physical directions are differentiated; parameter coordinate two is absent. -/
theorem translatedProduct_valid :
    (registry.validMixedOn? translatedProduct [0, 1]).isSome = true := by
  decide +kernel

/-- The accepted domain check justifies the actual mixed derivative throughout
the box, using the same nonlinear expression and fixed derivative inventory. -/
theorem iteratedPartialDeriv_translatedProduct (x : ℝ^3) (hx : x ∈ domain) :
    iteratedPartialDeriv [0, 1]
      (fun y : ℝ^3 ↦ Real.arsinh (y 0) * Real.arsinh (y 1 + y 2)) x =
        (translatedProduct.mixedDiff [0, 1]).eval x := by
  have hvalid : translatedProduct.ValidMixedAt [0, 1] x := by
    cases hroute : registry.validMixedOn? translatedProduct [0, 1] with
    | none =>
        have h := translatedProduct_valid
        simp only [hroute, Option.isSome_none, Bool.false_eq_true] at h
    | some route => exact route.cert x hx
  simpa [translatedProduct, inverseHyperbolic, Expr.eval, Real.arsinh] using
    Expr.iteratedPartialDeriv_eval translatedProduct [0, 1] x hvalid

end PDE.Examples.MixedDomainReplay
