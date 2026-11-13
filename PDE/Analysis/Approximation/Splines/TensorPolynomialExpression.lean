/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.TensorHornerAffine
public import CAS.Expr.Substitution

/-!
# Affine tensor expressions in the polynomial fragment

Rational reciprocal scales are constants, so sparse polynomial reflection
can collect the substituted expression without encountering division nodes.

## Main definitions

* `tensorAffinePolynomialExpr`: the inverse affine substitution into a tensor polynomial, written
  with multiplication by the rational reciprocal scales.

## Main results

* `tensorAffinePolynomialExpr_eval`: the expression denotes the inverse-affine tensor value at
  every point.
-/

@[expose] public section

namespace CAS.Splines

open CAS.Verified

/-- Inverse affine substitution using rational multiplication for polynomial reflection. -/
def tensorAffinePolynomialExpr (coefficients : List (List ℚ))
    (originX scaleX originY scaleY : ℚ) : Expr (Fin 2) :=
  (tensorHornerExpr coefficients).mapVars fun i ↦
    if i = 0 then
      .mul (Expr.mkRatConst scaleX⁻¹) (.sub (.var 0) (Expr.mkRatConst originX))
    else
      .mul (Expr.mkRatConst scaleY⁻¹) (.sub (.var 1) (Expr.mkRatConst originY))

/-- Polynomial substitution denotes the original inverse-affine tensor value at every point. -/
theorem tensorAffinePolynomialExpr_eval (coefficients : List (List ℚ))
    (originX scaleX originY scaleY : ℚ) (ρ : Fin 2 → ℝ) :
    (tensorAffinePolynomialExpr coefficients originX scaleX originY scaleY).eval ρ =
      tensorHornerValue coefficients
        ((ρ 0 - (originX : ℝ)) / (scaleX : ℝ))
        ((ρ 1 - (originY : ℝ)) / (scaleY : ℝ)) := by
  simp [tensorAffinePolynomialExpr, Expr.eval_mapVars, tensorHornerExpr_eval,
    Expr.eval, div_eq_mul_inv, mul_comm]

end CAS.Splines
