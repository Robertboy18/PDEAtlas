/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Symbolic.ClosedForm.Scalar.Core

/-!
# Symbolic data for the Cole–Hopf transformation

We give the reflected expressions used to verify explicit instances of the
Cole–Hopf transformation of Evans, §4.4.1(b). The analytic transformation is defined in
`BurgersEquation.ColeHopf`. The expression type `Verified.Expr` and the closed-form engine that
produces the certificates come from SymLean, our computer algebra system for Lean.

The type `Verified.Expr (Fin 2)` is the typed expression syntax for two real coordinates.
Throughout this directory, coordinate `0` (notation `x`) is time and coordinate `1` (notation
`y`) is space. The heat and Burgers equations are represented by `DiffExpr.Equation`; evaluating
their residuals connects the reflected syntax to ordinary real-valued functions.

## Main definitions

* `coleHopfUnitTransformExpr` is the unit-viscosity expression `-2 v_y / v`,
  built from the spatial derivative `v.diff 1`.
* the heat side is the one-dimensional heat equation `HeatEquation.Symbolic.Space1.heat1DEquation`.
* `coleHopfUnitBurgersEquation` is the unit-viscosity Burgers equation.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.4.1(b), equations (5)-(10).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace BurgersEquation.ColeHopf

open CAS
open CAS.Euclid2

/-- The unit-viscosity Cole–Hopf expression `-2 v_y / v`, where `v_y = v.diff 1`
is the spatial derivative. -/
def coleHopfUnitTransformExpr (v : Verified.Expr (Fin 2)) : Verified.Expr (Fin 2) :=
  -2 * v.diff 1 / v

/-- The unit-viscosity Burgers equation `u_t + u u_x - u_xx = 0`. -/
def coleHopfUnitBurgersEquation : DiffExpr.Equation 2 Scalar.Unknown where
  lhs :=
    DiffExpr.D x Scalar.u + Scalar.u * DiffExpr.D y Scalar.u - DiffExpr.D2 y Scalar.u
  rhs := 0

end BurgersEquation.ColeHopf
