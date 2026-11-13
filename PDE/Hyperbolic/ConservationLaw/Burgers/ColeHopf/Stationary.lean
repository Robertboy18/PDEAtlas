/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Burgers.ColeHopf.Symbolic
public import CAS.Exact.ExpressionSideConditions
import CAS.ExactTactic

/-!
# A stationary Burgers profile from the Cole–Hopf transform

We verify the stationary velocity `-2 + 4 / (1 + exp(2x))` directly against the
unit-viscosity Burgers equation. It equals the Cole–Hopf transform of the heat profile
`exp(t + x) + exp(t - x)` in `TwoExponential`, an explicit instance of Evans, §4.4.1(b). The
velocity and its residual are typed reflected expressions. The closed residual certificate is
checked directly by `cas`; the analytic residual theorem first discharges the nonvanishing
condition from positivity of the exponential denominator, then uses the analytic residual lemmas
to justify the symbolic derivatives.

We state both the closed-form certificate and the ordinary Euclidean residual; the latter does
not mention the symbolic normal form.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.4.1(b), equation (5).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace BurgersEquation.ColeHopf

open CAS
open CAS.Euclid2

noncomputable section

/--
The same nonconstant velocity in a stationary normalized exponential form.

This is algebraically equivalent to the two-exponential Cole–Hopf velocity and
has the simpler Burgers residual
`u(x) = -2 + 4/(1+exp(2x))`.
-/
def coleHopfStationaryVelocity : Verified.Expr (Fin 2) :=
  -2 + 4 / (Verified.Expr.exp (2 * y : Verified.Expr (Fin 2)) + 1)

/-- The closed symbolic Burgers residual for the stationary Cole–Hopf velocity. -/
def coleHopfStationaryBurgersResidual : Verified.Expr (Fin 2) :=
  Scalar.residual coleHopfUnitBurgersEquation coleHopfStationaryVelocity

/-- The readable stationary Cole–Hopf denominator is positive everywhere. -/
theorem coleHopfStationary_denominator_pos (p : ℝ^2) :
    0 < (Verified.Expr.exp (2 * y : Verified.Expr (Fin 2)) + 1).eval p := by
  simpa [Verified.Expr.eval] using add_pos (Real.exp_pos (2 * p 1)) (zero_lt_one : (0 : ℝ) < 1)

/--
Pointwise analytic Burgers residual for the stationary Cole–Hopf velocity.

This is the calculus-facing proof: the symbolic derivatives are justified by
`symbolic_assumptions`, the denominator is explicitly nonzero, and the final algebra
is a field simplification plus normalization.
-/
private theorem coleHopfStationaryBurgers_analytic_residual_zero_of_den (p : ℝ^2)
    (hden : (Verified.Expr.exp (2 * y : Verified.Expr (Fin 2)) + 1).eval p ≠ 0) :
    DiffExpr.Equation.analyticResidual (Scalar.ansatz coleHopfStationaryVelocity) p
      coleHopfUnitBurgersEquation = 0 := by
  have huvalid : coleHopfStationaryVelocity.ValidAt p := by
    symbolic_assumptions
  have huyvalid : (coleHopfStationaryVelocity.diff (1 : Fin 2)).ValidAt p := by
    symbolic_assumptions
  have ht := Verified.Expr.partialDeriv_eval_eq
    (expr := coleHopfStationaryVelocity) (x := p) (i := (0 : Fin 2)) huvalid
  have hy := Verified.Expr.partialDeriv_eval_eq
    (expr := coleHopfStationaryVelocity) (x := p) (i := (1 : Fin 2)) huvalid
  have hyy := Verified.Expr.partialDeriv_eval_eq
    (expr := coleHopfStationaryVelocity.diff (1 : Fin 2)) (x := p) (i := (1 : Fin 2)) huyvalid
  simp only [DiffExpr.Equation.analyticResidual, DiffExpr.Equation.residual,
    coleHopfUnitBurgersEquation, DiffExpr.D,
    Euclid2.x, Euclid2.y, Scalar.u, DiffExpr.D2, DiffExpr.analyticEval,
    DiffExpr.analyticEval_sub, DiffExpr.lower, Scalar.ansatz,
    Verified.Expr.eval_trigSimplify, Verified.Expr.eval, CharP.cast_eq_zero, sub_zero]
  rw [ht, hy, hyy]
  simp [coleHopfStationaryVelocity,
    Verified.Expr.diff, Verified.Expr.eval, Verified.Expr.SymVar.expr] at *
  field_simp [hden]
  ring_nf

/-- The closed-form Burgers residual vanishes everywhere: `cas` reads the residual back from the
reflected expression and certifies it with one kernel evaluation. -/
theorem coleHopfStationaryBurgers_closed_residual_eq_zero :
    Set.EqOn (Exact.exprFn coleHopfStationaryBurgersResidual) Exact.zeroFn Set.univ := by
  cas

/--
Analytic residual theorem for the stationary Cole–Hopf velocity.

The exponential denominator is positive at every point, so the statement needs no domain
restriction.
-/
theorem coleHopfStationaryBurgers_analytic_residual_eq_zero (p : ℝ^2) :
    DiffExpr.Equation.analyticResidual (Scalar.ansatz coleHopfStationaryVelocity) p
      coleHopfUnitBurgersEquation = 0 := by
  have hden : (Verified.Expr.exp (2 * y : Verified.Expr (Fin 2)) + 1).eval p ≠ 0 :=
    ne_of_gt (coleHopfStationary_denominator_pos p)
  exact coleHopfStationaryBurgers_analytic_residual_zero_of_den p hden

end

end BurgersEquation.ColeHopf
