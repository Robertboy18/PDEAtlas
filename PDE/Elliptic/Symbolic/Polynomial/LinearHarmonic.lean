/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Laplace.Equation
public import CAS.ClosedForm.Scalar.Models
public import CAS.ExactTactic
public import PDE.Symbolic.ClosedForm.Differential.Equation

/-!
# A linear harmonic polynomial

The coordinate function `u(x, y) = x` is harmonic on the plane. We check that fact at
each level of the symbolic pipeline: the compiled Laplace residual of the `Verified.Expr` `x`
vanishes (closed by `cas`), the analytic residual of the symbolic Laplace equation vanishes, the
Euclidean `laplacian` of the evaluated expression is zero, and the `laplaceEquation 2`
residual is satisfied everywhere.

It is the simplest instance of the pattern shared by the other polynomial and radial examples:
a symbolic identity together with validity side conditions yields an analytic PDE statement.

## Main results

* `linearHarmonic2D_harmonic`: the symbolic Laplace residual of `x` is identically zero.
* `laplacian_linearHarmonic2D_zero`: the Euclidean Laplacian of `p ↦ p 0` vanishes.
* `linearHarmonic2D_satisfiesPDEProblem`: the Laplace equation on `ℝ^2` holds.
-/

@[expose] public section

open PDE (laplacian laplaceEquation)

namespace LaplacianEquation.Symbolic

open CAS
open CAS.Certificate
open CAS.Euclid2
open scoped CAS

noncomputable section

/-- The coordinate function `u(x, y) = x`. -/
def linearHarmonic2D : Verified.Expr (Fin 2) :=
  x

/-- The symbolic Laplace residual of `u(x, y) = x`. -/
def linearHarmonic2DResidual : Verified.Expr (Fin 2) :=
  Scalar.residual (Scalar.laplace (n := 2)) linearHarmonic2D

/-- The symbolic residual of the coordinate function vanishes identically. -/
theorem linearHarmonic2D_residual_bound :
    ResidualBound (Exact.exprFn linearHarmonic2DResidual) Set.univ 0 := by
  cas

/-- The coordinate function `x` has zero symbolic Laplace residual. -/
theorem linearHarmonic2D_harmonic :
    Set.EqOn (Exact.exprFn linearHarmonic2DResidual) Exact.zeroFn Set.univ := by
  cas

private theorem linearHarmonic2D_analytic_side_condition
    (p : ℝ^2) (_hp : p ∈ Set.univ) :
    DiffExpr.AnalyticSideCondition
      (Scalar.ansatz linearHarmonic2D) p (Scalar.laplace (n := 2)).residual := by
  simp [DiffExpr.AnalyticSideCondition, DiffExpr.lower, DiffExpr.Lap,
    Scalar.laplace, DiffExpr.Equation.residual, Scalar.u,
    Scalar.ansatz, linearHarmonic2D, Verified.Expr.ValidAt, Verified.Expr.SymVar.expr,
    Verified.Expr.diff]

/-- The analytic residual associated with the symbolic Laplace equation is zero. -/
theorem linearHarmonic2D_analytic_residual_zero :
    ∀ p, p ∈ Set.univ →
      DiffExpr.Equation.analyticResidual
        (Scalar.ansatz linearHarmonic2D) p (Scalar.laplace (n := 2)) = 0 := by
  intro p hp
  exact DiffExpr.Equation.analyticResidual_eq_zero_of_closedResidualVanishesAt
    (by
      change linearHarmonic2DResidual.eval p = 0
      exact linearHarmonic2D_harmonic hp)
    (linearHarmonic2D_analytic_side_condition p hp)

/-- The Euclidean Laplacian of the coordinate function is zero. -/
theorem laplacian_linearHarmonic2D_zero (p : ℝ^2) :
    laplacian (fun q : ℝ^2 ↦ linearHarmonic2D.eval q) p = 0 := by
  have hvalid : linearHarmonic2D.ValidAt p := by
    symbolic_assumptions
  have hdiff : ∀ i : Fin 2, (linearHarmonic2D.diff i).ValidAt p := by
    symbolic_assumptions
  rw [← Verified.Expr.closedLaplacian_eval_eq_laplacian
    (expr := linearHarmonic2D) (x := p) hvalid hdiff]
  simpa [linearHarmonic2DResidual, Scalar.laplaceResidual, Scalar.residual,
    Scalar.laplace, DiffExpr.Lap, Scalar.u,
    DiffExpr.Equation.closedResidual, DiffExpr.Equation.residual, DiffExpr.lower,
    Exact.exprFn, Exact.zeroFn] using linearHarmonic2D_harmonic trivial

/-- The coordinate function satisfies the Laplace residual on `ℝ^2`. -/
theorem linearHarmonic2D_satisfiesPDEProblem :
    ∀ p ∈ (laplaceEquation 2).domain,
      (laplaceEquation 2).residual
        (fun q : ℝ^2 ↦ linearHarmonic2D.eval q) p = 0 := by
  intro p _hp
  simpa [PDE.LinearPDE.residual, laplaceEquation, laplacian] using
    laplacian_linearHarmonic2D_zero p

end

end LaplacianEquation.Symbolic
