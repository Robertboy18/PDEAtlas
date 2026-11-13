/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Poisson.Equation
public import CAS.ClosedForm.Scalar.Models
public import CAS.ExactTactic
public import PDE.Symbolic.ClosedForm.Differential.Equation

/-!
# A quadratic solution of Poisson's equation

The potential `u(x, y) = x² + y²` satisfies `Δu = 4`. LeanPDE writes Poisson's equation as
`-Δu = f`, so `u` solves the symbolic Poisson equation with constant source `f = -4`. We
check the identity at each level of the symbolic pipeline: the compiled residual for
`-Δu = -4` vanishes (closed by `cas`), the analytic residual vanishes, the Euclidean `laplacian`
of the evaluated expression is the constant `4`, and the `poissonEquation 2` with source
`-4` is satisfied everywhere.

## Main results

* `quadraticPoisson2D_satisfies_poisson`: the symbolic residual of `-Δu = -4` is identically
  zero.
* `laplacian_quadraticPoisson2D_eq_four`: the Euclidean Laplacian of `x² + y²` is `4`.
* `quadraticPoisson2D_satisfiesPDEProblem`: the Poisson equation with source `-4`
  holds on `ℝ^2`.
-/

@[expose] public section

open PDE (laplacian)

namespace LaplacianEquation.Symbolic

open CAS
open CAS.Certificate
open CAS.Euclid2
open scoped CAS

noncomputable section

/-- The quadratic potential `u(x, y) = x² + y²`. -/
def quadraticPoisson2D : Verified.Expr (Fin 2) :=
  x ^ 2 + y ^ 2

/-- The constant source in the equation `-Δu = -4`. -/
def quadraticPoisson2DRhs : Verified.Expr (Fin 2) :=
  -4

/-- The symbolic Poisson equation `-Δu = -4` in two dimensions. -/
def poissonQuadratic2DEquation : DiffExpr.Equation 2 Scalar.Unknown :=
  Scalar.poisson quadraticPoisson2DRhs

/-- The symbolic Poisson residual of `u(x, y) = x² + y²`. -/
def quadraticPoisson2DResidual : Verified.Expr (Fin 2) :=
  Scalar.residual poissonQuadratic2DEquation quadraticPoisson2D

/-- The symbolic Poisson residual vanishes identically. -/
theorem quadraticPoisson2D_residual_bound :
    ResidualBound (Exact.exprFn quadraticPoisson2DResidual) Set.univ 0 := by
  cas

/-- The polynomial `x² + y²` has zero residual for `-Δu = -4`. -/
theorem quadraticPoisson2D_satisfies_poisson :
    Set.EqOn (Exact.exprFn quadraticPoisson2DResidual) Exact.zeroFn Set.univ := by
  cas

private theorem quadraticPoisson2D_analytic_side_condition
    (p : ℝ^2) (_hp : p ∈ Set.univ) :
    DiffExpr.AnalyticSideCondition
      (Scalar.ansatz quadraticPoisson2D) p poissonQuadratic2DEquation.residual := by
  simp [DiffExpr.AnalyticSideCondition, DiffExpr.lower, DiffExpr.Lap,
    poissonQuadratic2DEquation, Scalar.poisson, DiffExpr.Equation.residual,
    Scalar.u, Scalar.ansatz, quadraticPoisson2D,
    quadraticPoisson2DRhs, Verified.Expr.ValidAt, Verified.Expr.SymVar.expr,
    Verified.Expr.diff]

/-- The analytic residual associated with the symbolic Poisson equation is zero. -/
theorem quadraticPoisson2D_analytic_residual_zero :
    ∀ p, p ∈ Set.univ →
      DiffExpr.Equation.analyticResidual
        (Scalar.ansatz quadraticPoisson2D) p poissonQuadratic2DEquation = 0 := by
  intro p hp
  exact DiffExpr.Equation.analyticResidual_eq_zero_of_closedResidualVanishesAt
    (by
      change quadraticPoisson2DResidual.eval p = 0
      exact quadraticPoisson2D_satisfies_poisson hp)
    (quadraticPoisson2D_analytic_side_condition p hp)

/-- The Euclidean Laplacian of `x² + y²` is the constant `4`. -/
theorem laplacian_quadraticPoisson2D_eq_four (p : ℝ^2) :
    laplacian (fun q : ℝ^2 ↦ quadraticPoisson2D.eval q) p = 4 := by
  have hvalid : quadraticPoisson2D.ValidAt p := by
    symbolic_assumptions
  have hdiff : ∀ i : Fin 2, (quadraticPoisson2D.diff i).ValidAt p := by
    symbolic_assumptions
  rw [← Verified.Expr.closedLaplacian_eval_eq_laplacian
    (expr := quadraticPoisson2D) (x := p) hvalid hdiff]
  have hres : -(Verified.Expr.closedLaplacian quadraticPoisson2D).eval p -
      quadraticPoisson2DRhs.eval p = 0 := by
    simpa [quadraticPoisson2DResidual, poissonQuadratic2DEquation,
      Scalar.poissonResidual, Scalar.residual, Scalar.poisson, DiffExpr.Lap,
      Scalar.u, DiffExpr.Equation.closedResidual,
      DiffExpr.Equation.residual, DiffExpr.lower, Exact.exprFn, Exact.zeroFn] using
      quadraticPoisson2D_satisfies_poisson trivial
  have hrhs : quadraticPoisson2DRhs.eval p = -4 := by
    norm_num [quadraticPoisson2DRhs, Verified.Expr.eval]
  linarith

/-- The quadratic potential satisfies the Poisson residual with source `-4`. -/
theorem quadraticPoisson2D_satisfiesPDEProblem :
    ∀ p ∈ (PoissonEquation.poissonEquation 2 (fun _ : ℝ^2 ↦ (-4 : ℝ))).domain,
      (PoissonEquation.poissonEquation 2 (fun _ : ℝ^2 ↦ (-4 : ℝ))).residual
        (fun q : ℝ^2 ↦ quadraticPoisson2D.eval q) p = 0 := by
  intro p _hp
  have hlap := laplacian_quadraticPoisson2D_eq_four p
  rw [PoissonEquation.poissonEquation_residual]
  linarith

end

end LaplacianEquation.Symbolic
