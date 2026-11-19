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
# A quadratic harmonic polynomial in three dimensions

The polynomial `x² + y² - 2z²` is harmonic on `ℝ^3`: its second derivatives are `2`, `2`, and
`-4`, which sum to zero. It is a degree-two solid spherical harmonic. We check the fact
at each level of the symbolic pipeline: the compiled Laplace residual vanishes (closed by
`cas`), the analytic residual of the symbolic Laplace equation vanishes, the Euclidean
`laplacian` of the evaluated expression is zero, and the `laplaceEquation 3` residual
is satisfied everywhere.

## Main results

* `quadraticHarmonic3D_harmonic`: the symbolic Laplace residual is identically zero.
* `laplacian_quadraticHarmonic3D_zero`: the Euclidean Laplacian of the evaluated polynomial
  vanishes.
* `quadraticHarmonic3D_satisfiesPDEProblem`: the Laplace equation on `ℝ^3` holds.
-/

@[expose] public section

open PDE (laplacian laplaceEquation)

namespace LaplacianEquation.Symbolic

open CAS
open CAS.Certificate
open scoped CAS

noncomputable section

/-- The quadratic harmonic polynomial `x² + y² - 2z²` on `ℝ^3`. -/
def quadraticHarmonic3D : Verified.Expr (Fin 3) :=
  (CAS.Euclid3.x : Verified.Expr (Fin 3)) ^ 2 +
    (CAS.Euclid3.y : Verified.Expr (Fin 3)) ^ 2 -
      2 * (CAS.Euclid3.z : Verified.Expr (Fin 3)) ^ 2

/-- The symbolic Laplace residual of `x² + y² - 2z²`. -/
def quadraticHarmonic3DResidual : Verified.Expr (Fin 3) :=
  Scalar.residual (Scalar.laplace (n := 3)) quadraticHarmonic3D

/-- The symbolic Laplace residual vanishes identically. -/
theorem quadraticHarmonic3D_residual_bound :
    ResidualBound (Exact.exprFn quadraticHarmonic3DResidual) Set.univ 0 := by
  cas

/-- The polynomial `x² + y² - 2z²` has zero symbolic Laplace residual. -/
theorem quadraticHarmonic3D_harmonic :
    Set.EqOn (Exact.exprFn quadraticHarmonic3DResidual) Exact.zeroFn Set.univ := by
  cas

private theorem quadraticHarmonic3D_analytic_side_condition
    (p : ℝ^3) (_hp : p ∈ Set.univ) :
    DiffExpr.AnalyticSideCondition
      (Scalar.ansatz quadraticHarmonic3D) p (Scalar.laplace (n := 3)).residual := by
  have hvalid : quadraticHarmonic3D.ValidAt p := by
    symbolic_assumptions
  have hdiff : ∀ i : Fin 3, (quadraticHarmonic3D.diff i).ValidAt p := by
    symbolic_assumptions
  simp [DiffExpr.AnalyticSideCondition, DiffExpr.lower, DiffExpr.Lap,
    Scalar.laplace, DiffExpr.Equation.residual,
    Scalar.u, Scalar.ansatz, hvalid, hdiff]

/-- The analytic residual associated with the symbolic Laplace equation is zero. -/
theorem quadraticHarmonic3D_analytic_residual_zero :
    ∀ p, p ∈ Set.univ →
      DiffExpr.Equation.analyticResidual
        (Scalar.ansatz quadraticHarmonic3D) p (Scalar.laplace (n := 3)) = 0 := by
  intro p hp
  exact DiffExpr.Equation.analyticResidual_eq_zero_of_closedResidualVanishesAt
    (by
      change quadraticHarmonic3DResidual.eval p = 0
      exact quadraticHarmonic3D_harmonic hp)
    (quadraticHarmonic3D_analytic_side_condition p hp)

/-- The Euclidean Laplacian of `x² + y² - 2z²` is zero. -/
theorem laplacian_quadraticHarmonic3D_zero (p : ℝ^3) :
    laplacian (fun q : ℝ^3 ↦ quadraticHarmonic3D.eval q) p = 0 := by
  have hvalid : quadraticHarmonic3D.ValidAt p := by
    symbolic_assumptions
  have hdiff : ∀ i : Fin 3, (quadraticHarmonic3D.diff i).ValidAt p := by
    symbolic_assumptions
  rw [← Verified.Expr.closedLaplacian_eval_eq_laplacian
    (expr := quadraticHarmonic3D) (x := p) hvalid hdiff]
  simpa [quadraticHarmonic3DResidual, Scalar.laplaceResidual, Scalar.residual,
    Scalar.laplace, DiffExpr.Lap, Scalar.u,
    DiffExpr.Equation.closedResidual, DiffExpr.Equation.residual, DiffExpr.lower,
    Exact.exprFn, Exact.zeroFn] using quadraticHarmonic3D_harmonic trivial

/-- The polynomial satisfies the Laplace residual on `ℝ^3`. -/
theorem quadraticHarmonic3D_satisfiesPDEProblem :
    ∀ p ∈ (laplaceEquation 3).domain,
      (laplaceEquation 3).residual
        (fun q : ℝ^3 ↦ quadraticHarmonic3D.eval q) p = 0 := by
  intro p _hp
  simpa [PDE.LinearPDE.residual, laplaceEquation, laplacian] using
    laplacian_quadraticHarmonic3D_zero p

end

end LaplacianEquation.Symbolic
