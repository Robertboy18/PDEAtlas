/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Symbolic.Radial.PuncturedPlane
public import CAS.ClosedForm.Scalar.Models
public import CAS.ExactTactic
public import PDE.Symbolic.ClosedForm.Differential.Equation

/-!
# A symbolic rational harmonic function

The function `x / (x² + y²)` is the real part of `1 / z` for `z = x + iy`, hence harmonic on the
punctured plane. We represent it as a `Verified.Expr` and check harmonicity through the
symbolic pipeline: the compiled Laplace residual is a rational expression that `cas` reduces to
zero under the side condition `x² + y² ≠ 0`, and the validity of the expression and its first
derivatives off the origin then transports the identity to the Euclidean `laplacian` and to the
analytic residual of the symbolic Laplace equation. Unlike the polynomial examples, every
statement here carries the punctured-domain hypothesis, because the expression has a pole at
the origin.

## Main results

* `rationalHarmonic2DResidual_eval_eq_zero_of_sum_sq_ne_zero`: the symbolic Laplace residual
  vanishes wherever `x² + y² ≠ 0`.
* `laplacian_rationalHarmonic2D_of_ne_zero`: the Euclidean Laplacian of `x / (x² + y²)` is
  zero on the punctured plane.
* `rationalHarmonic2D_analytic_residual_zero_of_ne_zero`: the analytic residual vanishes on
  the punctured plane.
-/

@[expose] public section

open PDE (laplacian)

namespace LaplacianEquation.Symbolic

open CAS
open CAS.Euclid2
open scoped CAS

noncomputable section

/-! ## Rational singular harmonic ansatz -/

/-- A rational harmonic function, the real-coordinate core of `Re(1/z)`. -/
def rationalHarmonic2D : Verified.Expr (Fin 2) :=
  (x : Verified.Expr (Fin 2)) / (x ^ 2 + y ^ 2)

/-- Closed symbolic residual for `x/(x²+y²)` under the Laplace equation. -/
def rationalHarmonic2DResidual : Verified.Expr (Fin 2) :=
  Scalar.laplaceResidual rationalHarmonic2D

/--
Pointwise symbolic residual calculation for the rational harmonic ansatz.

The symbolic residual is the Laplacian of `x / (x² + y²)`.  The expression is
mathematically meaningful off the pole, where `x² + y² ≠ 0`, and the residual
simplifies to zero there by direct algebra.
-/
theorem rationalHarmonic2DResidual_eval_eq_zero_of_sum_sq_ne_zero
    (p : ℝ^2) (_h : (p 0) ^ 2 + (p 1) ^ 2 ≠ 0) :
    rationalHarmonic2DResidual.eval p = 0 := by
  cas [rationalHarmonic2DResidual, Scalar.laplaceResidual,
    Scalar.laplace, Scalar.residual, DiffExpr.Lap, Scalar.u, Scalar.ansatz,
    DiffExpr.Equation.closedResidual, DiffExpr.Equation.residual, DiffExpr.lower,
    rationalHarmonic2D, Verified.Expr.diff, Verified.Expr.eval,
    Verified.Expr.closedLaplacian, Verified.Expr.eval_simplify,
    Verified.Expr.SymVar.expr]

/-- Equality-to-zero form of the rational harmonic symbolic residual on the punctured plane. -/
theorem rationalHarmonic2D_eqOn_zero_punctured :
    Set.EqOn (Exact.exprFn rationalHarmonic2DResidual) Exact.zeroFn puncturedPlane2D := by
  intro p hp
  have hzero :
      rationalHarmonic2DResidual.eval p = 0 :=
    rationalHarmonic2DResidual_eval_eq_zero_of_sum_sq_ne_zero p
      (sum_sq_ne_zero_of_ne_zero p hp)
  simpa [Exact.exprFn, Exact.zeroFn] using hzero

/-- The rational harmonic symbolic expression is valid away from the origin. -/
private theorem rationalHarmonic2D_validAt_of_ne_zero
    (p : ℝ^2) (hp : p ∈ puncturedPlane2D) :
    rationalHarmonic2D.ValidAt p := by
  have hsum_ne := sum_sq_ne_zero_of_ne_zero p hp
  symbolic_assumptions

/-- The first derivatives of `x/(x²+y²)` are valid away from the origin. -/
private theorem rationalHarmonic2D_diff_validAt_of_ne_zero
    (p : ℝ^2) (hp : p ∈ puncturedPlane2D) :
    ∀ i : Fin 2, (rationalHarmonic2D.diff i).ValidAt p := by
  have hsum_sq_ne := sum_sq_sq_ne_zero_of_ne_zero p hp
  intro coord
  fin_cases coord <;>
    simp [rationalHarmonic2D, Verified.Expr.ValidAt, Verified.Expr.diff,
      Verified.Expr.eval, Verified.Expr.SymVar.expr, hsum_sq_ne]

/-- Analytic Laplacian theorem for the rational harmonic function `x/(x²+y²)`.

The symbolic differentiation reduces the claim to a rational identity, while
the punctured-domain hypothesis supplies the nonvanishing denominator.
-/
theorem laplacian_rationalHarmonic2D_of_ne_zero
    (p : ℝ^2) (hp : p ∈ puncturedPlane2D) :
    laplacian (fun q : ℝ^2 ↦ rationalHarmonic2D.eval q) p = 0 := by
  have h0 : rationalHarmonic2D.ValidAt p := rationalHarmonic2D_validAt_of_ne_zero p hp
  have h1 : ∀ i : Fin 2, (rationalHarmonic2D.diff i).ValidAt p :=
    rationalHarmonic2D_diff_validAt_of_ne_zero p hp
  rw [← Verified.Expr.closedLaplacian_eval_eq_laplacian
    (expr := rationalHarmonic2D) (x := p) h0 h1]
  exact rationalHarmonic2D_eqOn_zero_punctured hp

/-- Analytic side conditions for the rational harmonic residual off the origin. -/
private theorem rationalHarmonic2D_analytic_side_condition_of_ne_zero
    (p : ℝ^2) (hp : p ∈ puncturedPlane2D) :
    DiffExpr.AnalyticSideCondition
      (Scalar.ansatz rationalHarmonic2D) p (Scalar.laplace (n := 2)).residual := by
  have h0 : rationalHarmonic2D.ValidAt p := rationalHarmonic2D_validAt_of_ne_zero p hp
  have h1 : ∀ i : Fin 2, (rationalHarmonic2D.diff i).ValidAt p :=
    rationalHarmonic2D_diff_validAt_of_ne_zero p hp
  simp [DiffExpr.AnalyticSideCondition, DiffExpr.lower, DiffExpr.Lap,
    Scalar.laplace, DiffExpr.Equation.residual, Scalar.u,
    Scalar.ansatz, h0, h1]

/-- Analytic residual theorem for the rational harmonic function `x/(x²+y²)`. -/
theorem rationalHarmonic2D_analytic_residual_zero_of_ne_zero
    (p : ℝ^2) (hp : p ∈ puncturedPlane2D) :
    DiffExpr.Equation.analyticResidual
      (Scalar.ansatz rationalHarmonic2D) p (Scalar.laplace (n := 2)) = 0 := by
  have hclosed :
      (Scalar.residual (Scalar.laplace (n := 2)) rationalHarmonic2D).eval p = 0 := by
    simpa [Exact.exprFn, Exact.zeroFn, rationalHarmonic2DResidual,
      Scalar.laplaceResidual] using
      rationalHarmonic2D_eqOn_zero_punctured hp
  exact DiffExpr.Equation.analyticResidual_eq_zero_of_closedResidualVanishesAt hclosed
    (rationalHarmonic2D_analytic_side_condition_of_ne_zero p hp)

end

end LaplacianEquation.Symbolic
