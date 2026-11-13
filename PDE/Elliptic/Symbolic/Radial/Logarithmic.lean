/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution
public import PDE.Elliptic.Symbolic.Radial.PuncturedPlane
public import CAS.ClosedForm.Scalar.Models
public import CAS.ExactTactic
public import PDE.Symbolic.ClosedForm.Differential.Equation

/-!
# Symbolic logarithmic fundamental solution

The fundamental solution of Laplace's equation in the plane is

`Φ(x) = -(1 / (2π)) log ‖x‖ = -(1 / (4π)) log (x₁² + x₂²)`,

harmonic on the punctured plane (Evans, PDE, §2.2.1). We treat both the unnormalized
core `log (x² + y²)` and the normalized expression as `Verified.Expr` terms and prove, on
`puncturedPlane2D`, that their symbolic and analytic Laplace residuals vanish and that the
Euclidean `laplacian` of the evaluated expressions is zero. We also identify the normalized
symbolic expression with `PotentialTheory.fundamentalSolution 2` away from the pole, so the
symbolic checks attach to the same closed form used in the analytic potential theory rather than
to a parallel convention. The three-dimensional Newtonian core is treated separately in
`PDE.Elliptic.Symbolic.Radial.Newtonian`.

The logarithm and its derivatives are only valid where `x² + y² ≠ 0`; the punctured-domain
hypothesis supplies exactly that side condition, which is why every statement is restricted to
`puncturedPlane2D`. The expressions and their symbolic derivatives come from SymLean, whose
`symbolic_assumptions` tactic discharges these validity conditions. Its `cas` tactic closes the
residual of the normalized expression; for `log (x² + y²)` itself, `field_simp` and `ring_nf`
close the residual after unfolding.

## Main results

* `logRadiusSquared2DResidual_eval_eq_zero_of_sum_sq_ne_zero`,
  `laplacian_logRadiusSquared2D_of_ne_zero`: `log (x² + y²)` is harmonic off the origin.
* `laplaceFundamental2DSymbolic_eval_eq_fundamentalSolution`: the normalized symbolic
  expression equals `PotentialTheory.fundamentalSolution 2` on the punctured plane.
* `laplacian_laplaceFundamental2DSymbolic_of_ne_zero`,
  `laplaceFundamental2DSymbolic_analytic_residual_zero_of_ne_zero`: harmonicity of the
  normalized fundamental solution, in Euclidean and analytic-residual form.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.1, the radial equation (5), the fundamental solution
  (6) and its harmonicity off the origin, p. 22.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian)

namespace LaplacianEquation.Symbolic

open CAS
open CAS.Euclid2
open scoped CAS

noncomputable section

/-! ## Logarithmic singular harmonic ansatz -/

/-- The normalizing constant in the two-dimensional fundamental solution is nonzero. -/
private theorem four_mul_pi_ne_zero : (4 * Real.pi : ℝ) ≠ 0 := by
  positivity

/-- The square of the normalizing constant is nonzero. -/
private theorem four_mul_pi_sq_ne_zero : (4 * Real.pi : ℝ) ^ 2 ≠ 0 :=
  pow_ne_zero 2 four_mul_pi_ne_zero

/-- The logarithmic radial expression `log(x²+y²)`. -/
def logRadiusSquared2D : Verified.Expr (Fin 2) :=
  .log ((x : Verified.Expr (Fin 2)) ^ 2 + (y : Verified.Expr (Fin 2)) ^ 2)

/-- The logarithmic radial expression is valid away from the origin. -/
private theorem logRadiusSquared2D_validAt_of_ne_zero
    (p : ℝ^2) (hp : p ∈ puncturedPlane2D) :
    logRadiusSquared2D.ValidAt p := by
  have hpos := sum_sq_pos_of_ne_zero p hp
  have hsum_ne := ne_of_gt hpos
  symbolic_assumptions

/-- The first derivatives of `log(x²+y²)` are valid away from the origin. -/
private theorem logRadiusSquared2D_diff_validAt_of_ne_zero
    (p : ℝ^2) (hp : p ∈ puncturedPlane2D) :
    ∀ i : Fin 2, (logRadiusSquared2D.diff i).ValidAt p := by
  have hpos := sum_sq_pos_of_ne_zero p hp
  have hsum_ne := sum_sq_ne_zero_of_ne_zero p hp
  unfold logRadiusSquared2D
  symbolic_assumptions

/-- Compiled symbolic residual for `log(x²+y²)` under the Laplace equation. -/
def logRadiusSquared2DResidual : Verified.Expr (Fin 2) :=
  Scalar.laplaceResidual logRadiusSquared2D

/--
Pointwise symbolic residual calculation for `log(x²+y²)`.

The closed residual is the symbolic Laplacian of `log(x²+y²)`, and the only
mathematical side condition needed for the algebra is `x²+y² ≠ 0`.
-/
theorem logRadiusSquared2DResidual_eval_eq_zero_of_sum_sq_ne_zero
    (p : ℝ^2) (h : (p 0) ^ 2 + (p 1) ^ 2 ≠ 0) :
    logRadiusSquared2DResidual.eval p = 0 := by
  simp [logRadiusSquared2DResidual, Scalar.laplaceResidual,
    Scalar.laplace, Scalar.residual,
    DiffExpr.Lap, Scalar.u, Scalar.ansatz,
    DiffExpr.Equation.closedResidual, DiffExpr.Equation.residual,
    DiffExpr.lower, logRadiusSquared2D, Verified.Expr.diff, Verified.Expr.eval,
    Verified.Expr.closedLaplacian,
    Verified.Expr.eval_simplify, Verified.Expr.SymVar.expr]
  field_simp [h]
  ring_nf

/-- Equality-to-zero form of the symbolic logarithmic residual on the punctured plane. -/
theorem logRadiusSquared2D_eqOn_zero_punctured :
    Set.EqOn (Exact.exprFn logRadiusSquared2DResidual) Exact.zeroFn puncturedPlane2D := by
  intro p hp
  have hzero :
      logRadiusSquared2DResidual.eval p = 0 := by
    exact logRadiusSquared2DResidual_eval_eq_zero_of_sum_sq_ne_zero p
      (sum_sq_ne_zero_of_ne_zero p hp)
  simpa [Exact.exprFn, Exact.zeroFn] using hzero

/-- Analytic Laplacian theorem for `log(x²+y²)`: its Euclidean Laplacian vanishes at every
point of the punctured plane.

The symbolic residual vanishes by `logRadiusSquared2D_eqOn_zero_punctured`, and the
punctured-domain hypothesis supplies the validity side conditions for the logarithm and its
first derivatives that carry this over to `laplacian`.
-/
theorem laplacian_logRadiusSquared2D_of_ne_zero
    (p : ℝ^2) (hp : p ∈ puncturedPlane2D) :
    laplacian (fun q : ℝ^2 ↦ logRadiusSquared2D.eval q) p = 0 := by
  have h0 : logRadiusSquared2D.ValidAt p := logRadiusSquared2D_validAt_of_ne_zero p hp
  have h1 : ∀ i : Fin 2, (logRadiusSquared2D.diff i).ValidAt p :=
    logRadiusSquared2D_diff_validAt_of_ne_zero p hp
  rw [← Verified.Expr.closedLaplacian_eval_eq_laplacian
    (expr := logRadiusSquared2D) (x := p) h0 h1]
  simpa [Exact.exprFn, Exact.zeroFn, logRadiusSquared2DResidual,
    Scalar.laplaceResidual, Scalar.residual,
    Scalar.laplace, DiffExpr.Lap, Scalar.u,
    DiffExpr.Equation.closedResidual, DiffExpr.Equation.residual, DiffExpr.lower] using
    logRadiusSquared2D_eqOn_zero_punctured hp

/-- Analytic side conditions for the logarithmic Laplace residual on the punctured plane. -/
private theorem logRadiusSquared2D_analytic_side_condition_of_ne_zero
    (p : ℝ^2) (hp : p ∈ puncturedPlane2D) :
    DiffExpr.AnalyticSideCondition
      (Scalar.ansatz logRadiusSquared2D) p (Scalar.laplace (n := 2)).residual := by
  have h0 : logRadiusSquared2D.ValidAt p := logRadiusSquared2D_validAt_of_ne_zero p hp
  have h1 : ∀ i : Fin 2, (logRadiusSquared2D.diff i).ValidAt p :=
    logRadiusSquared2D_diff_validAt_of_ne_zero p hp
  simp [DiffExpr.AnalyticSideCondition, DiffExpr.lower, DiffExpr.Lap,
    Scalar.laplace, DiffExpr.Equation.residual, Scalar.u,
    Scalar.ansatz, h0, h1]

/-- Analytic residual theorem for `log(x²+y²)` on the punctured plane. -/
theorem logRadiusSquared2D_analytic_residual_zero_of_ne_zero
    (p : ℝ^2) (hp : p ∈ puncturedPlane2D) :
    DiffExpr.Equation.analyticResidual
      (Scalar.ansatz logRadiusSquared2D) p (Scalar.laplace (n := 2)) = 0 := by
  have hclosed :
      (Scalar.residual (Scalar.laplace (n := 2)) logRadiusSquared2D).eval p = 0 := by
    simpa [Exact.exprFn, Exact.zeroFn, logRadiusSquared2DResidual,
      Scalar.laplaceResidual] using
      logRadiusSquared2D_eqOn_zero_punctured hp
  exact DiffExpr.Equation.analyticResidual_eq_zero_of_closedResidualVanishesAt hclosed
    (logRadiusSquared2D_analytic_side_condition_of_ne_zero p hp)

/-! ## Normalized two-dimensional fundamental solution -/

/-- The Poisson-normalized two-dimensional Laplace fundamental solution in coordinates.

This is the same closed form as `PotentialTheory.fundamentalSolution 2` away from the pole,
written in the symbolic language so the residual can be inspected by the CAS pipeline. -/
def laplaceFundamental2DSymbolic : Verified.Expr (Fin 2) :=
  -((1 : Verified.Expr (Fin 2)) / (4 * (.pi : Verified.Expr (Fin 2)))) * logRadiusSquared2D

/--
The symbolic normalized logarithmic fundamental solution agrees with the
analytic `PotentialTheory.fundamentalSolution 2` away from the pole.

The residual theorems below are therefore about the same function as the analytic potential
theory.
-/
theorem laplaceFundamental2DSymbolic_eval_eq_fundamentalSolution
    (p : ℝ^2) (hp : p ∈ puncturedPlane2D) :
    laplaceFundamental2DSymbolic.eval p =
      PotentialTheory.fundamentalSolution 2 p := by
  have hp0 : p ≠ 0 := by
    change p ≠ 0 at hp
    exact hp
  have hnorm : ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 :=
    by simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq p
  have hlog :
      Real.log ((p 0) ^ 2 + (p 1) ^ 2) = 2 * Real.log ‖p‖ := by
    rw [← hnorm, Real.log_pow]
    norm_num
  simp only [Verified.Expr.eval, laplaceFundamental2DSymbolic,
    logRadiusSquared2D, Verified.Expr.SymVar.expr,
    Euclid2.x, Euclid2.y, Verified.Expr.eval_mul_operator,
    Verified.Expr.eval_div_operator, Nat.cast_one, Nat.cast_ofNat, mul_comm,
    div_eq_mul_inv, mul_inv_rev, one_mul, Verified.Expr.eval_pow_operator,
    neg_mul, mul_assoc, PotentialTheory.fundamentalSolution, hp0, ↓reduceDIte,
    OfNat.ofNat_ne_one, ↓reduceIte, neg_inj, mul_eq_mul_left_iff, inv_eq_zero,
    Real.pi_ne_zero, or_false]
  rw [hlog]
  ring

/-- Closed symbolic residual for the normalized two-dimensional fundamental solution. -/
def laplaceFundamental2DResidual : Verified.Expr (Fin 2) :=
  Scalar.laplaceResidual laplaceFundamental2DSymbolic

/-- The normalized fundamental symbolic expression is valid away from the origin. -/
private theorem laplaceFundamental2DSymbolic_validAt_of_ne_zero
    (p : ℝ^2) (hp : p ∈ puncturedPlane2D) :
    laplaceFundamental2DSymbolic.ValidAt p := by
  have hpos := sum_sq_pos_of_ne_zero p hp
  have hsum_ne := ne_of_gt hpos
  have h4pi := four_mul_pi_ne_zero
  symbolic_assumptions

/-- The first derivatives of the normalized fundamental expression are valid away from the pole. -/
private theorem laplaceFundamental2DSymbolic_diff_validAt_of_ne_zero
    (p : ℝ^2) (hp : p ∈ puncturedPlane2D) :
    ∀ i : Fin 2, (laplaceFundamental2DSymbolic.diff i).ValidAt p := by
  have hpos := sum_sq_pos_of_ne_zero p hp
  have hsum_ne := sum_sq_ne_zero_of_ne_zero p hp
  have h4pi := four_mul_pi_ne_zero
  have h4pi_sq := four_mul_pi_sq_ne_zero
  unfold laplaceFundamental2DSymbolic logRadiusSquared2D
  symbolic_assumptions

/--
Analytic Laplacian theorem for the normalized two-dimensional fundamental
expression.

Ordinary Lean proves validity of the logarithmic expression away from the
pole. The checked CAS closes only the constant-scaled symbolic residual, and
the derivative identity transports that result to the Euclidean Laplacian.
-/
theorem laplacian_laplaceFundamental2DSymbolic_of_ne_zero
    (p : ℝ^2) (hp : p ∈ puncturedPlane2D) :
    laplacian
      (fun q : ℝ^2 ↦ laplaceFundamental2DSymbolic.eval q) p = 0 := by
  have h0 : laplaceFundamental2DSymbolic.ValidAt p :=
    laplaceFundamental2DSymbolic_validAt_of_ne_zero p hp
  have h1 : ∀ i : Fin 2, (laplaceFundamental2DSymbolic.diff i).ValidAt p :=
    laplaceFundamental2DSymbolic_diff_validAt_of_ne_zero p hp
  have hcas :
      Set.EqOn
        (Exact.exprFn laplaceFundamental2DResidual)
        Exact.zeroFn puncturedPlane2D := by
    cas
  rw [← Verified.Expr.closedLaplacian_eval_eq_laplacian
    (expr := laplaceFundamental2DSymbolic) (x := p) h0 h1]
  simpa [Exact.exprFn, Exact.zeroFn, laplaceFundamental2DResidual,
    Scalar.laplaceResidual, Scalar.residual, Scalar.laplace,
    DiffExpr.Lap, Scalar.u, DiffExpr.Equation.closedResidual,
    DiffExpr.Equation.residual, DiffExpr.lower] using
    hcas hp

/-- Analytic side conditions for the normalized fundamental-solution residual off the pole. -/
private theorem laplaceFundamental2DSymbolic_analytic_side_condition_of_ne_zero
    (p : ℝ^2) (hp : p ∈ puncturedPlane2D) :
    DiffExpr.AnalyticSideCondition
      (Scalar.ansatz laplaceFundamental2DSymbolic) p (Scalar.laplace (n := 2)).residual := by
  have h0 : laplaceFundamental2DSymbolic.ValidAt p :=
    laplaceFundamental2DSymbolic_validAt_of_ne_zero p hp
  have h1 : ∀ i : Fin 2, (laplaceFundamental2DSymbolic.diff i).ValidAt p :=
    laplaceFundamental2DSymbolic_diff_validAt_of_ne_zero p hp
  simp [DiffExpr.AnalyticSideCondition, DiffExpr.lower, DiffExpr.Lap,
    Scalar.laplace, DiffExpr.Equation.residual, Scalar.u,
    Scalar.ansatz, h0, h1]

/-- Analytic residual theorem for the normalized two-dimensional fundamental expression. -/
theorem laplaceFundamental2DSymbolic_analytic_residual_zero_of_ne_zero
    (p : ℝ^2) (hp : p ∈ puncturedPlane2D) :
    DiffExpr.Equation.analyticResidual
      (Scalar.ansatz laplaceFundamental2DSymbolic) p (Scalar.laplace (n := 2)) = 0 := by
  have hcas :
      Set.EqOn
        (Exact.exprFn laplaceFundamental2DResidual)
        Exact.zeroFn puncturedPlane2D := by
    cas
  have hclosed :
      (Scalar.residual (Scalar.laplace (n := 2)) laplaceFundamental2DSymbolic).eval p = 0 := by
    simpa [Exact.exprFn, Exact.zeroFn, laplaceFundamental2DResidual,
      Scalar.laplaceResidual] using hcas hp
  exact DiffExpr.Equation.analyticResidual_eq_zero_of_closedResidualVanishesAt hclosed
    (laplaceFundamental2DSymbolic_analytic_side_condition_of_ne_zero p hp)
end

end LaplacianEquation.Symbolic
