/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Symbolic.Heat.Equations
public import PDE.Parabolic.Symbolic.Heat.SpatialSlice
public import PDE.Symbolic.Calculus.WeakFormIntegrands
public import PDE.Symbolic.ClosedForm.Tactic.Residual
public import CAS.ExactTactic
public import PDE.Parabolic.Heat.Equation

/-!
# Polynomial heat-equation residual certificates

Two polynomial solutions of the heat equation, checked by the certified symbolic
differentiator (`cas`) and then transported to ordinary Euclidean derivatives:

* in one space dimension, `u(t, x) = x² + 2t`, for which `uₜ = 2 = uₓₓ`;
* in two space dimensions, `u(t, x, y) = x² + y² + 4t`, for which `uₜ = 4 = Δu`.

In the symbolic coordinates the first variable (`x` in `Euclid2`, `x` in `Euclid3`) is time
and the remaining variables are space, matching `heat1DEquation` and `heat2DEquation`.

The one-dimensional example exercises the weak-form integrand
`uₜ v + uₓ vₓ - f v` rather than the pointwise residual. With `f = 0` and the test
function `v = x` the integrand is `2 · x + 2x · 1 = 4x`. This closed form is proved
pointwise, as an integral identity over any domain, and in the `ResidualBound`/`ApproxOn`
certificate formats. The two-dimensional example goes through the pointwise coordinate
residual and ends in the predicate `HeatEquation.heatEquation` on all of spacetime.

## Main results

* `polynomialHeat1D_weak_integrand_eval_eq_euclidean_derivatives`,
  `polynomialHeat1D_weak_integrand_integral_eq_euclidean_derivatives`: the symbolic weak
  integrand agrees with the `partialDeriv` expression `uₜ v + ∑ᵢ ∂ᵢu ∂ᵢv - f v`.
* `polynomialHeat1D_weak_integrand_eval_eq_expected`,
  `polynomialHeat1D_weak_integrand_integral_eq_expected`: that integrand is `4x`.
* `polynomialHeat2D_residual_eq_zero`, `polynomialHeat2D_analyticResidual_zero`: the
  two-dimensional residual vanishes symbolically and analytically.
* `polynomialHeat2D_satisfiesPDEProblem_univ`: `x² + y² + 4t` satisfies
  `HeatEquation.heatEquation (n := 2) Set.univ`.

## Implementation notes

The integral identities are consequences of pointwise identities, integrated over an arbitrary
set; no integration by parts takes place, so they are not weak formulations in the PDE sense.
The passage from the coordinate residual to the heat equation uses the slice-Laplacian
identity `laplacian_timeSpaceCons_slice2_eval_eq` from
`PDE.Parabolic.Symbolic.Heat.SpatialSlice`, whose validity hypotheses are discharged by
`symbolic_assumptions` because polynomials have no domain restrictions.
-/

@[expose] public section

open PDE (laplacian SatisfiesPDEProblem)

namespace HeatEquation.Symbolic

open PDE.Common
open CAS
open scoped CAS
open CAS.Certificate
open MeasureTheory

noncomputable section

/-! ## One-dimensional polynomial heat ansatz -/

namespace Space1

open CAS.Euclid2

/-- `u(t,x) = x^2 + 2t`, with symbolic `x` as time and `y` as space. -/
def polynomialHeat1DAnsatz : Verified.Expr (Fin 2) :=
  y ^ 2 + 2 * x

/-! ### Weak-form integrand bridge -/

/--
The residual below records the weak heat integrand identity
`u_t v + u_x v_x - f v`.

Here `u(t,x)=x²+2t`, `f=0`, and `v=x`, so the closed-form integrand is `4x`
in the spatial variable.  In the symbolic coordinates below, `x` is time and
`y` is the single spatial coordinate, so the expected expression is `4*y`.
-/
def polynomialHeat1DWeakResidual : Verified.Expr (Fin 2) :=
  heatWeakResidualIntegrand
    x [y] polynomialHeat1DAnsatz
    (0 : Verified.Expr (Fin 2)) (y : Verified.Expr (Fin 2)) -
    (4 * y : Verified.Expr (Fin 2))

/-- The sample weak heat integrand agrees pointwise with its expected value. -/
theorem polynomialHeat1D_weak_integrand_residual_eq_zero :
    Set.EqOn
      (Exact.exprFn polynomialHeat1DWeakResidual)
      Exact.zeroFn
      Set.univ := by
  cas

/--
The weak heat integrand in Euclidean derivatives.

This is the form used in weak heat-equation arguments,
`u_t v + u_x v_x - f v`, with the spatial derivative list chosen explicitly.
-/
theorem polynomialHeat1D_weak_integrand_eval_eq_euclidean_derivatives
    (p : ℝ^2) :
    (heatWeakResidualIntegrand
        x [y] polynomialHeat1DAnsatz
        (0 : Verified.Expr (Fin 2)) (y : Verified.Expr (Fin 2))).eval p =
      (∂[x.idx]
          (fun q : ℝ^2 ↦ polynomialHeat1DAnsatz.eval q)) p *
        (y : Verified.Expr (Fin 2)).eval p +
      ([y].map fun coord ↦
        (∂[coord.idx]
            (fun q : ℝ^2 ↦ polynomialHeat1DAnsatz.eval q)) p *
          (∂[coord.idx]
            (fun q : ℝ^2 ↦ (y : Verified.Expr (Fin 2)).eval q)) p).sum -
      (0 : Verified.Expr (Fin 2)).eval p * (y : Verified.Expr (Fin 2)).eval p := by
  exact heatWeakResidualIntegrand_eval_eq_time_mul_add_spatial_sum_sub
    (t := x) (spatial := [y]) (u := polynomialHeat1DAnsatz)
    (f := (0 : Verified.Expr (Fin 2))) (v := (y : Verified.Expr (Fin 2))) (p := p)
    (by symbolic_assumptions) (by symbolic_assumptions)

/-- The Euclidean derivative identity for the sample weak heat integrand, integrated. -/
theorem polynomialHeat1D_weak_integrand_integral_eq_euclidean_derivatives
    (Ω : Set (ℝ^2)) :
    (∫ q in Ω,
      (heatWeakResidualIntegrand
        x [y] polynomialHeat1DAnsatz
        (0 : Verified.Expr (Fin 2)) (y : Verified.Expr (Fin 2))).eval q) =
      ∫ q in Ω,
        ((∂[x.idx]
            (fun r : ℝ^2 ↦ polynomialHeat1DAnsatz.eval r)) q *
          (y : Verified.Expr (Fin 2)).eval q +
        ([y].map fun coord ↦
          (∂[coord.idx]
              (fun r : ℝ^2 ↦ polynomialHeat1DAnsatz.eval r)) q *
            (∂[coord.idx]
              (fun r : ℝ^2 ↦ (y : Verified.Expr (Fin 2)).eval r)) q).sum -
        (0 : Verified.Expr (Fin 2)).eval q * (y : Verified.Expr (Fin 2)).eval q) := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with q
  exact polynomialHeat1D_weak_integrand_eval_eq_euclidean_derivatives q

/-- Closed-form value of the sample weak heat integrand. -/
theorem polynomialHeat1D_weak_integrand_eval_eq_expected
    (p : ℝ^2) :
    (heatWeakResidualIntegrand
        x [y] polynomialHeat1DAnsatz
        (0 : Verified.Expr (Fin 2)) (y : Verified.Expr (Fin 2))).eval p =
      (4 * y : Verified.Expr (Fin 2)).eval p := by
  simp [heatWeakResidualIntegrand, spatialDirichletIntegrand, spatialDirichletRaw,
    polynomialHeat1DAnsatz, Verified.Expr.Alg.eval_normalize,
    Verified.Expr.closedPartial, Verified.Expr.eval, Verified.Expr.SymVar.expr]
  ring_nf

/-- The closed-form value of the sample weak heat integrand, integrated. -/
theorem polynomialHeat1D_weak_integrand_integral_eq_expected
    (Ω : Set (ℝ^2)) :
    (∫ q in Ω,
      (heatWeakResidualIntegrand
        x [y] polynomialHeat1DAnsatz
        (0 : Verified.Expr (Fin 2)) (y : Verified.Expr (Fin 2))).eval q) =
      ∫ q in Ω, (4 * y : Verified.Expr (Fin 2)).eval q := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with q
  exact polynomialHeat1D_weak_integrand_eval_eq_expected q

/-- Residual-bound form of the weak heat-form residual certificate. -/
theorem polynomialHeat1D_weak_integrand_residual_bound :
    ResidualBound
      (Exact.exprFn polynomialHeat1DWeakResidual)
      Set.univ
      0 := by
  cas

/-- Zero-error approximation for the weak heat-form residual. -/
theorem polynomialHeat1D_weak_integrand_zero_error :
    ApproxOn
      (Exact.exprFn polynomialHeat1DWeakResidual)
      Exact.zeroFn
      Set.univ
      0 := by
  exact approxOn_of_eqOn polynomialHeat1D_weak_integrand_residual_eq_zero

end Space1

/-! ## Two-space-dimensional polynomial heat ansatz -/

namespace Space2

open CAS.Euclid3

/-- `u(t,x,y)=x^2+y^2+4t`, with `Euclid3.x` as time. -/
def polynomialHeat2DAnsatz : Verified.Expr (Fin 3) :=
  y ^ 2 + z ^ 2 + 4 * x

/-- Compiled symbolic residual for the two-space-dimensional polynomial heat ansatz. -/
def polynomialHeat2DResidual : Verified.Expr (Fin 3) :=
  Scalar.residual heat2DEquation polynomialHeat2DAnsatz

/-- The two-dimensional polynomial heat residual vanishes identically. -/
theorem polynomialHeat2D_residual_eq_zero :
    Set.EqOn
      (Exact.exprFn polynomialHeat2DResidual)
      Exact.zeroFn
      Set.univ := by
  cas

/-- Analytic Euclidean residual version of the two-space-dimensional polynomial check. -/
theorem polynomialHeat2D_analyticResidual_zero :
    ∀ p, p ∈ Set.univ →
      DiffExpr.Equation.analyticResidual
        (Scalar.ansatz polynomialHeat2DAnsatz) p heat2DEquation = 0 := by
  intro p _hp
  have hclosed :
      (Scalar.residual heat2DEquation polynomialHeat2DAnsatz).eval p = 0 := by
    simpa [polynomialHeat2DResidual, Exact.exprFn, Exact.zeroFn] using
      polynomialHeat2D_residual_eq_zero trivial
  exact DiffExpr.Equation.analyticResidual_eq_zero_of_closedResidualVanishesAt
    hclosed (by symbolic_residual)

/--
The polynomial `u(t,x,y)=x²+y²+4t` solves the heat equation on all of spacetime.

The CAS proves the spacetime coordinate residual. The slice-Laplacian identity
used for the Gaussian kernel turns that calculation into the predicate
`HeatEquation.heatEquation` on all of spacetime.
-/
theorem polynomialHeat2D_satisfiesPDEProblem_univ :
    SatisfiesPDEProblem
      (HeatEquation.heatEquation (n := 2) Set.univ)
      (fun p : ℝ^3 ↦ polynomialHeat2DAnsatz.eval p) := by
  apply HeatEquation.heatEquation.of_residual (n := 2)
  intro p _hp
  have hcoord :
      (∂[0]
          (fun q : ℝ^3 ↦ polynomialHeat2DAnsatz.eval q)) p -
        ((∂[1]
            (fun q : ℝ^3 ↦ (polynomialHeat2DAnsatz.diff 1).eval q)) p +
          (∂[2]
            (fun q : ℝ^3 ↦ (polynomialHeat2DAnsatz.diff 2).eval q)) p) = 0 := by
    have h := polynomialHeat2D_analyticResidual_zero p trivial
    simpa [heat2DEquation, Scalar.heatSpatial, Scalar.spatialLaplacian,
      Scalar.u, DiffExpr.D, DiffExpr.D2,
      DiffExpr.lower, Verified.Expr.eval, DiffExpr.Equation.analyticResidual,
      DiffExpr.analyticEval, DiffExpr.Equation.residual] using h
  have hlap :
      laplacian (n := 2)
          (fun y : ℝ^2 ↦
            polynomialHeat2DAnsatz.eval (PDE.Common.timeSpaceCons (n := 2) (p 0) y))
          (spatialPartCLM 2 p) =
        (∂[(1 : Fin 3)]
            (fun q : ℝ^3 ↦
              (polynomialHeat2DAnsatz.diff (1 : Fin 3)).eval q)) p +
          (∂[(2 : Fin 3)]
            (fun q : ℝ^3 ↦
              (polynomialHeat2DAnsatz.diff (2 : Fin 3)).eval q)) p :=
    laplacian_timeSpaceCons_slice2_eval_eq polynomialHeat2DAnsatz p
      (by
        intro y
        unfold polynomialHeat2DAnsatz
        symbolic_assumptions)
      (by
        intro i y
        unfold polynomialHeat2DAnsatz
        fin_cases i <;> symbolic_assumptions)
  simpa [HeatEquation.heatOperator, hlap] using hcoord

end Space2

end

end HeatEquation.Symbolic
