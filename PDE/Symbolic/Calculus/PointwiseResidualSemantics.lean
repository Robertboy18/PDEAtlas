/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Symbolic.Calculus.PointwiseResiduals
public import PDE.Symbolic.Calculus.TensorOperatorSemantics

/-!
# Analytic semantics of pointwise symbolic PDE residuals

At a point where the differentiated expressions are valid, each residual of
`PDE.Symbolic.Calculus.PointwiseResiduals` evaluates to its analytic formula: advection
(`advectionIntegrand_eval_eq_advectiveDerivative`), convective derivative
(`convectiveDerivative_eval_eq_advectiveDerivative`), the stationary Euler and Navier–Stokes
momentum components
(`eulerMomentumResidual_eval_eq_sum_mul_partialDeriv_add_partialDeriv_sub` and
`navierStokesMomentumResidual_eval_eq_sum_mul_partialDeriv_add_partialDeriv_sub_lap_sub`),
transport (`transportResidualIntegrand_eval_eq_advectiveDerivative_sub`), and divergence-form
conservation (`conservationResidualIntegrand_eval_eq_sum_partialDeriv_sub`). Most also have a
form written as an explicit sum of `partialDeriv` terms.
-/

@[expose] public section

namespace CAS

open PDE
open scoped BigOperators

/-- Symbolic advection evaluates to the sum of velocity components times analytic coordinate
partials of the advected scalar. -/
theorem advectionIntegrand_eval_eq_sum_mul_partialDeriv {n : Nat}
    (b : Fin n → Verified.Expr (Fin n)) (u : Verified.Expr (Fin n)) (x : ℝ^n)
    (hu : u.ValidAt x) :
    (advectionIntegrand b u).eval x =
      ∑ i : Fin n,
        (b i).eval x *
          (∂[i] (fun y : ℝ^n ↦ u.eval y)) x := by
  unfold advectionIntegrand Verified.Expr.closedGradient
  rw [dotProduct_eval_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  change
    (b i).eval x *
        Verified.Expr.eval (fun k : Fin n ↦ x k) (Verified.Expr.closedPartial i u) =
      (b i).eval x *
        (∂[i] (fun y : ℝ^n ↦ u.eval y)) x
  rw [Verified.Expr.closedPartial_eval_eq_partialDeriv
    (expr := u) (x := x) (i := i) hu]

/-- Symbolic advection evaluates to LeanPDE's analytic advection operator.

This formulation hides the coordinate sum behind `advectiveDerivative`. -/
theorem advectionIntegrand_eval_eq_advectiveDerivative {n : Nat}
    (b : Fin n → Verified.Expr (Fin n)) (u : Verified.Expr (Fin n)) (x : ℝ^n)
    (hu : u.ValidAt x) :
    (advectionIntegrand b u).eval x =
      advectiveDerivative
        (fun y : ℝ^n ↦ WithLp.toLp 2 (fun i : Fin n ↦ (b i).eval y))
        (fun y : ℝ^n ↦ u.eval y) x := by
  rw [advectionIntegrand_eval_eq_sum_mul_partialDeriv b u x hu]
  rw [advectiveDerivative_eq_sum_mul_partialDeriv]

/-- The `i`th symbolic convective derivative evaluates to `∑ⱼ uⱼ ∂ⱼuᵢ`. -/
theorem convectiveDerivative_eval_eq_sum_mul_partialDeriv {n : Nat}
    (u : Fin n → Verified.Expr (Fin n)) (x : ℝ^n) (i : Fin n)
    (hu : (u i).ValidAt x) :
    (convectiveDerivative u i).eval x =
      ∑ j : Fin n,
        (u j).eval x *
          (∂[j] (fun y : ℝ^n ↦ (u i).eval y)) x := by
  simpa [convectiveDerivative] using
    advectionIntegrand_eval_eq_sum_mul_partialDeriv (b := u) (u := u i) (x := x) hu

/-- Symbolic convection agrees componentwise with analytic advection of the denoted vector
field. -/
theorem convectiveDerivative_eval_eq_advectiveDerivative {n : Nat}
    (u : Fin n → Verified.Expr (Fin n)) (x : ℝ^n) (i : Fin n)
    (hu : (u i).ValidAt x) :
    (convectiveDerivative u i).eval x =
      advectiveDerivative
        (fun y : ℝ^n ↦ WithLp.toLp 2 (fun j : Fin n ↦ (u j).eval y))
        (fun y : ℝ^n ↦ (u i).eval y) x := by
  simpa [convectiveDerivative] using
    advectionIntegrand_eval_eq_advectiveDerivative (b := u) (u := u i) (x := x) hu

/-- A symbolic stationary Euler momentum component evaluates to
`∑ⱼ uⱼ ∂ⱼuᵢ + ∂ᵢp - fᵢ`. -/
theorem eulerMomentumResidual_eval_eq_sum_mul_partialDeriv_add_partialDeriv_sub {n : Nat}
    (u : Fin n → Verified.Expr (Fin n)) (p : Verified.Expr (Fin n))
    (f : Fin n → Verified.Expr (Fin n))
    (x : ℝ^n) (i : Fin n)
    (hu : (u i).ValidAt x) (hp : p.ValidAt x) :
    (eulerMomentumResidual u p f i).eval x =
      (∑ j : Fin n,
        (u j).eval x *
          (∂[j] (fun y : ℝ^n ↦ (u i).eval y)) x) +
        (∂[i] (fun y : ℝ^n ↦ p.eval y)) x -
        (f i).eval x := by
  unfold eulerMomentumResidual Verified.Expr.closedGradient
  change
    Verified.Expr.eval (fun k : Fin n ↦ x k)
        (Verified.Expr.Alg.normalize
          (convectiveDerivative u i + Verified.Expr.closedPartial i p - f i)) =
      (∑ j : Fin n,
        (u j).eval x *
          (∂[j] (fun y : ℝ^n ↦ (u i).eval y)) x) +
        (∂[i] (fun y : ℝ^n ↦ p.eval y)) x -
        (f i).eval x
  rw [Verified.Expr.Alg.eval_normalize]
  change
    (convectiveDerivative u i).eval x +
        Verified.Expr.eval (fun k : Fin n ↦ x k) (Verified.Expr.closedPartial i p) -
        (f i).eval x =
      (∑ j : Fin n,
        (u j).eval x *
          (∂[j] (fun y : ℝ^n ↦ (u i).eval y)) x) +
        (∂[i] (fun y : ℝ^n ↦ p.eval y)) x -
        (f i).eval x
  rw [convectiveDerivative_eval_eq_sum_mul_partialDeriv
    (u := u) (x := x) (i := i) hu]
  rw [Verified.Expr.closedPartial_eval_eq_partialDeriv
    (expr := p) (x := x) (i := i) hp]

/-- A symbolic stationary Navier-Stokes momentum component evaluates to
`∑ⱼ uⱼ ∂ⱼuᵢ + ∂ᵢp - ν Δuᵢ - fᵢ`. -/
theorem navierStokesMomentumResidual_eval_eq_sum_mul_partialDeriv_add_partialDeriv_sub_lap_sub
    {n : Nat}
    (ν : Verified.Expr (Fin n)) (u : Fin n → Verified.Expr (Fin n)) (p : Verified.Expr (Fin n))
    (f : Fin n → Verified.Expr (Fin n)) (x : ℝ^n) (i : Fin n)
    (hu : (u i).ValidAt x) (hp : p.ValidAt x)
    (hdu : ∀ j : Fin n, ((u i).diff j).ValidAt x) :
    (navierStokesMomentumResidual ν u p f i).eval x =
      (∑ j : Fin n,
        (u j).eval x *
          (∂[j] (fun y : ℝ^n ↦ (u i).eval y)) x) +
        (∂[i] (fun y : ℝ^n ↦ p.eval y)) x -
        ν.eval x * laplacian
          (fun y : ℝ^n ↦ (u i).eval y) x -
        (f i).eval x := by
  unfold navierStokesMomentumResidual Verified.Expr.closedGradient
  change
    Verified.Expr.eval (fun k : Fin n ↦ x k)
        (Verified.Expr.Alg.normalize
          (convectiveDerivative u i + Verified.Expr.closedPartial i p -
            ν * vectorLaplacian u i - f i)) =
      (∑ j : Fin n,
        (u j).eval x *
          (∂[j] (fun y : ℝ^n ↦ (u i).eval y)) x) +
        (∂[i] (fun y : ℝ^n ↦ p.eval y)) x -
        ν.eval x * laplacian
          (fun y : ℝ^n ↦ (u i).eval y) x -
        (f i).eval x
  rw [Verified.Expr.Alg.eval_normalize]
  change
    (convectiveDerivative u i).eval x +
        Verified.Expr.eval (fun k : Fin n ↦ x k) (Verified.Expr.closedPartial i p) -
        (ν.eval x * (vectorLaplacian u i).eval x) -
        (f i).eval x =
      (∑ j : Fin n,
        (u j).eval x *
          (∂[j] (fun y : ℝ^n ↦ (u i).eval y)) x) +
        (∂[i] (fun y : ℝ^n ↦ p.eval y)) x -
        ν.eval x * laplacian
          (fun y : ℝ^n ↦ (u i).eval y) x -
        (f i).eval x
  rw [convectiveDerivative_eval_eq_sum_mul_partialDeriv
    (u := u) (x := x) (i := i) hu]
  rw [Verified.Expr.closedPartial_eval_eq_partialDeriv
    (expr := p) (x := x) (i := i) hp]
  rw [vectorLaplacian_eval_eq_laplacian
    (u := u) (x := x) (i := i) hu hdu]

/-- The symbolic transport residual evaluates to its analytic coordinate formula. -/
theorem transportResidualIntegrand_eval_eq_sum_mul_partialDeriv_sub {n : Nat}
    (b : Fin n → Verified.Expr (Fin n)) (u f : Verified.Expr (Fin n)) (x : ℝ^n)
    (hu : u.ValidAt x) :
    (transportResidualIntegrand b u f).eval x =
      (∑ i : Fin n,
        (b i).eval x *
          (∂[i] (fun y : ℝ^n ↦ u.eval y)) x) -
        f.eval x := by
  unfold transportResidualIntegrand
  change
    Verified.Expr.eval (fun k : Fin n ↦ x k)
        (Verified.Expr.Alg.normalize (advectionIntegrand b u - f)) =
      (∑ i : Fin n,
        (b i).eval x *
          (∂[i] (fun y : ℝ^n ↦ u.eval y)) x) -
        f.eval x
  rw [Verified.Expr.Alg.eval_normalize]
  change
    (advectionIntegrand b u).eval x - f.eval x =
      (∑ i : Fin n,
        (b i).eval x *
          (∂[i] (fun y : ℝ^n ↦ u.eval y)) x) -
        f.eval x
  rw [advectionIntegrand_eval_eq_sum_mul_partialDeriv (b := b) (u := u) (x := x) hu]

/-- The symbolic transport residual evaluates to analytic advection minus the source. -/
theorem transportResidualIntegrand_eval_eq_advectiveDerivative_sub {n : Nat}
    (b : Fin n → Verified.Expr (Fin n)) (u f : Verified.Expr (Fin n)) (x : ℝ^n)
    (hu : u.ValidAt x) :
    (transportResidualIntegrand b u f).eval x =
      advectiveDerivative
          (fun y : ℝ^n ↦ WithLp.toLp 2 (fun i : Fin n ↦ (b i).eval y))
          (fun y : ℝ^n ↦ u.eval y) x -
        f.eval x := by
  unfold transportResidualIntegrand
  rw [Verified.Expr.Alg.eval_normalize]
  change (advectionIntegrand b u).eval x - f.eval x = _
  rw [advectionIntegrand_eval_eq_advectiveDerivative b u x hu]

/-- The symbolic conservation-law residual evaluates to analytic coordinate divergence minus the
source. -/
theorem conservationResidualIntegrand_eval_eq_sum_partialDeriv_sub {n : Nat}
    (flux : Fin n → Verified.Expr (Fin n)) (f : Verified.Expr (Fin n)) (x : ℝ^n)
    (hflux : ∀ i : Fin n, (flux i).ValidAt x) :
    (conservationResidualIntegrand flux f).eval x =
      (∑ i : Fin n,
        (∂[i] (fun y : ℝ^n ↦ (flux i).eval y)) x) -
        f.eval x := by
  unfold conservationResidualIntegrand
  change
    Verified.Expr.eval (fun k : Fin n ↦ x k)
        (Verified.Expr.Alg.normalize (Verified.Expr.closedDivergence flux - f)) =
      (∑ i : Fin n,
        (∂[i] (fun y : ℝ^n ↦ (flux i).eval y)) x) -
        f.eval x
  rw [Verified.Expr.Alg.eval_normalize]
  change
    (Verified.Expr.closedDivergence flux).eval x - f.eval x =
      (∑ i : Fin n,
        (∂[i] (fun y : ℝ^n ↦ (flux i).eval y)) x) -
        f.eval x
  rw [Verified.Expr.closedDivergence_eval_eq_divergence
    (field := flux) (x := x) hflux]
  unfold divergence
  congr 1

end CAS
