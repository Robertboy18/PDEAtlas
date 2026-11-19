/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.Calculus.TensorOperators
public import CAS.Exact.VectorResidual

/-!
# Pointwise symbolic PDE residuals

Symbolic advection `advectionIntegrand` and convective derivative `convectiveDerivative`,
and the stationary residuals `transportResidualIntegrand`, `conservationResidualIntegrand`,
`eulerMomentumResidual`, and `navierStokesMomentumResidual`, as checked expressions. The
evaluation theorems in `PDE.Symbolic.Calculus.PointwiseResidualSemantics` identify them with
the analytic Euclidean formulas at each point; this module does not import the analytic
operators.

Every residual follows the convention `left-hand side - source`; hence a solution makes the
residual zero. The Euler and Navier–Stokes declarations encode only the momentum equation, not
the separate incompressibility constraint. The viscosity in the symbolic Navier–Stokes residual
is a scalar coefficient; positivity and constancy, when required by a particular PDE problem,
belong to that problem's hypotheses. `Exact.VectorResidual.eulerMomentumEq` and
`Exact.VectorResidual.navierStokesMomentumEq` turn the two momentum residuals into vector
residuals for the componentwise `cas` routes of `CAS.Exact.VectorResidual`.

The bridge theorems in `PointwiseResidualSemantics` require `Verified.Expr.ValidAt` precisely
for expressions they differentiate.
Undifferentiated coefficients and source terms are evaluated using the total semantics of
`Verified.Expr`, so their validity is not needed for these identities alone.
-/

@[expose] public section

namespace CAS

open scoped BigOperators

/-- Symbolic first-order advection integrand `b · ∇u`.

The velocity field `b` may depend on the spatial variables. -/
def advectionIntegrand {n : Nat} (b : Fin n → Verified.Expr (Fin n)) (u : Verified.Expr (Fin n)) :
    Verified.Expr (Fin n) :=
  dotProduct b (Verified.Expr.closedGradient u)

/-- Symbolic convective derivative `(u · ∇)u` of a vector field. -/
def convectiveDerivative {n : Nat} (u : Fin n → Verified.Expr (Fin n)) :
    Fin n → Verified.Expr (Fin n) :=
  fun i ↦ advectionIntegrand u (u i)

/-- Stationary incompressible Euler momentum residual `(u · ∇)u + ∇p - f`. -/
def eulerMomentumResidual {n : Nat}
    (u : Fin n → Verified.Expr (Fin n)) (p : Verified.Expr (Fin n))
    (f : Fin n → Verified.Expr (Fin n)) :
    Fin n → Verified.Expr (Fin n) :=
  fun i ↦
    Verified.Expr.Alg.normalize
      (convectiveDerivative u i + Verified.Expr.closedGradient p i - f i)

/-- Stationary incompressible Navier-Stokes momentum residual
`(u · ∇)u + ∇p - ν Δu - f`. -/
def navierStokesMomentumResidual {n : Nat}
    (ν : Verified.Expr (Fin n)) (u : Fin n → Verified.Expr (Fin n)) (p : Verified.Expr (Fin n))
    (f : Fin n → Verified.Expr (Fin n)) : Fin n → Verified.Expr (Fin n) :=
  fun i ↦
    Verified.Expr.Alg.normalize
      (convectiveDerivative u i + Verified.Expr.closedGradient p i -
        ν * vectorLaplacian u i - f i)

/-- Symbolic transport residual `b · ∇u - f`.

This is the stationary first-order residual, before any weak formulation or boundary
condition. -/
def transportResidualIntegrand {n : Nat}
    (b : Fin n → Verified.Expr (Fin n)) (u f : Verified.Expr (Fin n)) : Verified.Expr (Fin n) :=
  Verified.Expr.Alg.normalize (advectionIntegrand b u - f)

/-- Symbolic conservation-law residual `div F - f` for a flux field `F`. -/
def conservationResidualIntegrand {n : Nat}
    (flux : Fin n → Verified.Expr (Fin n)) (f : Verified.Expr (Fin n)) : Verified.Expr (Fin n) :=
  Verified.Expr.Alg.normalize (Verified.Expr.closedDivergence flux - f)

namespace Exact.VectorResidual

/-- Build a residual for a stationary Euler momentum identity
`(u · ∇)u + ∇p - f = expected`. -/
def eulerMomentumEq {n : Nat}
    (u : Fin n → Verified.Expr (Fin n)) (p : Verified.Expr (Fin n))
    (f expected : Fin n → Verified.Expr (Fin n)) :
    VectorResidual n n :=
  ofDifference (eulerMomentumResidual u p f) expected

/-- Build a residual for a stationary Navier-Stokes momentum identity
`(u · ∇)u + ∇p - ν Δu - f = expected`. -/
def navierStokesMomentumEq {n : Nat}
    (ν : Verified.Expr (Fin n)) (u : Fin n → Verified.Expr (Fin n)) (p : Verified.Expr (Fin n))
    (f expected : Fin n → Verified.Expr (Fin n)) : VectorResidual n n :=
  ofDifference (navierStokesMomentumResidual ν u p f) expected

end Exact.VectorResidual

end CAS
