/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Symbolic.Operators
public import CAS.ExactTactic
public import PDE.Symbolic.Calculus.PointwiseResidualSemantics
public import CAS.ClosedForm.Expression.Rotation

/-!
# Symbolic stationary solid rotation

The rigid rotation `u(x,y) = (-y, x)` is divergence free, and its convective acceleration
`(u · ∇)u = (-x, -y)` is exactly cancelled by the gradient of the centripetal pressure
`p = (x² + y²)/2`. Since the components of `u` are linear, `Δu = 0`, so the same pair solves the
stationary unforced Navier-Stokes momentum equation for any constant viscosity. These identities,
together with the pressure Poisson equation `-Δp = div((u · ∇)u)`, are stated as zero residual
bounds, proved by the `cas` tactic of SymLean, our computer algebra system for Lean, and then
written in ordinary Euclidean derivative notation.

The velocity grows linearly in space, so its energy on the whole plane is infinite.

## Main results

* `rotationField2_incompressible`: `div u = 0`.
* `rotationField2_euler_momentum_zero`,
  `rotationField2_navierStokes_momentum_zero`: the stationary Euler and unit-viscosity
  Navier-Stokes residuals vanish.
* `rotationField2_pressure_poisson`: the pressure Poisson residual vanishes.
* `rotationField2_euler_momentum_eval_eq_euclidean_derivatives`,
  `rotationField2_navierStokes_momentum_eval_eq_euclidean_derivatives`: the symbolic
  residuals read as `(u · ∇)uᵢ + ∂ᵢp - fᵢ` and `(u · ∇)uᵢ + ∂ᵢp - νΔuᵢ - fᵢ`.
-/

@[expose] public section

open PDE (laplacian)

namespace NavierStokes.Symbolic

open CAS
open CAS.Certificate
open CAS.Euclid2

noncomputable section

/-! ## Stationary solid rotation with pressure cancellation -/

/-- Centripetal pressure for solid rotation, `p=(x²+y²)/2`. -/
def solidRotationPressure2 : Verified.Expr (Fin 2) :=
  ((x ^ 2 + y ^ 2 : Verified.Expr (Fin 2)) / 2)

/-- No external force for the solid rotation pressure-balance example. -/
def solidRotationForce2 : Fin 2 → Verified.Expr (Fin 2) :=
  0

/--
Normalized symbolic residual for the solid-rotation Euler momentum equation
`(u · ∇)u + ∇((x²+y²)/2) = 0`.
-/
def solidRotationEulerMomentumResidual2 : Exact.VectorResidual 2 2 :=
  Exact.VectorResidual.eulerMomentumEq
    rotationField2
    solidRotationPressure2
    solidRotationForce2
    0

/--
Normalized symbolic Navier-Stokes momentum residual for the same profile.

The vector Laplacian of the linear rotation field is zero, so the Euler
pressure-balance identity also solves the stationary unforced Navier-Stokes
momentum residual for any constant viscosity.  The residual uses unit viscosity.
-/
def solidRotationNavierStokesMomentumResidual2 : Exact.VectorResidual 2 2 :=
  Exact.VectorResidual.navierStokesMomentumEq
    unitViscosity2
    rotationField2
    solidRotationPressure2
    solidRotationForce2
    0

/-- Residual of the pressure Poisson equation `-Δp = div((u · ∇)u)`. -/
def solidRotationPressurePoissonResidual2 : Verified.Expr (Fin 2) :=
    (-(Verified.Expr.closedLaplacian solidRotationPressure2))
      - Verified.Expr.closedDivergence
        (CAS.convectiveDerivative rotationField2)

/-- CAS theorem: solid rotation is incompressible. -/
theorem rotationField2_incompressible :
    ResidualBound
      (fun q : ℝ^2 ↦ (Verified.Expr.closedDivergence rotationField2).eval q)
      Set.univ 0 := by
  cas

/--
CAS theorem: pressure cancels the solid-rotation convective acceleration in
the stationary Euler momentum residual.
-/
theorem rotationField2_euler_momentum_zero :
    ResidualBound solidRotationEulerMomentumResidual2.vectorFn
      Set.univ 0 := by
  cas

/-- CAS theorem: solid rotation satisfies its pressure Poisson equation. -/
theorem rotationField2_pressure_poisson :
    ResidualBound (fun q : ℝ^2 ↦ solidRotationPressurePoissonResidual2.eval q)
      Set.univ 0 := by
  cas

/--
Euclidean stationary Euler component formula for solid rotation.

The CAS residual check proves the closed residual; this theorem exposes the same
component as `(u · ∇)uᵢ + ∂ᵢp - fᵢ`.
-/
theorem rotationField2_euler_momentum_eval_eq_euclidean_derivatives
    (q : ℝ^2) (i : Fin 2) :
    (eulerMomentumResidual
      rotationField2 solidRotationPressure2 solidRotationForce2 i).eval q =
      (∑ j : Fin 2,
        (rotationField2 j).eval q *
          (∂[j]
            (fun y : ℝ^2 ↦ (rotationField2 i).eval y)) q) +
        (∂[i]
          (fun y : ℝ^2 ↦ solidRotationPressure2.eval y)) q -
        (solidRotationForce2 i).eval q := by
  have : Fact (0 < 2) := ⟨by decide⟩
  exact
    eulerMomentumResidual_eval_eq_sum_mul_partialDeriv_add_partialDeriv_sub
      (u := rotationField2) (p := solidRotationPressure2)
      (f := solidRotationForce2) (x := q) (i := i)
      (by fin_cases i <;> symbolic_assumptions)
      (by symbolic_assumptions)

/--
CAS theorem: the same pressure-balanced rotation has zero stationary
Navier-Stokes momentum residual for unit viscosity.
-/
theorem rotationField2_navierStokes_momentum_zero :
    ResidualBound solidRotationNavierStokesMomentumResidual2.vectorFn
      Set.univ 0 := by
  cas

/-- Euclidean stationary Navier-Stokes component formula for solid rotation. -/
theorem rotationField2_navierStokes_momentum_eval_eq_euclidean_derivatives
    (q : ℝ^2) (i : Fin 2) :
    (navierStokesMomentumResidual
      unitViscosity2 rotationField2 solidRotationPressure2 solidRotationForce2 i).eval q =
      (∑ j : Fin 2,
        (rotationField2 j).eval q *
          (∂[j]
            (fun y : ℝ^2 ↦ (rotationField2 i).eval y)) q) +
        (∂[i]
          (fun y : ℝ^2 ↦ solidRotationPressure2.eval y)) q -
        unitViscosity2.eval q *
          laplacian
            (fun y : ℝ^2 ↦ (rotationField2 i).eval y) q -
        (solidRotationForce2 i).eval q := by
  have : Fact (0 < 2) := ⟨by decide⟩
  exact
    navierStokesMomentumResidual_eval_eq_sum_mul_partialDeriv_add_partialDeriv_sub_lap_sub
      (ν := unitViscosity2) (u := rotationField2) (p := solidRotationPressure2)
      (f := solidRotationForce2) (x := q) (i := i)
      (by fin_cases i <;> symbolic_assumptions)
      (by symbolic_assumptions)
      (by intro j; fin_cases i <;> fin_cases j <;> symbolic_assumptions)

/-- Every component of the solid-rotation Euler residual evaluates to zero. -/
theorem solidRotationEulerMomentumResidual2_eval_eq_zero
    (q : ℝ^2) (i : Fin 2) :
    (solidRotationEulerMomentumResidual2 i).eval q = 0 := by
  have hzero : solidRotationEulerMomentumResidual2.vectorFn q = 0 :=
    (eqOn_zero_of_residualBound_zero
      rotationField2_euler_momentum_zero) (Set.mem_univ q)
  exact congrFun hzero i

/-- Every component of the solid-rotation Navier-Stokes residual evaluates to zero. -/
theorem solidRotationNavierStokesMomentumResidual2_eval_eq_zero
    (q : ℝ^2) (i : Fin 2) :
    (solidRotationNavierStokesMomentumResidual2 i).eval q = 0 := by
  have hzero : solidRotationNavierStokesMomentumResidual2.vectorFn q = 0 :=
    (eqOn_zero_of_residualBound_zero
      rotationField2_navierStokes_momentum_zero) (Set.mem_univ q)
  exact congrFun hzero i


end

end NavierStokes.Symbolic
