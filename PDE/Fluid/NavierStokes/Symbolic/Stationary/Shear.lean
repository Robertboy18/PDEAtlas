/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Symbolic.Operators
public import CAS.ExactTactic
public import PDE.Symbolic.Calculus.PointwiseResidualSemantics

/-!
# A symbolic stationary shear flow

The flow `u(x,y) = (sin y, 0)` with zero pressure is a stationary solution of the two-dimensional
Navier-Stokes equations with unit viscosity and forcing `f = (sin y, 0)`. It is divergence free,
its convective acceleration vanishes because `u` is independent of `x` and has no `y` component,
and `Δ(sin y) = -sin y` balances the force. This sinusoidally forced shear is the Kolmogorov flow
of the hydrodynamic-stability literature. Both the incompressibility and the momentum identity are
stated as zero residual bounds, proved by the `cas` tactic of SymLean, our computer algebra system
for Lean, and then exposed in ordinary Euclidean derivative notation.

The whole-space profile is not an `L²` velocity field. The integral identities below hold
because the combined residual vanishes identically.

## Main results

* `shearVelocity2_incompressible`: `div u = 0`.
* `shearVelocity2_forced_navierStokes_momentum_zero`: the stationary residual
  `(u · ∇)u + ∇p - νΔu - f` vanishes; `shearNavierStokesResidualCert2` packages this as a
  zero-error residual certificate.
* `shearVelocity2_forced_navierStokes_momentum_eval_eq_euclidean_derivatives`: the symbolic
  residual read in Euclidean derivative notation.
* `shearVelocity2_forced_navierStokes_euclidean_component_integral_zero`: the pointwise residual
  integrates to zero on every domain, because it vanishes identically.
-/

@[expose] public section

open PDE (laplacian)

namespace NavierStokes.Symbolic

open CAS
open CAS.Certificate
open CAS.Euclid2

noncomputable section

/-! ## Stationary forced shear flow -/

/-- The two-dimensional stationary shear velocity `u(x,y) = (sin y, 0)`. -/
def shearVelocity2 : Fin 2 → Verified.Expr (Fin 2) :=
  ![(.sin y : Verified.Expr (Fin 2)), (0 : Verified.Expr (Fin 2))]

/-- Zero pressure for the stationary shear example. -/
def shearPressure2 : Verified.Expr (Fin 2) :=
  0

/--
Forcing for the stationary shear example.

Since `Delta(sin y) = -sin y`, the stationary residual
`(u . grad)u + grad p - Delta u - f` vanishes for `f=(sin y,0)`.
-/
def shearForce2 : Fin 2 → Verified.Expr (Fin 2) :=
  ![(.sin y : Verified.Expr (Fin 2)), (0 : Verified.Expr (Fin 2))]

/-- Normalized symbolic momentum residual for the stationary forced shear flow. -/
def shearNavierStokesMomentumResidual2 : Exact.VectorResidual 2 2 :=
  Exact.VectorResidual.navierStokesMomentumEq
    unitViscosity2
    shearVelocity2
    shearPressure2
    shearForce2
    0

/--
CAS theorem: the shear velocity is incompressible.

This is the closed-form identity `partial_x(sin y) + partial_y(0) = 0`.
-/
theorem shearVelocity2_incompressible :
    ResidualBound
      (fun q : ℝ^2 ↦ (Verified.Expr.closedDivergence shearVelocity2).eval q)
      Set.univ 0 := by
  cas

/--
CAS theorem: the forced shear flow has zero stationary Navier-Stokes momentum residual.

This is the pointwise vector identity
`(u . grad)u + grad p - nu Delta u - f = 0`.
-/
theorem shearVelocity2_forced_navierStokes_momentum_zero :
    ResidualBound shearNavierStokesMomentumResidual2.vectorFn
      Set.univ 0 := by
  cas

/--
Zero-error certificate for the forced shear momentum residual.

The exact CAS proves the underlying residual theorem. As a `ResidualCert` it can be
projected into later analytic goals, and its error budget enlarged when a downstream
estimate asks only for a coarser bound.
-/
def shearNavierStokesResidualCert2 :
    ResidualCert (ℝ^2) (Fin 2 → ℝ) Set.univ :=
  ResidualCert.ofResidualBound
    shearNavierStokesMomentumResidual2.vectorFn
    0
    shearVelocity2_forced_navierStokes_momentum_zero

/--
Euclidean stationary Navier-Stokes component formula for the forced shear residual.

This is the semantic bridge form: the CAS checks the closed symbolic residual, and
ordinary fluid proofs can read the residual as
`(u · ∇)uᵢ + ∂ᵢp - νΔuᵢ - fᵢ`.
-/
theorem shearVelocity2_forced_navierStokes_momentum_eval_eq_euclidean_derivatives
    (q : ℝ^2) (i : Fin 2) :
    (navierStokesMomentumResidual
      unitViscosity2 shearVelocity2 shearPressure2 shearForce2 i).eval q =
      (∑ j : Fin 2,
        (shearVelocity2 j).eval q *
          (∂[j]
            (fun y : ℝ^2 ↦ (shearVelocity2 i).eval y)) q) +
        (∂[i]
          (fun y : ℝ^2 ↦ shearPressure2.eval y)) q -
        unitViscosity2.eval q *
          laplacian
            (fun y : ℝ^2 ↦ (shearVelocity2 i).eval y) q -
        (shearForce2 i).eval q := by
  have : Fact (0 < 2) := ⟨by decide⟩
  exact
    navierStokesMomentumResidual_eval_eq_sum_mul_partialDeriv_add_partialDeriv_sub_lap_sub
      (ν := unitViscosity2) (u := shearVelocity2) (p := shearPressure2)
      (f := shearForce2) (x := q) (i := i)
      (by fin_cases i <;> symbolic_assumptions)
      (by symbolic_assumptions)
      (by intro j; fin_cases i <;> fin_cases j <;> symbolic_assumptions)

/-- Every component of the forced-shear momentum residual evaluates to zero. -/
theorem shearNavierStokesMomentumResidual2_eval_eq_zero
    (q : ℝ^2) (i : Fin 2) :
    (shearNavierStokesMomentumResidual2 i).eval q = 0 := by
  have hzero : shearNavierStokesMomentumResidual2.vectorFn q = 0 :=
    (eqOn_zero_of_residualBound_zero
      shearVelocity2_forced_navierStokes_momentum_zero) (Set.mem_univ q)
  exact congrFun hzero i

/--
Componentwise integral bridge for the forced shear Navier-Stokes residual.

Each component of the checked vector residual integrates to zero on any
domain.  This is the vector analogue of the scalar residual integral bridge used
for transport and weak elliptic residuals.
-/
theorem shearNavierStokesMomentumResidual2_integral_eq_zero
    (Ω : Set (ℝ^2)) (i : Fin 2) :
    (∫ x in Ω, Exact.exprFn (shearNavierStokesMomentumResidual2 i) x) = 0 := by
  simp [Exact.exprFn,
    shearNavierStokesMomentumResidual2_eval_eq_zero]

/--
The forced-shear symbolic component is the stationary Navier-Stokes momentum
residual itself. The vector residual stores the normalized residual minus the
expected zero component; this theorem removes that normalization.
-/
theorem shearNavierStokesMomentumResidual2_eval_eq_residual
    (q : ℝ^2) (i : Fin 2) :
    Exact.exprFn (shearNavierStokesMomentumResidual2 i) q =
      (navierStokesMomentumResidual
        unitViscosity2 shearVelocity2 shearPressure2 shearForce2 i).eval q := by
  fin_cases i <;>
    cas [shearNavierStokesMomentumResidual2,
      navierStokesMomentumResidual, shearVelocity2, shearPressure2, shearForce2,
      unitViscosity2]

/--
Symbolic residual integral bridge for the forced shear Navier-Stokes example:
each component of `(u · ∇)u + ∇p - νΔu - f` integrates to zero.
-/
theorem shearVelocity2_forced_navierStokes_symbolic_component_integral_zero
    (Ω : Set (ℝ^2)) (i : Fin 2) :
    (∫ x in Ω,
      (navierStokesMomentumResidual
        unitViscosity2 shearVelocity2 shearPressure2 shearForce2 i).eval x) = 0 := by
  calc
    (∫ x in Ω,
      (navierStokesMomentumResidual
        unitViscosity2 shearVelocity2 shearPressure2 shearForce2 i).eval x) =
        ∫ x in Ω, Exact.exprFn (shearNavierStokesMomentumResidual2 i) x := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          exact (shearNavierStokesMomentumResidual2_eval_eq_residual x i).symm
    _ = 0 := shearNavierStokesMomentumResidual2_integral_eq_zero Ω i

/--
Integral of the pointwise forced-shear Navier-Stokes residual in Euclidean notation.

The integrand is written entirely in ordinary derivative/Laplacian notation,
and vanishes identically, so the integral is zero for every domain `Ω`.
-/
theorem shearVelocity2_forced_navierStokes_euclidean_component_integral_zero
    (Ω : Set (ℝ^2)) (i : Fin 2) :
    (∫ x in Ω,
      ((∑ j : Fin 2,
        (shearVelocity2 j).eval x *
          (∂[j]
            (fun y : ℝ^2 ↦ (shearVelocity2 i).eval y)) x) +
        (∂[i]
          (fun y : ℝ^2 ↦ shearPressure2.eval y)) x -
        unitViscosity2.eval x *
          laplacian
            (fun y : ℝ^2 ↦ (shearVelocity2 i).eval y) x -
        (shearForce2 i).eval x)) = 0 := by
  calc
    (∫ x in Ω,
      ((∑ j : Fin 2,
        (shearVelocity2 j).eval x *
          (∂[j]
            (fun y : ℝ^2 ↦ (shearVelocity2 i).eval y)) x) +
        (∂[i]
          (fun y : ℝ^2 ↦ shearPressure2.eval y)) x -
        unitViscosity2.eval x *
          laplacian
            (fun y : ℝ^2 ↦ (shearVelocity2 i).eval y) x -
        (shearForce2 i).eval x)) =
        ∫ x in Ω,
          (navierStokesMomentumResidual
            unitViscosity2 shearVelocity2 shearPressure2 shearForce2 i).eval x := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          exact
            (shearVelocity2_forced_navierStokes_momentum_eval_eq_euclidean_derivatives
              x i).symm
    _ = 0 := shearVelocity2_forced_navierStokes_symbolic_component_integral_zero Ω i


end

end NavierStokes.Symbolic
