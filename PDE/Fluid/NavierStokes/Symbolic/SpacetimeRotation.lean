/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.VorticityTransport
public import PDE.Fluid.NavierStokes.Symbolic.Operators
public import CAS.ExactTactic

/-!
# Symbolic spacetime solid rotation

The rigid rotation `u(t,x,y) = (-y, x)` with centripetal pressure `p = (x² + y²)/2` is a
stationary solution of the incompressible Euler equations. Each velocity component is linear and
hence harmonic, so the same pair also solves the unforced Navier-Stokes equations for any constant
viscosity. The profile is embedded in spacetime coordinates `(t, x, y)` so that it exercises
the generic spacetime divergence, Euler, and Navier-Stokes residual operators of
`Symbolic.Operators`, time derivative included. The residual identities are proved by the `cas`
tactic of SymLean, our computer algebra system for Lean.

The identities are pointwise. The velocity grows linearly in space, so its energy on the whole
plane is infinite.

## Main results

* `spacetimeSolidRotation_divergenceFreeAt`: incompressibility in the analytic
  `IncompressibleFlow.DivergenceFreeAt` form.
* `spacetimeSolidRotation_planarVorticity_eq_two`,
  `spacetimeSolidRotation_planarVorticityTransportResidual_eq_zero`: the scalar vorticity is the
  constant `2`, so its transport residual vanishes.
* `spacetimeSolidRotation_eulerMomentum_component`,
  `spacetimeSolidRotation_navierStokesMomentum_component`: the analytic Euler and unit-viscosity
  Navier-Stokes momentum equations, obtained from the CAS residual checks through the semantic
  bridge.
-/

@[expose] public section

open PDE (spatialGradient)

namespace NavierStokes.Symbolic

open CAS
open CAS.Certificate
open CAS.Euclid2

noncomputable section

/-! ## Spacetime form of solid rotation -/

/-- Spacetime solid rotation velocity `u(t,x,y)=(-y,x)`. -/
def spacetimeSolidRotationVelocity2 : Fin 2 → Verified.Expr (Fin 3) :=
  ![-CAS.Euclid3.z, CAS.Euclid3.y]

/-- Spacetime centripetal pressure `p(t,x,y)=(x²+y²)/2`. -/
def spacetimeSolidRotationPressure2 : Verified.Expr (Fin 3) :=
  ((CAS.Euclid3.y ^ 2 + CAS.Euclid3.z ^ 2 : Verified.Expr (Fin 3)) / 2)

/-- Zero forcing for the spacetime solid-rotation example. -/
def spacetimeSolidRotationForce2 : Fin 2 → Verified.Expr (Fin 3) :=
  0

/-- Unit viscosity as a spacetime expression. -/
def spacetimeUnitViscosity2 : Verified.Expr (Fin 3) :=
  1

/--
Normalized spacetime Euler momentum residual for solid rotation.

This includes the time derivative term `∂ₜu`; it closes because the profile is
stationary and the pressure gradient cancels `(u · ∇)u`.
-/
def spacetimeSolidRotationEulerMomentumResidual2 : Exact.VectorResidual 3 2 :=
  Exact.VectorResidual.ofDifference
    (spacetimeEulerMomentumResidual
      spacetimeSolidRotationVelocity2
      spacetimeSolidRotationPressure2
      spacetimeSolidRotationForce2)
    0

/-- Normalized spacetime Navier-Stokes momentum residual for solid rotation. -/
def spacetimeSolidRotationNavierStokesMomentumResidual2 : Exact.VectorResidual 3 2 :=
  Exact.VectorResidual.ofDifference
    (spacetimeNavierStokesMomentumResidual
      spacetimeUnitViscosity2
      spacetimeSolidRotationVelocity2
      spacetimeSolidRotationPressure2
      spacetimeSolidRotationForce2)
    0

/-- Zero-error approximation form of spacetime incompressibility for solid rotation. -/
theorem spacetimeSolidRotation_incompressible_zero_error :
    ApproxOn
      (fun q : ℝ^3 ↦ (spacetimeDivergence spacetimeSolidRotationVelocity2).eval q)
      (fun _q ↦ 0)
      Set.univ
      0 := by
  cas

/-- Residual-bound form of spacetime incompressibility for solid rotation. -/
theorem spacetimeSolidRotation_incompressible_residualBound :
    ResidualBound
      (fun q : ℝ^3 ↦ (spacetimeDivergence spacetimeSolidRotationVelocity2).eval q)
      Set.univ
      0 := by
  cas

/-- Equality-to-zero form of the spacetime solid-rotation divergence residual. -/
theorem spacetimeSolidRotation_divergence_eq_zero :
    Set.EqOn
      (fun q : ℝ^3 ↦ (spacetimeDivergence spacetimeSolidRotationVelocity2).eval q)
      (fun _q ↦ 0)
      Set.univ := by
  cas

/--
Analytic incompressibility theorem consumed by the ordinary Navier-Stokes
interface.

The residual zero statement is supplied by the CAS claim, while the final target
is `IncompressibleFlow.DivergenceFreeAt` from `PDE.Fluid.Incompressible.Operators`.
-/
theorem spacetimeSolidRotation_divergenceFreeAt (x : ℝ^3) :
    IncompressibleFlow.DivergenceFreeAt
      (fun y ↦ WithLp.toLp 2 fun i : Fin 2 ↦
        (spacetimeSolidRotationVelocity2 i).eval y) x := by
  apply divergenceFreeAt_of_spacetimeDivergence_eval_zero
  · intro i
    fin_cases i <;> symbolic_assumptions
  · have h := spacetimeSolidRotation_divergence_eq_zero (x := x) trivial
    exact h

/-- Exact symbolic scalar vorticity of the solid-rotation field. -/
theorem spacetimeSolidRotation_vorticity_eq_two :
    Set.EqOn
      (fun q : ℝ^3 ↦ (spacetimePlanarVorticity spacetimeSolidRotationVelocity2).eval q)
      (fun q : ℝ^3 ↦ (2 : Verified.Expr (Fin 3)).eval q)
      Set.univ := by
  cas

/-- Analytic scalar vorticity of spacetime solid rotation is identically two. -/
theorem spacetimeSolidRotation_planarVorticity_eq_two (x : ℝ^3) :
    IncompressibleFlow.spacetimePlanarVorticity
      (fun y ↦ WithLp.toLp 2 fun i : Fin 2 ↦
        (spacetimeSolidRotationVelocity2 i).eval y) x = 2 := by
  calc
    _ = (spacetimePlanarVorticity spacetimeSolidRotationVelocity2).eval x := by
      symm
      apply eval_spacetimePlanarVorticity_eq
      intro i
      fin_cases i <;> symbolic_assumptions
    _ = 2 := by
      have h := spacetimeSolidRotation_vorticity_eq_two (x := x) trivial
      simpa [Verified.Expr.eval] using h

/-- The constant vorticity of spacetime solid rotation has zero transport residual. -/
theorem spacetimeSolidRotation_planarVorticityTransportResidual_eq_zero
    (x : ℝ^3) :
    IncompressibleFlow.spacetimePlanarVorticityTransportResidual
      (fun y ↦ WithLp.toLp 2 fun i : Fin 2 ↦
        (spacetimeSolidRotationVelocity2 i).eval y) x = 0 := by
  apply
    IncompressibleFlow.spacetimePlanarVorticityTransportResidual_eq_zero_of_eq_const
      (omega := 2)
  intro y
  exact spacetimeSolidRotation_planarVorticity_eq_two y

/--
CEGA zero-error spacetime Euler residual for solid rotation.

Unlike the stationary two-coordinate check in `Symbolic.Stationary.Rotation`, this theorem checks
the full spacetime residual with coordinate `0` reserved for time.
-/
theorem spacetimeSolidRotation_euler_momentum_zero_error :
    ResidualBound
      spacetimeSolidRotationEulerMomentumResidual2.vectorFn
      Set.univ
      0 := by
  cas

/-- Equality-to-zero form of the spacetime Euler residual vector. -/
theorem spacetimeSolidRotation_euler_eq_zero :
    Set.EqOn
      spacetimeSolidRotationEulerMomentumResidual2.vectorFn
      (fun _ ↦ 0)
      Set.univ := by
  cas

/--
Analytic component Euler momentum equation for spacetime solid rotation.

CAS supplies the closed residual identity; the conclusion uses the ordinary
material derivative and pressure-gradient operators.
-/
theorem spacetimeSolidRotation_eulerMomentum_component
    (x : ℝ^3) (i : Fin 2) :
    (IncompressibleFlow.materialDerivative 2
        (fun y ↦ WithLp.toLp 2 fun j : Fin 2 ↦
          (spacetimeSolidRotationVelocity2 j).eval y)
        (fun y ↦ WithLp.toLp 2 fun j : Fin 2 ↦
          (spacetimeSolidRotationVelocity2 j).eval y)
        x +
      spatialGradient
        (fun y : ℝ^3 ↦ spacetimeSolidRotationPressure2.eval y) x) i =
      (WithLp.toLp 2
        (fun j : Fin 2 ↦ (spacetimeSolidRotationForce2 j).eval x)) i := by
  apply eulerMomentumComponent_eq_of_spacetimeResidual_eval_zero
  · fin_cases i <;> symbolic_assumptions
  · intro _j
    fin_cases i <;> symbolic_assumptions
  · symbolic_assumptions
  · have hvec := spacetimeSolidRotation_euler_eq_zero (x := x) trivial
    have hcomp := congrFun hvec i
    change spacetimeSolidRotationEulerMomentumResidual2.vectorFn x i = 0 at hcomp
    have hraw :
        (spacetimeEulerMomentumResidual
            spacetimeSolidRotationVelocity2
            spacetimeSolidRotationPressure2
            spacetimeSolidRotationForce2 i).eval x -
          (0 : Verified.Expr (Fin 3)).eval x = 0 := by
      simpa [spacetimeSolidRotationEulerMomentumResidual2,
        Exact.VectorResidual.ofDifference,
        Exact.VectorResidual.vectorFn, Verified.Expr.Alg.eval_normalize] using hcomp
    simpa [Verified.Expr.eval] using hraw

/-- The spatial Laplacian of each linear solid-rotation component vanishes. -/
private theorem spacetimeSolidRotation_vectorLaplacian_eval_zero
    (q : ℝ^3) (i : Fin 2) :
    (spacetimeVectorLaplacian spacetimeSolidRotationVelocity2 i).eval q = 0 := by
  fin_cases i <;>
    simp [spacetimeVectorLaplacian, spacetimeSolidRotationVelocity2,
      Verified.Expr.Alg.eval_normalize, Verified.Expr.closedPartial,
      Verified.Expr.eval_trigSimplify, Verified.Expr.diff,
      Verified.Expr.sum, List.finRange, Verified.Expr.SymVar.expr]
  all_goals
    simp [Verified.Expr.trigSimplify, Verified.Expr.trigPostTop,
      Verified.Expr.mkNeg, Verified.Expr.diff, Verified.Expr.eval]

/--
Each spacetime solid-rotation Navier-Stokes residual component evaluates to zero.

This is the componentwise form of the vector identity consumed by the CAS/CEGA layer.
-/
theorem spacetimeSolidRotationNavierStokesMomentumResidual2_eval_eq_zero
    (q : ℝ^3) (i : Fin 2) :
    (spacetimeSolidRotationNavierStokesMomentumResidual2 i).eval q = 0 := by
  have hvec := spacetimeSolidRotation_euler_eq_zero (x := q) trivial
  have hcomp := congrFun hvec i
  change spacetimeSolidRotationEulerMomentumResidual2.vectorFn q i = 0 at hcomp
  have heuler :
      (spacetimeEulerMomentumResidual
        spacetimeSolidRotationVelocity2
        spacetimeSolidRotationPressure2
        spacetimeSolidRotationForce2 i).eval q = 0 := by
    have hraw :
        (spacetimeEulerMomentumResidual
            spacetimeSolidRotationVelocity2
            spacetimeSolidRotationPressure2
            spacetimeSolidRotationForce2 i).eval q -
          (0 : Verified.Expr (Fin 3)).eval q = 0 := by
      simpa [spacetimeSolidRotationEulerMomentumResidual2,
        Exact.VectorResidual.ofDifference,
        Exact.VectorResidual.vectorFn, Verified.Expr.Alg.eval_normalize] using hcomp
    simpa [Verified.Expr.eval] using hraw
  have hlaplacian := spacetimeSolidRotation_vectorLaplacian_eval_zero q i
  unfold spacetimeSolidRotationNavierStokesMomentumResidual2
  unfold Exact.VectorResidual.ofDifference
  change
    (Verified.Expr.Alg.normalize
      (spacetimeNavierStokesMomentumResidual
        spacetimeUnitViscosity2
        spacetimeSolidRotationVelocity2
        spacetimeSolidRotationPressure2
        spacetimeSolidRotationForce2 i -
      (0 : Verified.Expr (Fin 3)))).eval q = 0
  conv_lhs => rw [Verified.Expr.Alg.eval_normalize]
  rw [Verified.Expr.eval_sub_operator]
  rw [show (0 : Verified.Expr (Fin 3)).eval q = 0 by
    simp [Verified.Expr.eval], sub_zero]
  unfold spacetimeNavierStokesMomentumResidual
  conv_lhs => rw [Verified.Expr.Alg.eval_normalize]
  unfold spacetimeEulerMomentumResidual at heuler
  rw [Verified.Expr.Alg.eval_normalize] at heuler
  change
    (spacetimeMaterialDerivative
          spacetimeSolidRotationVelocity2 spacetimeSolidRotationVelocity2 i).eval q +
        (spacetimePressureGradient spacetimeSolidRotationPressure2 i).eval q -
        spacetimeUnitViscosity2.eval q *
          (spacetimeVectorLaplacian spacetimeSolidRotationVelocity2 i).eval q -
        (spacetimeSolidRotationForce2 i).eval q = 0
  change
    (spacetimeMaterialDerivative
          spacetimeSolidRotationVelocity2 spacetimeSolidRotationVelocity2 i).eval q +
        (spacetimePressureGradient spacetimeSolidRotationPressure2 i).eval q -
        (spacetimeSolidRotationForce2 i).eval q = 0 at heuler
  rw [hlaplacian]
  simpa using heuler

/-- CEGA zero-error spacetime Navier-Stokes residual for solid rotation. -/
theorem spacetimeSolidRotation_navierStokes_momentum_zero_error :
    ResidualBound
      spacetimeSolidRotationNavierStokesMomentumResidual2.vectorFn
      Set.univ
      0 := by
  simpa [ResidualBound] using
    approxOn_of_eqOn (by
      intro q _hq
      funext i
      simpa [Exact.VectorResidual.vectorFn] using
        spacetimeSolidRotationNavierStokesMomentumResidual2_eval_eq_zero q i)

/-- Equality-to-zero form of the spacetime Navier-Stokes residual vector. -/
theorem spacetimeSolidRotation_navierStokes_eq_zero :
    Set.EqOn
      spacetimeSolidRotationNavierStokesMomentumResidual2.vectorFn
      (fun _ ↦ 0)
      Set.univ :=
  eqOn_of_approxOn_zero spacetimeSolidRotation_navierStokes_momentum_zero_error

/--
Analytic component momentum equation for spacetime solid rotation.

The zero residual is supplied by the CAS vector residual check; the conclusion is stated
with the ordinary `IncompressibleFlow.materialDerivative`,
`spatialGradient`, and
`viscousTerm` operators.
-/
theorem spacetimeSolidRotation_navierStokesMomentum_component
    (x : ℝ^3) (i : Fin 2) :
    (IncompressibleFlow.materialDerivative 2
        (fun y ↦ WithLp.toLp 2 fun j : Fin 2 ↦
          (spacetimeSolidRotationVelocity2 j).eval y)
        (fun y ↦ WithLp.toLp 2 fun j : Fin 2 ↦
          (spacetimeSolidRotationVelocity2 j).eval y)
        x +
      spatialGradient
        (fun y : ℝ^3 ↦ spacetimeSolidRotationPressure2.eval y) x) i =
      (NavierStokes.viscousTerm 2 (spacetimeUnitViscosity2.eval x)
        (fun y ↦ WithLp.toLp 2 fun j : Fin 2 ↦
          (spacetimeSolidRotationVelocity2 j).eval y)
        x +
      WithLp.toLp 2
        (fun j : Fin 2 ↦ (spacetimeSolidRotationForce2 j).eval x)) i := by
  apply navierStokesMomentumComponent_eq_of_spacetimeResidual_eval_zero
  · fin_cases i <;> symbolic_assumptions
  · intro _j
    fin_cases i <;> symbolic_assumptions
  · symbolic_assumptions
  · intro j
    fin_cases i <;> fin_cases j <;> symbolic_assumptions
  · have hvec := spacetimeSolidRotation_navierStokes_eq_zero (x := x) trivial
    have hcomp := congrFun hvec i
    change spacetimeSolidRotationNavierStokesMomentumResidual2.vectorFn x i = 0 at hcomp
    have hraw :
        (spacetimeNavierStokesMomentumResidual
            spacetimeUnitViscosity2
            spacetimeSolidRotationVelocity2
            spacetimeSolidRotationPressure2
            spacetimeSolidRotationForce2 i).eval x -
          (0 : Verified.Expr (Fin 3)).eval x = 0 := by
      simpa [spacetimeSolidRotationNavierStokesMomentumResidual2,
        Exact.VectorResidual.ofDifference,
        Exact.VectorResidual.vectorFn, Verified.Expr.Alg.eval_normalize] using hcomp
    simpa [Verified.Expr.eval] using hraw


end

end NavierStokes.Symbolic
