/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.ClassicalSolutions
public import PDE.Fluid.Incompressible.ModelHierarchy
public import PDE.Fluid.Incompressible.Pressure
public import PDE.Fluid.Incompressible.InitialData
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Navier-Stokes problem data and finite-time classical interfaces

The data of an initial-value problem are kept separate from two finite-time
pointwise solution layers:

* `Problem` stores viscosity, forcing, and admissible initial velocity data.
* `PointwiseResidualSolution` stores candidate fields satisfying the displayed
  equations, without asserting analytic regularity.
* `SmoothSolution` adds positive-time smoothness and a one-sided continuous
  initial trace.

The momentum equation, incompressibility and the initial condition are equations (1)-(3) of
Fefferman's problem description, here on `(0,T) × ℝ^n` for every `n`. Fefferman takes `n = 2` or
`3` and smooth divergence-free data, and his condition (6) asks for smoothness up to `t = 0`;
`SmoothSolution` asks for it only at positive times. The pressure Poisson equation
`SmoothSolution.pressurePoissonResidual_eq_zero` comes from taking the divergence of the momentum
equation, as in Majda and Bertozzi, Chapter 1.

Distributional `WeakSolution` and energy-class `LerayHopfSolution` interfaces live
in separate modules because they use weak derivatives and integral identities,
not the pointwise residual equations. Global interfaces likewise use a separate
time domain instead of encoding infinity in a finite real horizon. A smooth solution
is not automatically a weak one: whole-space smoothness by itself does not imply the
`L²`, weak-gradient, decay, and spacetime-integrability assumptions stored by the weak
interface.

## References

* C. L. Fefferman, "Existence and smoothness of the Navier–Stokes equation", official problem
  description of the Clay Mathematics Institute, equations (1)-(3) and condition (6), p. 1.
  <https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf>
* A. J. Majda and A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge Texts in Applied
  Mathematics 27, Cambridge University Press, 2001, Chapter 1.
  <https://doi.org/10.1017/CBO9780511613203>
-/

@[expose] public section

open PDE (spatialGradient)

namespace NavierStokes

open EuclideanSpace IncompressibleFlow MeasureTheory Order
open scoped Topology

set_option linter.missingDocs true

/-- Data for a Navier-Stokes initial-value problem on `ℝ^n`.

The structure holds coefficients and prescribed data only. Distributional
incompressibility is part of the datum itself, so the classical, weak, and
Leray-Hopf interfaces all refer to the same admissible initial velocity without
applying a totalized classical derivative to arbitrary `L²` data. -/
structure Problem (n : ℕ) extends IncompressibleFlow.InitialValueData n where
  /-- Positive kinematic-viscosity coefficient. -/
  kinematicViscosity : Set.Ioi (0 : ℝ)

/-- The forced incompressible Navier–Stokes momentum equation at one spacetime point. -/
def MomentumEquationAt {n : ℕ} (nse : Problem n)
    (u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ) (x : ℝ^(n + 1)) : Prop :=
  IncompressibleFlow.materialDerivative n u u x +
      spatialGradient p x =
    viscousTerm n nse.kinematicViscosity u x + nse.forcing x

/-- Pointwise Navier-Stokes residual solution on `(0,T) × ℝ^n`, with a
prescribed value at `t = 0`.

This packages candidate velocity and pressure fields, a positive finite horizon,
the pointwise equations, and an exact initial value. It imposes no
differentiability, integrability, or energy condition. Since the differential
operators are totalized, use `SmoothSolution` when a theorem requires a
classical solution rather than only the displayed residual identities. -/
abbrev PointwiseResidualSolution {n : ℕ} (nse : Problem n) :=
  IncompressibleFlow.FiniteTimeResidualSolution nse.initialVelocity
    (MomentumEquationAt nse)

/-- The Navier–Stokes momentum residual vanishes at every point of the
finite-time domain. -/
theorem PointwiseResidualSolution.momentumResidual_eq_zero
    {n : ℕ} {nse : Problem n} (sol : PointwiseResidualSolution nse)
    {x : ℝ^(n + 1)} (hx : x ∈ IncompressibleFlow.finiteTimeDomain n sol.T) :
    IncompressibleFlow.navierStokesMomentumResidual
      n nse.kinematicViscosity sol.u sol.p nse.forcing x = 0 :=
  (IncompressibleFlow.navierStokesMomentumResidual_eq_zero_iff
    n nse.kinematicViscosity sol.u sol.p nse.forcing x).2
      (sol.momentum_at hx)

/-- A positive-time classical solution on `(0,T) × ℝ^n` with a continuous initial trace.

This extends a `PointwiseResidualSolution` by the regularity missing from the
residual layer. The velocity and pressure are ambient-smooth at every
positive-time point. Relative continuity of velocity at `t = 0` makes the stored
initial value a one-sided trace rather than an arbitrary value assigned
on a measure-zero slice. Neither a pressure trace nor smoothness up to `t = 0` is
required. -/
abbrev SmoothSolution {n : ℕ} (nse : Problem n) :=
  IncompressibleFlow.FiniteTimeClassicalSolution nse.initialVelocity
    (MomentumEquationAt nse)

/-- Every interior point of a smooth Navier–Stokes solution satisfies the
pressure Poisson equation. The viscous term contributes no source because
the spatial vector Laplacian has zero divergence under incompressibility. -/
theorem SmoothSolution.pressurePoissonResidual_eq_zero
    {n : ℕ} {nse : Problem n} (sol : SmoothSolution nse)
    {x : ℝ^(n + 1)} (hx : x ∈ IncompressibleFlow.finiteTimeDomain n sol.T) :
    IncompressibleFlow.pressurePoissonResidual
      n sol.u sol.p nse.forcing x = 0 := by
  have hu3 : ∀ i : Fin n, ContDiffAt ℝ 3 (fun y ↦ sol.u y i) x := by
    intro i
    exact ((contDiffAt_piLp (2 : ENNReal)).1
      ((sol.velocity_contDiffAt hx).of_le
        (WithTop.coe_le_coe.mpr le_top)) i)
  apply
    IncompressibleFlow.pressurePoissonResidual_eq_zero_of_eventually_momentum_eq_add
      n sol.u sol.p
        (viscousTerm n nse.kinematicViscosity sol.u)
        nse.forcing x
  · intro i
    exact (hu3 i).of_le (by norm_num)
  · exact (sol.pressure_contDiffAt hx).of_le
      (WithTop.coe_le_coe.mpr le_top)
  · intro i
    simpa only [viscousTerm_apply] using
      (IncompressibleFlow.spatialVectorLaplacian_component_differentiableAt
        n sol.u x hu3 i).const_mul nse.kinematicViscosity
  · rw [spatialDivergence_viscousTerm]
    have hLaplacianDivergence :=
      spatialDivergence_spatialVectorLaplacian_eq_zero_of_eventually_divergenceFreeAt
        n sol.u x hu3
        (IncompressibleFlow.FiniteTimeResidualSolution.eventually_incompressible_at
          sol.toFiniteTimeResidualSolution hx)
    rw [hLaplacianDivergence, mul_zero]
  · exact IncompressibleFlow.FiniteTimeResidualSolution.eventually_incompressible_at
      sol.toFiniteTimeResidualSolution hx
  · simpa only [
      MomentumEquationAt,
      IncompressibleFlow.materialDerivative_eq_timeDerivative_add_convectiveDerivative] using
      (IncompressibleFlow.FiniteTimeResidualSolution.eventually_momentum_at
        sol.toFiniteTimeResidualSolution hx)

/-- Under unit density, incompressibility on the classical positive-time domain removes the
gradient-of-divergence term when the dynamic and kinematic viscosities agree. -/
theorem SmoothSolution.newtonianCauchyStressDivergence_eq
    {n : ℕ} {nse : Problem n} (sol : SmoothSolution nse)
    {x : ℝ^(n + 1)} (hx : x ∈ IncompressibleFlow.finiteTimeDomain n sol.T) :
    IncompressibleFlow.newtonianCauchyStressDivergence
        n nse.kinematicViscosity sol.p sol.u x =
      -spatialGradient sol.p x +
        viscousTerm n nse.kinematicViscosity sol.u x := by
  rw [viscousTerm]
  apply newtonianCauchyStressDivergence_eq_of_eventually_divergenceFreeAt
  · exact (sol.pressure_contDiffAt hx).differentiableAt (by simp)
  · intro k
    exact ((contDiffAt_piLp (p := (2 : ENNReal))).1
      (sol.velocity_contDiffAt hx) k).of_le (WithTop.coe_le_coe.mpr le_top)
  · exact IncompressibleFlow.FiniteTimeResidualSolution.eventually_incompressible_at
      sol.toFiniteTimeResidualSolution hx

end NavierStokes
