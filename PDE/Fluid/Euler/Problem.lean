/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.ClassicalSolutions
public import PDE.Fluid.Incompressible.Euler
public import PDE.Fluid.Incompressible.Pressure
public import PDE.Fluid.Incompressible.InitialData
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Euler initial-value problems and finite-time classical solutions

There are two finite-time interfaces for incompressible Euler on `ℝ^n`:

* `PointwiseResidualSolution` stores fields satisfying the displayed equations and initial value,
  but imposes no differentiability or integrability;
* `SmoothSolution` adds interior smoothness and a one-sided continuous initial trace.

The distinction matters because `partialDeriv` is totalized. A residual identity alone is not a
classical PDE solution unless the derivatives are supported by an analytic regularity hypothesis.
Weak solutions use an integral identity and are defined separately in
`PDE.Fluid.Euler.WeakSolutions`. A smooth solution is not automatically a weak one: on
`ℝ^n`, smoothness alone does not supply the spatial `L²` bounds, decay, or spacetime integrability
required by the weak interface.

The equations are the incompressible Euler equations of Majda and Bertozzi, Section 1.1, with a
forcing term, that is, equations (1)-(3) of Fefferman's problem description with `ν = 0`.

## References

* A. J. Majda and A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge Texts in Applied
  Mathematics 27, Cambridge University Press, 2001, Chapter 1, Section 1.1.
  <https://doi.org/10.1017/CBO9780511613203>
* C. L. Fefferman, "Existence and smoothness of the Navier–Stokes equation", official problem
  description of the Clay Mathematics Institute, equations (1)-(3), p. 1.
  <https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf>
-/

@[expose] public section

open PDE (spatialGradient)

namespace Euler

open EuclideanSpace

set_option linter.missingDocs true

/-- The forced incompressible Euler momentum equation at one spacetime point. -/
def MomentumEquationAt {n : ℕ} (data : IncompressibleFlow.InitialValueData n)
    (u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ) (x : ℝ^(n + 1)) : Prop :=
  IncompressibleFlow.materialDerivative n u u x +
    spatialGradient p x = data.forcing x

/-- A finite-time pointwise Euler residual solution on `(0,T) × ℝ^n` with prescribed initial
velocity.

This type imposes no differentiability, integrability, decay, or energy
condition. Its differential operators are totalized, so this is an algebraic residual layer rather
than a classical-solution interface. -/
abbrev PointwiseResidualSolution {n : ℕ}
    (data : IncompressibleFlow.InitialValueData n) :=
  IncompressibleFlow.FiniteTimeResidualSolution data.initialVelocity
    (MomentumEquationAt data)

/-- The Euler momentum residual vanishes at every point of the finite-time domain. -/
theorem PointwiseResidualSolution.momentumResidual_eq_zero
    {n : ℕ} {data : IncompressibleFlow.InitialValueData n}
    (sol : PointwiseResidualSolution data)
    {x : ℝ^(n + 1)} (hx : x ∈ IncompressibleFlow.finiteTimeDomain n sol.T) :
    IncompressibleFlow.eulerMomentumResidual n sol.u sol.p data.forcing x = 0 :=
  (IncompressibleFlow.eulerMomentumResidual_eq_zero_iff n sol.u sol.p data.forcing x).2
    (sol.momentum_at hx)

/-- An interior-smooth classical Euler solution on `[0,T) × ℝ^n`.

Velocity and pressure are ambient-smooth at every positive-time point. Relative continuity at the
initial surface makes the stored initial value a one-sided trace. Regularity at the terminal time
`T` is not required. -/
abbrev SmoothSolution {n : ℕ}
    (data : IncompressibleFlow.InitialValueData n) :=
  IncompressibleFlow.FiniteTimeClassicalSolution data.initialVelocity
    (MomentumEquationAt data)

/-- Every interior point of a smooth Euler solution satisfies the pressure
Poisson equation obtained by taking the spatial divergence of momentum. -/
theorem SmoothSolution.pressurePoissonResidual_eq_zero
    {n : ℕ} {data : IncompressibleFlow.InitialValueData n}
    (sol : SmoothSolution data)
    {x : ℝ^(n + 1)} (hx : x ∈ IncompressibleFlow.finiteTimeDomain n sol.T) :
    IncompressibleFlow.pressurePoissonResidual
      n sol.u sol.p data.forcing x = 0 := by
  apply IncompressibleFlow.pressurePoissonResidual_eq_zero_of_eventually_momentum_eq
    n sol.u sol.p data.forcing x
  · intro i
    exact ((contDiffAt_piLp (2 : ENNReal)).1
      ((sol.velocity_contDiffAt hx).of_le
        (WithTop.coe_le_coe.mpr le_top)) i)
  · exact (sol.pressure_contDiffAt hx).of_le
      (WithTop.coe_le_coe.mpr le_top)
  · exact IncompressibleFlow.FiniteTimeResidualSolution.eventually_incompressible_at
      sol.toFiniteTimeResidualSolution hx
  · simpa only [
      MomentumEquationAt,
      IncompressibleFlow.materialDerivative_eq_timeDerivative_add_convectiveDerivative] using
      (IncompressibleFlow.FiniteTimeResidualSolution.eventually_momentum_at
        sol.toFiniteTimeResidualSolution hx)

end Euler
