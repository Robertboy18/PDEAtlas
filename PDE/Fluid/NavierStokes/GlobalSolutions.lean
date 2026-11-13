/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Problem
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Global Navier-Stokes solutions

Pointwise residual and smooth classical solution interfaces on all nonnegative
times. `GlobalPointwiseResidualSolution` has no finite
horizon and imposes only the pointwise equations plus the initial value.
`GlobalSmoothSolution` adds relative smoothness on the physical half-space.

Here “global” means that the equations hold at every time `t > 0`. Global solutions
restrict to the finite-time residual interface from `Problem`.

The smoothness of `GlobalSmoothSolution` is condition (6) of Fefferman's problem description,
`p, u ∈ C^∞(ℝ^n × [0,∞))`, for the equations (1)-(3). Fefferman's bounded-energy condition (7) is
not part of the interface. The pressure Poisson equation
`GlobalSmoothSolution.pressurePoissonResidual_eq_zero` is the one in Majda and Bertozzi, Chapter 1.

## References

* C. L. Fefferman, "Existence and smoothness of the Navier–Stokes equation", official problem
  description of the Clay Mathematics Institute, equations (1)-(3) and conditions (6) and (7), p. 1.
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

/-- A global-in-time pointwise Navier-Stokes residual solution on
`(0,∞) × ℝ^n`, together with the prescribed value at `t = 0`.

The time domain is `(0, ∞)` itself rather than a finite horizon. This layer carries no
regularity; `GlobalSmoothSolution` adds it. -/
abbrev GlobalPointwiseResidualSolution {n : ℕ} (nse : Problem n) :=
  IncompressibleFlow.GlobalResidualSolution nse.initialVelocity
    (MomentumEquationAt nse)

/-- The Navier–Stokes momentum residual vanishes at every strictly
positive-time point. -/
theorem GlobalPointwiseResidualSolution.momentumResidual_eq_zero
    {n : ℕ} {nse : Problem n} (sol : GlobalPointwiseResidualSolution nse)
    {x : ℝ^(n + 1)} (hx : x ∈ PDE.Common.positiveTimeDomain) :
    IncompressibleFlow.navierStokesMomentumResidual
      n nse.kinematicViscosity sol.u sol.p nse.forcing x = 0 :=
  (IncompressibleFlow.navierStokesMomentumResidual_eq_zero_iff
    n nse.kinematicViscosity sol.u sol.p nse.forcing x).2
      (sol.momentum_at hx)

/-- A global solution whose velocity and pressure are smooth relative to the physical domain
`t ≥ 0`.

Smoothness is `ContDiffOn` on `[0, ∞) × ℝ^n`, so at `t = 0` it is one-sided and no extension to
negative times is needed. Pressure is not normalized: as in the PDE, it is determined only up to
the gauges compatible with the chosen function class. -/
abbrev GlobalSmoothSolution {n : ℕ} (nse : Problem n) :=
  IncompressibleFlow.GlobalClassicalSolution nse.initialVelocity
    (MomentumEquationAt nse)

/-- Under unit density, incompressibility on the global classical domain removes the
gradient-of-divergence term when the dynamic and kinematic viscosities agree. -/
theorem GlobalSmoothSolution.newtonianCauchyStressDivergence_eq
    {n : ℕ} {nse : Problem n} (sol : GlobalSmoothSolution nse)
    {x : ℝ^(n + 1)} (hx : x ∈ PDE.Common.positiveTimeDomain) :
    IncompressibleFlow.newtonianCauchyStressDivergence
        n nse.kinematicViscosity sol.p sol.u x =
      -spatialGradient sol.p x +
        viscousTerm n nse.kinematicViscosity sol.u x := by
  rw [viscousTerm]
  apply newtonianCauchyStressDivergence_eq_of_eventually_divergenceFreeAt
  · exact (sol.pressure_contDiffOn.contDiffAt
      (IncompressibleFlow.globalDomain_mem_nhds hx)).differentiableAt (by simp)
  · intro k
    exact ((contDiffAt_piLp (p := (2 : ENNReal))).1
      (sol.velocity_contDiffOn.contDiffAt
        (IncompressibleFlow.globalDomain_mem_nhds hx)) k).of_le
          (WithTop.coe_le_coe.mpr le_top)
  · exact IncompressibleFlow.GlobalResidualSolution.eventually_incompressible_at
      sol.toGlobalResidualSolution hx

/-- Every strictly positive-time point of a global smooth Navier–Stokes
solution satisfies the pressure Poisson equation. -/
theorem GlobalSmoothSolution.pressurePoissonResidual_eq_zero
    {n : ℕ} {nse : Problem n} (sol : GlobalSmoothSolution nse)
    {x : ℝ^(n + 1)} (hx : x ∈ PDE.Common.positiveTimeDomain) :
    IncompressibleFlow.pressurePoissonResidual
      n sol.u sol.p nse.forcing x = 0 := by
  change 0 < x 0 at hx
  let T := x 0 + 1
  have hT : 0 < T := by
    dsimp [T]
    linarith
  have hxT : x ∈ IncompressibleFlow.finiteTimeDomain n T := by
    exact ⟨hx, by simp [T]⟩
  exact SmoothSolution.pressurePoissonResidual_eq_zero
    (IncompressibleFlow.GlobalClassicalSolution.toFiniteTime sol T hT) hxT

end NavierStokes
