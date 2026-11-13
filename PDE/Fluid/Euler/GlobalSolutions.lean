/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Euler.Problem

/-!
# Global classical Euler solutions

Pointwise residual and smooth Euler solution interfaces on all nonnegative times.
`GlobalPointwiseResidualSolution` stores the equations without analytic regularity, while
`GlobalSmoothSolution` adds relative smoothness on the closed physical half-space. Here “global”
means that the equations hold at every time `t > 0`.

The equations are the incompressible Euler equations of Majda and Bertozzi, Section 1.1, with a
forcing term.

## References

* A. J. Majda and A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge Texts in Applied
  Mathematics 27, Cambridge University Press, 2001, Chapter 1, Section 1.1.
  <https://doi.org/10.1017/CBO9780511613203>
-/

@[expose] public section

namespace Euler

open EuclideanSpace

set_option linter.missingDocs true

/-- A global pointwise Euler residual solution on `(0,∞) × ℝ^n`, with prescribed data at time
zero.

No differentiability or integrability is included. The pointwise differential operators are
totalized, so use `GlobalSmoothSolution` when classical regularity is required. -/
abbrev GlobalPointwiseResidualSolution {n : ℕ}
    (data : IncompressibleFlow.InitialValueData n) :=
  IncompressibleFlow.GlobalResidualSolution data.initialVelocity
    (MomentumEquationAt data)

/-- The Euler momentum residual vanishes at every strictly positive time. -/
theorem GlobalPointwiseResidualSolution.momentumResidual_eq_zero
    {n : ℕ} {data : IncompressibleFlow.InitialValueData n}
    (sol : GlobalPointwiseResidualSolution data)
    {x : ℝ^(n + 1)} (hx : x ∈ PDE.Common.positiveTimeDomain) :
    IncompressibleFlow.eulerMomentumResidual n sol.u sol.p data.forcing x = 0 :=
  (IncompressibleFlow.eulerMomentumResidual_eq_zero_iff n sol.u sol.p data.forcing x).2
    (sol.momentum_at hx)

/-- A global classical Euler solution smooth relative to the closed physical half-space `t ≥ 0`.

Smoothness is relative to `[0, ∞) × ℝ^n`, so no extension to negative times is needed. -/
abbrev GlobalSmoothSolution {n : ℕ}
    (data : IncompressibleFlow.InitialValueData n) :=
  IncompressibleFlow.GlobalClassicalSolution data.initialVelocity
    (MomentumEquationAt data)

/-- Every strictly positive-time point of a global smooth Euler solution
satisfies the pressure Poisson equation. -/
theorem GlobalSmoothSolution.pressurePoissonResidual_eq_zero
    {n : ℕ} {data : IncompressibleFlow.InitialValueData n}
    (sol : GlobalSmoothSolution data)
    {x : ℝ^(n + 1)} (hx : x ∈ PDE.Common.positiveTimeDomain) :
    IncompressibleFlow.pressurePoissonResidual
      n sol.u sol.p data.forcing x = 0 := by
  change 0 < x 0 at hx
  let T := x 0 + 1
  have hT : 0 < T := by
    dsimp [T]
    linarith
  have hxT : x ∈ IncompressibleFlow.finiteTimeDomain n T := by
    exact ⟨hx, by simp [T]⟩
  exact SmoothSolution.pressurePoissonResidual_eq_zero
    (IncompressibleFlow.GlobalClassicalSolution.toFiniteTime sol T hT) hxT

end Euler
