/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Operators
public import PDE.Parabolic.Heat.Kernel.Basic
import PDE.FDeriv.SpaceTime
import PDE.Parabolic.Heat.Kernel.SpatialDerivatives
import PDE.Parabolic.Heat.Kernel.TimeDerivative

/-!
# The heat-kernel equation

The Euclidean heat kernel `Φ(x, t) = (4πt)^(-n/2) exp(-‖x‖² / (4t))` solves the heat equation
`Φₜ - ΔΦ = 0` on `ℝ^n × (0, ∞)` (Evans, PDE, §2.3.1, the fundamental solution). The time
derivative and the spatial Laplacian are computed separately in
`PDE.Parabolic.Heat.Kernel.TimeDerivative` and `PDE.Parabolic.Heat.Kernel.SpatialDerivatives`;
both equal `(‖x‖² / (4t²) - n / (2t)) Φ(x, t)`.

## Main results

* `fundamentalSolutionHeat_satisfies_equation`: for `t > 0`, the spacetime function
  `xt ↦ Φ(spatialPart xt, xt 0)` has time derivative equal to the spatial Laplacian of the
  slice `y ↦ Φ(y, t)` at `x`, so the heat residual vanishes.
* `partialDeriv_time_fundamentalSolutionHeat`: the closed form of that time derivative.

## Implementation notes

`fundamentalSolutionHeat` is zero-extended to `t ≤ 0`, so the spacetime function is not
smooth across `t = 0`. The statements are restricted to `t > 0`, where the Gaussian branch is
in force on a neighbourhood of `(t, x)` and `partialDeriv 0` is the classical time derivative.
The time derivative is taken as the coordinate-`0` partial derivative of the spacetime function
at the point `timeSpaceCons t x`, and is identified with the one-variable derivative of
`s ↦ Φ(x, s)` at `t` through `partialDeriv_timeSpaceCons_eq_deriv`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1, the fundamental solution and the remark before
  Theorem 1 that it solves the heat equation away from the origin.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian)

namespace HeatEquation

open scoped Pointwise
open PDE.Common

variable {n : ℕ}

/-! ## Positive-time heat equation -/

/-- The fundamental solution satisfies the heat equation for `t > 0`. -/
theorem fundamentalSolutionHeat_satisfies_equation
    (x : ℝ^n) (t : ℝ) (ht : 0 < t) :
    (∂[0]
        (fun (xt : ℝ^(n + 1)) ↦
          fundamentalSolutionHeat (n := n) (spatialPartCLM n xt) (xt 0)))
        (timeSpaceCons (n := n) t x) -
      laplacian (n := n) (fun y ↦ fundamentalSolutionHeat (n := n) y t) x = 0 := by
  have hdiff : DifferentiableAt ℝ
      (fun xt : ℝ^(n + 1) ↦ fundamentalSolutionHeat (spatialPartCLM n xt) (xt 0))
      (timeSpaceCons t x) := by
    have h := (hasFDerivAt_fundamentalSolutionHeat_timeSpace x t ht).differentiableAt
    have hp := ((timeCLM n).differentiableAt (x := timeSpaceCons t x)).prodMk
      (spatialPartCLM n).differentiableAt
    simpa using! h.comp (timeSpaceCons t x) hp
  rw [PDE.partialDeriv_timeSpaceCons_eq_deriv _ x t hdiff]
  simp only [spatialPartCLM_timeSpaceCons, timeSpaceCons_zero]
  rw [fundamentalSolutionHeat_deriv_t x t ht,
    laplacian_fundamentalSolutionHeat x t ht, sub_self]

/-- Time partial derivative of the spacetime heat kernel at `(t,x)` for `t > 0`. -/
theorem partialDeriv_time_fundamentalSolutionHeat
    (x : ℝ^n) (t : ℝ) (ht : 0 < t) :
    (∂[0]
        (fun (xt : ℝ^(n + 1)) ↦
          fundamentalSolutionHeat (n := n) (spatialPartCLM n xt) (xt 0)))
        (timeSpaceCons (n := n) t x) =
      (‖x‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) * fundamentalSolutionHeat (n := n) x t := by
  have hPDE := fundamentalSolutionHeat_satisfies_equation (n := n) x t ht
  have hEq :
      (∂[0]
          (fun xt : ℝ^(n + 1) ↦
            fundamentalSolutionHeat (n := n) (spatialPartCLM n xt) (xt 0)))
          (timeSpaceCons (n := n) t x) =
        laplacian (n := n)
          (fun y : ℝ^n ↦ fundamentalSolutionHeat (n := n) y t) x := by
    exact sub_eq_zero.mp (by simpa using hPDE)
  simpa [hEq] using (laplacian_fundamentalSolutionHeat (n := n) x t ht)

end HeatEquation
