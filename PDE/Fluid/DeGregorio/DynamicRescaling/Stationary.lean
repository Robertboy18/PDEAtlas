/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import CAS.ExactTactic

/-!
# Stationary transport residual and the analytic CLM profile

The stationary residual is `F(Ω) = (cω + U_x) Ω - (cl x + a U) Ω_x`.
Its exact perturbation expansion gives the linear and quadratic terms used in stability
analysis. At `b = 1/2`, the analytic profiles `Ω(x) = -x/(b²+x²)` and
`U(x) = arctan(x/b)` have residual `-a (U(x)-2x) Ω_x` when `cl = 1-2a`, `cω = -1`. For `a = 0`
this is the exact steady state (3.5) of Chen, Hou and Huang, who take it from Elgindi and Jeong.
The explicit derivatives and the residual algebra are proved with the `cas` tactic of SymLean.

These identities concern the transport residual only. The Biot–Savart relation
`U_x = HΩ` for the CLM pair is not used.

## References

* T. M. Elgindi and I.-J. Jeong, "On the effects of advection and vortex stretching",
  *Arch. Ration. Mech. Anal.* 235 (2020), no. 3, 1763-1817; arXiv:1701.04050.
  <https://doi.org/10.1007/s00205-019-01455-9>
  <https://arxiv.org/abs/1701.04050>
* J. Chen, T. Y. Hou, and D. Huang, "On the finite time blowup of the De Gregorio model for the 3D
  Euler equations", *Comm. Pure Appl. Math.* 74 (2021), no. 6, 1282-1350; numbering of
  arXiv:1905.06387v3, (1.4), p. 2, (2.2) and (2.3), p. 5, (3.5), p. 8, and (3.8)-(3.10), p. 9.
  <https://doi.org/10.1002/cpa.21991>
  <https://arxiv.org/abs/1905.06387v3>
-/

@[expose] public section

namespace DeGregorio

noncomputable section

/-- Right-hand side of the stationary rescaled transport equation. -/
def stationaryResidual (a spatialRate vorticityRate : ℝ) (ω u : ℝ → ℝ) (x : ℝ) : ℝ :=
  (vorticityRate + deriv u x) * ω x -
    (spatialRate * x + a * u x) * deriv ω x

/-- The terms linear in a profile perturbation and its two rate perturbations. -/
def linearizedTransport
    (a spatialRateBar vorticityRateBar spatialRate vorticityRate : ℝ)
    (ωBar uBar ω u : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(spatialRateBar * x + a * uBar x) * deriv ω x +
    (vorticityRateBar + deriv uBar x) * ω x +
      (vorticityRate + deriv u x) * ωBar x -
        (spatialRate * x + a * u x) * deriv ωBar x

/-- Exact stationary expansion into profile error, linear part, and quadratic remainder.
Derivatives of the sum are justified by spatial differentiability of all four fields. -/
theorem stationaryResidual_add
    (a spatialRateBar vorticityRateBar spatialRate vorticityRate : ℝ)
    (ωBar uBar ω u : ℝ → ℝ) (x : ℝ)
    (hωBar : DifferentiableAt ℝ ωBar x) (huBar : DifferentiableAt ℝ uBar x)
    (hω : DifferentiableAt ℝ ω x) (hu : DifferentiableAt ℝ u x) :
    stationaryResidual a (spatialRateBar + spatialRate) (vorticityRateBar + vorticityRate)
        (fun y ↦ ωBar y + ω y) (fun y ↦ uBar y + u y) x =
      stationaryResidual a spatialRateBar vorticityRateBar ωBar uBar x +
        linearizedTransport a spatialRateBar vorticityRateBar spatialRate vorticityRate
          ωBar uBar ω u x +
        stationaryResidual a spatialRate vorticityRate ω u x := by
  unfold stationaryResidual linearizedTransport
  rw [deriv_fun_add huBar hu, deriv_fun_add hωBar hω]
  cas

/-- Analytic vorticity profile of equation (3.5), with `b = 1/2`. -/
def clmVorticity (x : ℝ) : ℝ :=
  -x / ((1 / 4 : ℝ) + x ^ 2)

/-- Corresponding normalized velocity profile of equation (3.8). -/
def clmVelocity (x : ℝ) : ℝ :=
  Real.arctan (2 * x)

/-- The CLM vorticity profile is differentiable with its explicit rational derivative. -/
theorem hasDerivAt_clmVorticity (x : ℝ) :
    HasDerivAt clmVorticity
      ((x ^ 2 - (1 / 4 : ℝ)) / ((1 / 4 : ℝ) + x ^ 2) ^ 2) x := by
  cas

/-- The CLM velocity derivative is the rational function displayed in equation (3.5). -/
theorem hasDerivAt_clmVelocity (x : ℝ) :
    HasDerivAt clmVelocity ((1 / 2 : ℝ) / ((1 / 4 : ℝ) + x ^ 2)) x := by
  cas

/-- The approximate profile error in equation (3.10), valid for every `a`. -/
theorem stationaryResidual_clm (a x : ℝ) :
    stationaryResidual a (1 - 2 * a) (-1) clmVorticity clmVelocity x =
      -a * (clmVelocity x - 2 * x) * deriv clmVorticity x := by
  unfold stationaryResidual
  rw [(hasDerivAt_clmVorticity x).deriv, (hasDerivAt_clmVelocity x).deriv]
  unfold clmVorticity clmVelocity
  cas

/-- At `a = 0` the CLM profile has zero stationary transport residual. -/
theorem stationaryResidual_clm_zero (x : ℝ) :
    stationaryResidual 0 1 (-1) clmVorticity clmVelocity x = 0 := by
  simpa using stationaryResidual_clm 0 x

end

end DeGregorio
