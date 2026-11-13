/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.ExactTactic
public import PDE.Symbolic.PDEDerivatives
public import CAS.IntegrationTactic
public import PDE.Parabolic.Heat.MeanValue.Flux
public import PDE.Representations.SeparationOfVariables
/-!
# Symbolic derivatives in Euclidean coordinates and of library functions

The coordinate derivatives and Laplacians of `Derivatives.lean` on `ℝ^n`: radial Laplacians, the
Newtonian potential, which is harmonic away from its pole, and the multiple `x r` of the planar
distance in real-power form, whose Laplacian is `x / r`; then the derivative of a library
function, a separation-of-variables sine mode.
-/

@[expose] public section

namespace PDE.Examples.CASDerivatives

/-! ## Euclidean shapes -/

/-- A polar-Laplacian coordinate derivative from `PDE.FDeriv.Polar.Laplacian`. -/
example (p : ℝ^2) : (∂[0] (fun q : ℝ^2 ↦ q 0 * Real.cos (q 1))) p = Real.cos (p 1) := by
  cas

/-- Parameters and a nonvanishing coordinate. -/
example (p : ℝ^2) (hp : p 0 ≠ 0) :
    (∂[0] (fun q : ℝ^2 ↦ q 1 / q 0)) p = -p 1 / p 0 ^ 2 := by
  cas

/-- A mixed second partial derivative needs validity only at the point. -/
example (p : ℝ^2) :
    (∂[0] (fun q : ℝ^2 ↦ (∂[1] (fun r : ℝ^2 ↦ r 0 * r 1 ^ 2)) q)) p =
      2 * p 1 := by
  cas

/-- The coordinate Laplacian of a harmonic function. -/
example (p : ℝ^2) : laplacian (fun q : ℝ^2 ↦ Real.exp (q 0) * Real.sin (q 1)) p = 0 := by
  cas

/-- A rational numeral base with a symbolic exponent as a frozen parameter. The summand route
normalizes the parameter before the real-power pass sees it, so the base reaches the pass as
the literal `1/4`, which the pass splits into natural-base powers (`Real.div_rpow`). -/
example (p : ℕ) (x : ℝ^2) :
    laplacian (fun q : ℝ^2 ↦ ((1 : ℝ) / 4) ^ p * (q 0 ^ 2 + q 1 ^ 2)) x = 4 / 2 ^ (2 * p) := by
  cas

/-- A Fréchet derivative applied to a coordinate direction is a partial derivative. -/
example (p : ℝ^2) : fderiv ℝ (fun q : ℝ^2 ↦ q 0 * q 1) p (EuclideanSpace.single 0 1) = p 1 := by
  cas

/-- The Newtonian potential is harmonic away from the origin. The identification of the
computed Laplacian with `0` needs `(√u)² = u`, which the finisher takes from the positivity
hypothesis on the radicand. -/
example (p : ℝ^3) (hp : 0 < p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2) :
    laplacian (fun q : ℝ^3 ↦ 1 / Real.sqrt (q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2)) p = 0 := by
  cas

/-- A Laplacian stated in real-power form is folded for the checked normalizer summand by
summand: each second derivative is normalized on its own before the sum of the normal forms is
compared with the stated value, and the recorded conditions are compacted, so that the
positivity of the radicand discharges them. -/
example (p : ℝ^2) (x : ℝ) (hp : 0 < p 0 ^ 2 + p 1 ^ 2) :
    laplacian (fun q : ℝ^2 ↦ x * (q 0 ^ 2 + q 1 ^ 2) ^ (1 / 2 : ℝ)) p =
      x * (p 0 ^ 2 + p 1 ^ 2) ^ (-(1 / 2) : ℝ) := by
  cas

/-! ## Derivatives of library functions -/

open PDE.Representations HeatEquation

/-- The imported unit-interval sine mode is unfolded before differentiation. -/
example (n : ℕ) (x : ℝ) :
    deriv (intervalDirichletSineMode n) x =
      Real.cos ((n.succ : ℝ) * Real.pi * x) * ((n.succ : ℝ) * Real.pi) := by
  unfold intervalDirichletSineMode
  cas

end PDE.Examples.CASDerivatives
