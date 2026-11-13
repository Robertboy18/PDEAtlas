/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

import CAS.ExactTactic

/-!
# Kovasznay's exact stationary Navier-Stokes flow

We check a rationally scaled form of the exact wake of:

L. I. G. Kovasznay, *Laminar Flow Behind a Two-Dimensional Grid*,
Proceedings of the Cambridge Philosophical Society 44 (1948), 58-62.

The usual parameters satisfy `nu * (lambda^2 - k^2) = lambda`. Choosing
`lambda = -1`, `k = 2`, and `nu = 1/3` removes square roots and pi while
preserving the exponential-trigonometric pressure balance.

The fields and pointwise residuals are real-valued Lean functions, and the
computer algebra system checks the differentiation and the final cancellation.
The identities hold on the whole plane. The energy is infinite there: the velocity
tends to a nonzero constant downstream and grows exponentially upstream.
-/

@[expose] public section

namespace PDE.Examples.Research.KovasznayFlow

noncomputable section

/-- Exponential wake profile `exp(-x)`. -/
def decay (x : ℝ) : ℝ :=
  Real.exp (-x)

/-- Horizontal velocity of the scaled Kovasznay wake. -/
def velocityX (x y : ℝ) : ℝ :=
  1 - decay x * Real.cos (2 * y)

/-- Vertical velocity of the scaled Kovasznay wake. -/
def velocityY (x y : ℝ) : ℝ :=
  -(decay x * Real.sin (2 * y) / 2)

/-- Kovasznay pressure, up to an irrelevant additive constant. -/
def pressure (x _y : ℝ) : ℝ :=
  -(decay x ^ 2 / 2)

/-- Kinematic viscosity for the scaled flow. -/
def viscosity : ℝ :=
  1 / 3

/-- Pointwise incompressibility residual `u_x + v_y`. -/
def divergence (x y : ℝ) : ℝ :=
  deriv (fun ξ : ℝ ↦ velocityX ξ y) x +
    deriv (fun η : ℝ ↦ velocityY x η) y

/-- Horizontal stationary Navier-Stokes momentum residual. -/
def momentumResidualX (x y : ℝ) : ℝ :=
  velocityX x y * deriv (fun ξ : ℝ ↦ velocityX ξ y) x +
    velocityY x y * deriv (fun η : ℝ ↦ velocityX x η) y +
    deriv (fun ξ : ℝ ↦ pressure ξ y) x -
    viscosity *
      (deriv (fun ξ : ℝ ↦ deriv (fun r : ℝ ↦ velocityX r y) ξ) x +
        deriv (fun η : ℝ ↦ deriv (fun r : ℝ ↦ velocityX x r) η) y)

/-- Vertical stationary Navier-Stokes momentum residual. -/
def momentumResidualY (x y : ℝ) : ℝ :=
  velocityX x y * deriv (fun ξ : ℝ ↦ velocityY ξ y) x +
    velocityY x y * deriv (fun η : ℝ ↦ velocityY x η) y +
    deriv (fun η : ℝ ↦ pressure x η) y -
    viscosity *
      (deriv (fun ξ : ℝ ↦ deriv (fun r : ℝ ↦ velocityY r y) ξ) x +
        deriv (fun η : ℝ ↦ deriv (fun r : ℝ ↦ velocityY x r) η) y)

/-- The streamwise derivative of the horizontal velocity is `exp(-x) cos(2y)`. -/
theorem velocityX_deriv_x (x y : ℝ) :
    deriv (fun ξ : ℝ ↦ velocityX ξ y) x =
      decay x * Real.cos (2 * y) := by
  simp only [velocityX, decay]
  cas

/-- The transverse shear of the horizontal velocity is `2 exp(-x) sin(2y)`. -/
theorem velocityX_deriv_y (x y : ℝ) :
    deriv (fun η : ℝ ↦ velocityX x η) y =
      2 * decay x * Real.sin (2 * y) := by
  simp only [velocityX, decay]
  cas

/-- The streamwise derivative of the vertical velocity is its negative. -/
theorem velocityY_deriv_x (x y : ℝ) :
    deriv (fun ξ : ℝ ↦ velocityY ξ y) x =
      decay x * Real.sin (2 * y) / 2 := by
  simp only [velocityY, decay]
  cas

/-- The transverse derivative of the vertical velocity cancels the horizontal divergence term. -/
theorem velocityY_deriv_y (x y : ℝ) :
    deriv (fun η : ℝ ↦ velocityY x η) y =
      -(decay x * Real.cos (2 * y)) := by
  simp only [velocityY, decay]
  cas

/-- The second streamwise derivative is the horizontal perturbation `u - 1`. -/
theorem velocityX_deriv_xx (x y : ℝ) :
    deriv (fun ξ : ℝ ↦ deriv (fun r : ℝ ↦ velocityX r y) ξ) x =
      -(decay x * Real.cos (2 * y)) := by
  simp only [velocityX, decay]
  cas

/-- The second transverse derivative is `-4(u - 1)`, reflecting the wave number `2`. -/
theorem velocityX_deriv_yy (x y : ℝ) :
    deriv (fun η : ℝ ↦ deriv (fun r : ℝ ↦ velocityX x r) η) y =
      4 * decay x * Real.cos (2 * y) := by
  simp only [velocityX, decay]
  cas

/-- The second streamwise derivative of the vertical velocity equals the velocity itself. -/
theorem velocityY_deriv_xx (x y : ℝ) :
    deriv (fun ξ : ℝ ↦ deriv (fun r : ℝ ↦ velocityY r y) ξ) x =
      -(decay x * Real.sin (2 * y) / 2) := by
  simp only [velocityY, decay]
  cas

/-- The second transverse derivative of the vertical velocity is `-4v`. -/
theorem velocityY_deriv_yy (x y : ℝ) :
    deriv (fun η : ℝ ↦ deriv (fun r : ℝ ↦ velocityY x r) η) y =
      2 * decay x * Real.sin (2 * y) := by
  simp only [velocityY, decay]
  cas

/-- The streamwise pressure gradient is `exp(-2x)`. -/
theorem pressure_deriv_x (x y : ℝ) :
    deriv (fun ξ : ℝ ↦ pressure ξ y) x = decay x ^ 2 := by
  simp only [pressure, decay]
  cas

/-- The pressure has no transverse variation. -/
theorem pressure_deriv_y (x y : ℝ) :
    deriv (fun η : ℝ ↦ pressure x η) y = 0 := by
  simp only [pressure]
  cas

/-- The scaled Kovasznay velocity is exactly divergence free. -/
theorem velocity_incompressible (x y : ℝ) :
    divergence x y = 0 := by
  unfold divergence
  rw [velocityX_deriv_x, velocityY_deriv_y]
  cas

/-- The horizontal stationary Navier-Stokes momentum residual vanishes. -/
theorem navierStokes_momentum_x_zero (x y : ℝ) :
    momentumResidualX x y = 0 := by
  unfold momentumResidualX
  rw [velocityX_deriv_x, velocityX_deriv_y, pressure_deriv_x,
    velocityX_deriv_xx, velocityX_deriv_yy]
  simp only [viscosity, velocityX, velocityY]
  cas

/-- The vertical stationary Navier-Stokes momentum residual vanishes. -/
theorem navierStokes_momentum_y_zero (x y : ℝ) :
    momentumResidualY x y = 0 := by
  unfold momentumResidualY
  rw [velocityY_deriv_x, velocityY_deriv_y, pressure_deriv_y,
    velocityY_deriv_xx, velocityY_deriv_yy]
  simp only [viscosity, velocityX, velocityY]
  cas

/-- The scaled Kovasznay profile solves both stationary momentum equations. -/
theorem navierStokes_momentum_zero (x y : ℝ) :
    momentumResidualX x y = 0 ∧ momentumResidualY x y = 0 :=
  ⟨navierStokes_momentum_x_zero x y, navierStokes_momentum_y_zero x y⟩

end

end PDE.Examples.Research.KovasznayFlow
