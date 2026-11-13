/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

import CAS.ExactTactic

/-!
# A decaying Taylor–Green vortex

We check the planar viscous Taylor–Green vortex (Taylor and Green, 1937).

At unit viscosity, the factor `exp(-2t)` makes the time derivative cancel the
vector Laplacian. The pressure is written in an equivalent sine-square form
that exposes its cancellation with nonlinear convection.

The fields and pointwise residuals are real-valued Lean functions, and the `cas` tactic of the
computer algebra system SymLean checks the differentiation and the final cancellation. The profile
is `2π`-periodic in both variables, so its energy on the whole plane is infinite. The
three-dimensional Taylor–Green flow, which is not explicit, is a different problem.

## References

* G. I. Taylor and A. E. Green, "Mechanism of the production of small eddies from large ones",
  *Proceedings of the Royal Society of London. Series A* 158 (1937), no. 895, 499-521.
  <https://doi.org/10.1098/rspa.1937.0036>
-/

@[expose] public section

namespace PDE.Examples.Research.TaylorGreenVortex

noncomputable section

/-- Exponential viscous decay `exp(-2t)`. -/
def decay (t : ℝ) : ℝ :=
  Real.exp (-2 * t)

/-- Horizontal velocity of the planar Taylor–Green vortex. -/
def velocityX (t x y : ℝ) : ℝ :=
  decay t * Real.sin x * Real.cos y

/-- Vertical velocity of the planar Taylor–Green vortex. -/
def velocityY (t x y : ℝ) : ℝ :=
  -(decay t * Real.cos x * Real.sin y)

/--
Taylor–Green pressure up to a time-dependent additive constant.

This equals the usual double-angle pressure modulo a function of time, so its
spatial gradient is unchanged.
-/
def pressure (t x y : ℝ) : ℝ :=
  -(decay t ^ 2 * (Real.sin x ^ 2 + Real.sin y ^ 2) / 2)

/-- Pointwise incompressibility residual `u_x + v_y`. -/
def divergence (t x y : ℝ) : ℝ :=
  deriv (fun ξ : ℝ ↦ velocityX t ξ y) x +
    deriv (fun η : ℝ ↦ velocityY t x η) y

/-- Horizontal unit-viscosity Navier-Stokes momentum residual. -/
def momentumResidualX (t x y : ℝ) : ℝ :=
  deriv (fun τ : ℝ ↦ velocityX τ x y) t +
    velocityX t x y * deriv (fun ξ : ℝ ↦ velocityX t ξ y) x +
    velocityY t x y * deriv (fun η : ℝ ↦ velocityX t x η) y +
    deriv (fun ξ : ℝ ↦ pressure t ξ y) x -
    (deriv (fun ξ : ℝ ↦ deriv (fun r : ℝ ↦ velocityX t r y) ξ) x +
      deriv (fun η : ℝ ↦ deriv (fun r : ℝ ↦ velocityX t x r) η) y)

/-- Vertical unit-viscosity Navier-Stokes momentum residual. -/
def momentumResidualY (t x y : ℝ) : ℝ :=
  deriv (fun τ : ℝ ↦ velocityY τ x y) t +
    velocityX t x y * deriv (fun ξ : ℝ ↦ velocityY t ξ y) x +
    velocityY t x y * deriv (fun η : ℝ ↦ velocityY t x η) y +
    deriv (fun η : ℝ ↦ pressure t x η) y -
    (deriv (fun ξ : ℝ ↦ deriv (fun r : ℝ ↦ velocityY t r y) ξ) x +
      deriv (fun η : ℝ ↦ deriv (fun r : ℝ ↦ velocityY t x r) η) y)

/-- The horizontal velocity decays in time according to `∂t u = -2u`. -/
theorem velocityX_deriv_t (t x y : ℝ) :
    deriv (fun τ : ℝ ↦ velocityX τ x y) t =
      -2 * decay t * Real.sin x * Real.cos y := by
  simp only [velocityX, decay]
  cas

/-- The horizontal divergence term is `exp(-2t) cos(x) cos(y)`. -/
theorem velocityX_deriv_x (t x y : ℝ) :
    deriv (fun ξ : ℝ ↦ velocityX t ξ y) x =
      decay t * Real.cos x * Real.cos y := by
  simp only [velocityX, decay]
  cas

/-- The transverse shear of the horizontal velocity is `-exp(-2t) sin(x) sin(y)`. -/
theorem velocityX_deriv_y (t x y : ℝ) :
    deriv (fun η : ℝ ↦ velocityX t x η) y =
      -(decay t * Real.sin x * Real.sin y) := by
  simp only [velocityX, decay]
  cas

/-- The vertical velocity decays in time according to `∂t v = -2v`. -/
theorem velocityY_deriv_t (t x y : ℝ) :
    deriv (fun τ : ℝ ↦ velocityY τ x y) t =
      2 * decay t * Real.cos x * Real.sin y := by
  simp only [velocityY, decay]
  cas

/-- The streamwise shear of the vertical velocity is `exp(-2t) sin(x) sin(y)`. -/
theorem velocityY_deriv_x (t x y : ℝ) :
    deriv (fun ξ : ℝ ↦ velocityY t ξ y) x =
      decay t * Real.sin x * Real.sin y := by
  simp only [velocityY, decay]
  cas

/-- The vertical divergence term cancels the horizontal divergence term. -/
theorem velocityY_deriv_y (t x y : ℝ) :
    deriv (fun η : ℝ ↦ velocityY t x η) y =
      -(decay t * Real.cos x * Real.cos y) := by
  simp only [velocityY, decay]
  cas

/-- The horizontal velocity is an eigenfunction of `∂xx` with eigenvalue `-1`. -/
theorem velocityX_deriv_xx (t x y : ℝ) :
    deriv (fun ξ : ℝ ↦ deriv (fun r : ℝ ↦ velocityX t r y) ξ) x =
      -(decay t * Real.sin x * Real.cos y) := by
  simp only [velocityX, decay]
  cas

/-- The horizontal velocity is an eigenfunction of `∂yy` with eigenvalue `-1`. -/
theorem velocityX_deriv_yy (t x y : ℝ) :
    deriv (fun η : ℝ ↦ deriv (fun r : ℝ ↦ velocityX t x r) η) y =
      -(decay t * Real.sin x * Real.cos y) := by
  simp only [velocityX, decay]
  cas

/-- The vertical velocity is an eigenfunction of `∂xx` with eigenvalue `-1`. -/
theorem velocityY_deriv_xx (t x y : ℝ) :
    deriv (fun ξ : ℝ ↦ deriv (fun r : ℝ ↦ velocityY t r y) ξ) x =
      decay t * Real.cos x * Real.sin y := by
  simp only [velocityY, decay]
  cas

/-- The vertical velocity is an eigenfunction of `∂yy` with eigenvalue `-1`. -/
theorem velocityY_deriv_yy (t x y : ℝ) :
    deriv (fun η : ℝ ↦ deriv (fun r : ℝ ↦ velocityY t x r) η) y =
      decay t * Real.cos x * Real.sin y := by
  simp only [velocityY, decay]
  cas

/-- The horizontal pressure gradient is `-exp(-4t) sin(x) cos(x)`. -/
theorem pressure_deriv_x (t x y : ℝ) :
    deriv (fun ξ : ℝ ↦ pressure t ξ y) x =
      -(decay t ^ 2 * Real.sin x * Real.cos x) := by
  simp only [pressure, decay]
  cas

/-- The vertical pressure gradient is `-exp(-4t) sin(y) cos(y)`. -/
theorem pressure_deriv_y (t x y : ℝ) :
    deriv (fun η : ℝ ↦ pressure t x η) y =
      -(decay t ^ 2 * Real.sin y * Real.cos y) := by
  simp only [pressure, decay]
  cas

/-- The decaying Taylor–Green velocity is exactly divergence free. -/
theorem velocity_incompressible (t x y : ℝ) :
    divergence t x y = 0 := by
  unfold divergence
  rw [velocityX_deriv_x, velocityY_deriv_y]
  cas

/-- The horizontal unit-viscosity Navier-Stokes momentum residual vanishes. -/
theorem navierStokes_momentum_x_zero (t x y : ℝ) :
    momentumResidualX t x y = 0 := by
  unfold momentumResidualX
  rw [velocityX_deriv_t, velocityX_deriv_x, velocityX_deriv_y,
    pressure_deriv_x, velocityX_deriv_xx, velocityX_deriv_yy]
  simp only [velocityX, velocityY]
  cas

/-- The vertical unit-viscosity Navier-Stokes momentum residual vanishes. -/
theorem navierStokes_momentum_y_zero (t x y : ℝ) :
    momentumResidualY t x y = 0 := by
  unfold momentumResidualY
  rw [velocityY_deriv_t, velocityY_deriv_x, velocityY_deriv_y,
    pressure_deriv_y, velocityY_deriv_xx, velocityY_deriv_yy]
  simp only [velocityX, velocityY]
  cas

/-- The Taylor–Green profile solves both unit-viscosity momentum equations. -/
theorem navierStokes_momentum_zero (t x y : ℝ) :
    momentumResidualX t x y = 0 ∧ momentumResidualY t x y = 0 :=
  ⟨navierStokes_momentum_x_zero t x y,
    navierStokes_momentum_y_zero t x y⟩

end

end PDE.Examples.Research.TaylorGreenVortex
