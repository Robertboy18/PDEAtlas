/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Representations.SeparationOfVariables
import CAS.ExactTactic

/-!
# Separated modes for the one-dimensional heat equation

Each unit-interval Dirichlet sine mode `sin((n+1)πx)` pairs with the time factor
`exp(-((n+1)π)² t)`. Their product `intervalHeatMode n` is `C²`, solves the heat equation at every
point of `ℝ²`, vanishes at `x = 0` and `x = 1`, and has the sine mode as initial value
(`intervalHeatMode_satisfies_heat_dirichlet_ivp`). The product calculation for a general eigenpair
is `separated_heat_residual_zero`. SymLean's `cas` tactic checks the derivative of the time factor
(`intervalHeatTimeMode_deriv`).

This is Evans's §4.1.1, Example 1, on `U = (0, 1)`: the solution (6) for the eigenvalue
`λ = ((n+1)π)²` with eigenfunction `w(x) = sin((n+1)πx)` and `d = 1`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.1.1, Example 1, (1)-(7), pp. 168-169.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HeatEquation

open PDE.Representations

section

/-- The heat-equation time factor attached to the `n`th Dirichlet sine mode. -/
noncomputable def intervalHeatTimeMode (n : ℕ) : ℝ → ℝ :=
  fun t ↦ Real.exp (-(intervalDirichletEigenvalue n) * t)

/-- The separated heat solution built from the `n`th unit-interval Dirichlet mode. -/
noncomputable def intervalHeatMode (n : ℕ) (t x : ℝ) : ℝ :=
  intervalDirichletSineMode n x * intervalHeatTimeMode n t

/-- The heat time mode satisfies `T' = -λT`. -/
theorem intervalHeatTimeMode_deriv (n : ℕ) (t : ℝ) :
    deriv (intervalHeatTimeMode n) t =
      -intervalDirichletEigenvalue n * intervalHeatTimeMode n t := by
  cas

/-- Separation-of-variables product calculation for the one-dimensional heat equation.

If `X'' = -λX` and `T' = -λT`, then `u(t,x) = X(x)T(t)` has zero heat residual
`u_t - u_xx`, with derivatives taken as `deriv`. No differentiability is assumed; the
regularity of the sine modes is part of `intervalHeatMode_satisfies_heat_dirichlet_ivp`.
This is the computation of Evans's §4.1.1, Example 1, that leads from (2) to (3)-(5), used
in the converse direction with `μ = -λ`. -/
theorem separated_heat_residual_zero {lam : ℝ} {X T : ℝ → ℝ}
    (hX : ∀ x : ℝ, deriv (deriv X) x = -lam * X x)
    (hT : ∀ t : ℝ, deriv T t = -lam * T t)
    (t x : ℝ) :
    deriv (fun s : ℝ ↦ X x * T s) t -
        deriv (deriv (fun y : ℝ ↦ X y * T t)) x = 0 := by
  have htime : deriv (fun s : ℝ ↦ X x * T s) t = X x * deriv T t := by
    exact deriv_const_mul_field (X x)
  have hspace1 : deriv (fun y : ℝ ↦ X y * T t) = fun y : ℝ ↦ deriv X y * T t := by
    exact deriv_mul_const_field' (T t)
  have hspace2 :
      deriv (deriv (fun y : ℝ ↦ X y * T t)) x = deriv (deriv X) x * T t := by
    calc
      deriv (deriv (fun y : ℝ ↦ X y * T t)) x =
          deriv (fun y : ℝ ↦ deriv X y * T t) x := by
        simp [hspace1]
      _ = deriv (deriv X) x * T t := deriv_mul_const_field (T t)
  rw [htime, hspace2, hT t, hX x]
  ring

/-- The product `sin((n+1)πx) exp(-((n+1)π)^2 t)` has zero heat residual. -/
theorem intervalHeatMode_residual_zero (n : ℕ) (t x : ℝ) :
    deriv (fun s : ℝ ↦ intervalHeatMode n s x) t -
        deriv (deriv (fun y : ℝ ↦ intervalHeatMode n t y)) x = 0 := by
  exact separated_heat_residual_zero
    (lam := intervalDirichletEigenvalue n)
    (X := intervalDirichletSineMode n)
    (T := intervalHeatTimeMode n)
    (intervalDirichletSineMode_second_deriv n)
    (intervalHeatTimeMode_deriv n)
    t x

/-- The unit-interval heat mode satisfies the homogeneous Dirichlet condition at `x=0`. -/
@[simp] theorem intervalHeatMode_left_boundary (n : ℕ) (t : ℝ) :
    intervalHeatMode n t 0 = 0 := by
  simp [intervalHeatMode]

/-- The unit-interval heat mode satisfies the homogeneous Dirichlet condition at `x=1`. -/
@[simp] theorem intervalHeatMode_right_boundary (n : ℕ) (t : ℝ) :
    intervalHeatMode n t 1 = 0 := by
  simp [intervalHeatMode]

/-- The unit-interval heat mode has initial trace equal to its spatial sine mode. -/
@[simp] theorem intervalHeatMode_initial_trace (n : ℕ) (x : ℝ) :
    intervalHeatMode n 0 x = intervalDirichletSineMode n x := by
  simp [intervalHeatMode, intervalHeatTimeMode]

/-- The heat mode is `C²` in `(t, x)` and satisfies the residual, boundary, and initial
conditions. -/
theorem intervalHeatMode_satisfies_heat_dirichlet_ivp (n : ℕ) :
    ContDiff ℝ 2 (fun p : ℝ × ℝ ↦ intervalHeatMode n p.1 p.2) ∧
    (∀ t x : ℝ,
      deriv (fun s : ℝ ↦ intervalHeatMode n s x) t -
          deriv (deriv (fun y : ℝ ↦ intervalHeatMode n t y)) x = 0) ∧
    (∀ t : ℝ, intervalHeatMode n t 0 = 0) ∧
    (∀ t : ℝ, intervalHeatMode n t 1 = 0) ∧
    (∀ x : ℝ, intervalHeatMode n 0 x = intervalDirichletSineMode n x) := by
  refine ⟨?_, intervalHeatMode_residual_zero n, intervalHeatMode_left_boundary n,
    intervalHeatMode_right_boundary n, intervalHeatMode_initial_trace n⟩
  change ContDiff ℝ 2 (fun p : ℝ × ℝ ↦
    Real.sin (((n.succ : ℝ) * Real.pi) * p.2) *
      Real.exp (-intervalDirichletEigenvalue n * p.1))
  fun_prop

end

end HeatEquation
