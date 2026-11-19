/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Representations.SeparationOfVariables
import CAS.ExactTactic

/-!
# Separated modes for the one-dimensional wave equation

We pair the unit-interval Dirichlet sine modes with matching oscillatory time factors,
which for the unit wave speed are the same sine modes `sin((n+1)πt)`. We prove the separated
product residual and describe the resulting classical wave modes with their boundary and initial
data.

The computation follows Evans, §4.1.1, Example 1, which separates variables for the heat
equation: the product form (2) and the separated equations (3)-(5), with the Dirichlet
eigenvalues of `-Δ`. For the wave equation the time factor solves `v'' = -λv` in place of (4).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.1.1, Example 1, equations (2)-(5).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace WaveEquation

open PDE.Representations

section

/-- A separated wave solution built from the `n`th unit-interval Dirichlet sine mode: the spatial
factor `sin((n+1)πx)` times the time factor `sin((n+1)πt)`, which is the same sine mode because
the wave speed is one. -/
noncomputable def intervalWaveMode (n : ℕ) (t x : ℝ) : ℝ :=
  intervalDirichletSineMode n x * intervalDirichletSineMode n t

/-- Separation-of-variables product calculation for the one-dimensional wave equation.

If both separated factors solve the same oscillator equation `Y'' = -λY`, then the product field
`u(t,x) = X(x)T(t)` has zero wave residual `u_tt - u_xx`. The oscillator hypotheses state the
second-derivative identities needed by this calculation. -/
theorem separated_wave_residual_zero {lam : ℝ} {X T : ℝ → ℝ}
    (hX : ∀ x : ℝ, deriv (deriv X) x = -lam * X x) (hT : ∀ t : ℝ, deriv (deriv T) t = -lam * T t)
    (t x : ℝ) :
    deriv (deriv (fun s : ℝ ↦ X x * T s)) t - deriv (deriv (fun y : ℝ ↦ X y * T t)) x = 0 := by
  have htime1 : deriv (fun s : ℝ ↦ X x * T s) = fun s : ℝ ↦ X x * deriv T s :=
    deriv_const_mul_field' (X x)
  have htime2 :
      deriv (deriv (fun s : ℝ ↦ X x * T s)) t = X x * deriv (deriv T) t := by
    calc
      deriv (deriv (fun s : ℝ ↦ X x * T s)) t =
          deriv (fun s : ℝ ↦ X x * deriv T s) t := by
        simp [htime1]
      _ = X x * deriv (deriv T) t := deriv_const_mul_field (X x)
  have hspace1 : deriv (fun y : ℝ ↦ X y * T t) = fun y : ℝ ↦ deriv X y * T t :=
    deriv_mul_const_field' (T t)
  have hspace2 :
      deriv (deriv (fun y : ℝ ↦ X y * T t)) x = deriv (deriv X) x * T t := by
    calc
      deriv (deriv (fun y : ℝ ↦ X y * T t)) x =
          deriv (fun y : ℝ ↦ deriv X y * T t) x := by
        simp [hspace1]
      _ = deriv (deriv X) x * T t := deriv_mul_const_field (T t)
  rw [htime2, hspace2, hT t, hX x]
  ring

/-- The product `sin((n+1)πx) sin((n+1)πt)` has zero wave residual. -/
theorem intervalWaveMode_residual_zero (n : ℕ) (t x : ℝ) :
    deriv (deriv (fun s : ℝ ↦ intervalWaveMode n s x)) t -
        deriv (deriv (fun y : ℝ ↦ intervalWaveMode n t y)) x = 0 :=
  separated_wave_residual_zero (lam := intervalDirichletEigenvalue n)
    (X := intervalDirichletSineMode n) (T := intervalDirichletSineMode n)
    (intervalDirichletSineMode_second_deriv n) (intervalDirichletSineMode_second_deriv n) t x

/-- The unit-interval wave mode satisfies the homogeneous Dirichlet condition at `x=0`. -/
@[simp] theorem intervalWaveMode_left_boundary (n : ℕ) (t : ℝ) :
    intervalWaveMode n t 0 = 0 := by
  simp [intervalWaveMode]

/-- The unit-interval wave mode satisfies the homogeneous Dirichlet condition at `x=1`. -/
@[simp] theorem intervalWaveMode_right_boundary (n : ℕ) (t : ℝ) :
    intervalWaveMode n t 1 = 0 := by
  simp [intervalWaveMode]

/-- The sine-in-time wave mode has zero initial displacement. -/
@[simp] theorem intervalWaveMode_initial_displacement (n : ℕ) (x : ℝ) :
    intervalWaveMode n 0 x = 0 := by
  simp [intervalWaveMode, intervalDirichletSineMode]

/-- The sine-in-time wave mode has initial velocity `((n+1)π) sin((n+1)πx)`. -/
theorem intervalWaveMode_initial_velocity (n : ℕ) (x : ℝ) :
    deriv (fun t : ℝ ↦ intervalWaveMode n t x) 0 =
      intervalDirichletSineMode n x * ((n.succ : ℝ) * Real.pi) := by
  unfold intervalWaveMode intervalDirichletSineMode
  cas

/-- The named smooth wave mode satisfies the residual, boundary, and initial conditions. -/
theorem intervalWaveMode_satisfies_wave_dirichlet_ivp (n : ℕ) :
    ContDiff ℝ 2 (fun p : ℝ × ℝ ↦ intervalWaveMode n p.1 p.2) ∧
    (∀ t x : ℝ,
      deriv (deriv (fun s : ℝ ↦ intervalWaveMode n s x)) t -
          deriv (deriv (fun y : ℝ ↦ intervalWaveMode n t y)) x = 0) ∧
    (∀ t : ℝ, intervalWaveMode n t 0 = 0) ∧
    (∀ t : ℝ, intervalWaveMode n t 1 = 0) ∧
    (∀ x : ℝ, intervalWaveMode n 0 x = 0) ∧
    (∀ x : ℝ,
      deriv (fun t : ℝ ↦ intervalWaveMode n t x) 0 =
        intervalDirichletSineMode n x * ((n.succ : ℝ) * Real.pi)) := by
  refine ⟨?_, intervalWaveMode_residual_zero n, intervalWaveMode_left_boundary n,
    intervalWaveMode_right_boundary n, intervalWaveMode_initial_displacement n,
    intervalWaveMode_initial_velocity n⟩
  change ContDiff ℝ 2 (fun p : ℝ × ℝ ↦ Real.sin (((n.succ : ℝ) * Real.pi) * p.2) *
      Real.sin (((n.succ : ℝ) * Real.pi) * p.1))
  fun_prop

end

end WaveEquation
