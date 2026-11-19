/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import CAS.ExactTactic

/-!
# Separation-of-variables data

The Dirichlet eigenvalues `((n+1)π)^2` and sine modes of the unit interval: smoothness, the
first and second derivatives, the boundary values, and nontriviality. On the unit interval they
solve the eigenvalue problem `-Δw = λw`, `w = 0` on the boundary, to which separation of variables
reduces the heat equation in Evans, §4.1.1, Example 1 (equation (5)). The heat and wave equations
for these modes are proved in the corresponding equation modules.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.1.1, Example 1, (1)-(5),
  pp. 167-168.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Representations

section

variable {n : ℕ}

/-! ## Unit-interval Dirichlet modes -/

/-- The Dirichlet eigenvalue `((n+1)π)^2` for the unit-interval sine mode. -/
noncomputable def intervalDirichletEigenvalue (n : ℕ) : ℝ :=
  ((n.succ : ℝ) * Real.pi) ^ 2

/-- The `n`th positive Dirichlet sine mode on the unit interval. -/
noncomputable def intervalDirichletSineMode (n : ℕ) : ℝ → ℝ :=
  fun x ↦ Real.sin (((n.succ : ℝ) * Real.pi) * x)

/-- Every unit-interval Dirichlet sine mode is smooth. -/
theorem contDiff_intervalDirichletSineMode {k : WithTop ℕ∞} (n : ℕ) :
    ContDiff ℝ k (intervalDirichletSineMode n) := by
  unfold intervalDirichletSineMode
  fun_prop

/-- The unit-interval sine mode satisfies the Dirichlet eigenvalue equation. -/
theorem intervalDirichletSineMode_second_deriv (n : ℕ) (x : ℝ) :
    deriv (deriv (intervalDirichletSineMode n)) x =
      -intervalDirichletEigenvalue n * intervalDirichletSineMode n x := by
  cas

/-- First derivative of the unit-interval sine mode. -/
theorem intervalDirichletSineMode_deriv (n : ℕ) (x : ℝ) :
    deriv (intervalDirichletSineMode n) x =
      Real.cos (((n.succ : ℝ) * Real.pi) * x) * ((n.succ : ℝ) * Real.pi) := by
  cas

/-- Unit-interval sine modes have zero Dirichlet trace at the left endpoint. -/
@[simp] theorem intervalDirichletSineMode_zero (n : ℕ) :
    intervalDirichletSineMode n 0 = 0 := by
  simp [intervalDirichletSineMode]

/-- Unit-interval sine modes have zero Dirichlet trace at the right endpoint. -/
@[simp] theorem intervalDirichletSineMode_one (n : ℕ) :
    intervalDirichletSineMode n 1 = 0 := by
  simpa [intervalDirichletSineMode, mul_assoc] using (Real.sin_nat_mul_pi n.succ)

/-- Unit-interval sine modes are nontrivial. -/
theorem intervalDirichletSineMode_nontrivial (n : ℕ) :
    ∃ x : ℝ, intervalDirichletSineMode n x ≠ 0 := by
  refine ⟨((n : ℝ) + 1)⁻¹ * (2 : ℝ)⁻¹, ?_⟩
  let a : ℝ := (n.succ : ℝ) * Real.pi
  have hn : ((n : ℝ) + 1) ≠ 0 := by nlinarith
  have hx : a * (((n : ℝ) + 1)⁻¹ * (2 : ℝ)⁻¹) = Real.pi / 2 := by
    simp [a, Nat.cast_succ, div_eq_mul_inv, mul_assoc, mul_comm, hn]
  change Real.sin (a * (((n : ℝ) + 1)⁻¹ * (2 : ℝ)⁻¹)) ≠ 0
  rw [hx]
  norm_num

end

end PDE.Representations
