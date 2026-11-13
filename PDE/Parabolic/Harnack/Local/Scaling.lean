/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harnack.Local.Scaling
public import PDE.Parabolic.MaximumPrinciple.MatrixOperator
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Scaling the parabolic operator

Spatial dilation by `r` and temporal dilation by `r²` multiply the parabolic
residual by `r²`. The principal matrix is pulled back, drift gains a factor
`r`, and potential gains a factor `r²`. The spatial calculation is the elliptic
identity `EllipticHarnack.matrixOperator_comp_const_add_smul`.
-/

@[expose] public noncomputable section

namespace ParabolicHarnack

open ParabolicMaximum

variable {n : ℕ}

/-- The exact residual identity for parabolic translation and dilation.
It differentiates no coefficients and remains true at zero scale. -/
theorem matrixParabolicOperator_comp_space_time_dilation
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (d : ℝ^n → ℝ → ℝ^n) (c : ℝ^n → ℝ → ℝ)
    (u : ℝ^n → ℝ → ℝ) (z x : ℝ^n) (s t r : ℝ) :
    matrixParabolicOperator
      (fun y v ↦ a (z + r • y) (s + r ^ 2 * v))
      (fun y v ↦ r • d (z + r • y) (s + r ^ 2 * v))
      (fun y v ↦ r ^ 2 * c (z + r • y) (s + r ^ 2 * v))
      (fun y v ↦ u (z + r • y) (s + r ^ 2 * v)) x t =
        r ^ 2 * matrixParabolicOperator a d c u (z + r • x) (s + r ^ 2 * t) := by
  have htime :
      deriv (fun v ↦ u (z + r • x) (s + r ^ 2 * v)) t =
        r ^ 2 * deriv (u (z + r • x)) (s + r ^ 2 * t) := by
    rw [deriv_comp_mul_left (r ^ 2) (fun v ↦ u (z + r • x) (s + v)),
      deriv_comp_const_add]
    rfl
  rw [matrixParabolicOperator, htime,
    EllipticHarnack.matrixOperator_comp_const_add_smul
      (fun y ↦ a y (s + r ^ 2 * t)) (fun y ↦ d y (s + r ^ 2 * t))
      (fun y ↦ c y (s + r ^ 2 * t)) (fun y ↦ u y (s + r ^ 2 * t))]
  exact (mul_add _ _ _).symm

end ParabolicHarnack
