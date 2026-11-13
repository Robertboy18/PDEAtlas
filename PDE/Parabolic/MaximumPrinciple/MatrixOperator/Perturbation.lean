/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.MaximumPrinciple.MatrixOperator
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Constant and potential perturbations of the parabolic operator

Adding a positive constant keeps a nonnegative approximate solution away from
zero. Its residual can then be absorbed into a bounded change of potential.
The identities require no derivatives of the potential.
-/

@[expose] public noncomputable section

namespace ParabolicMaximum

variable {n : ℕ}

/-- A constant added to the field contributes only through the potential. -/
theorem matrixParabolicOperator_add_const
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ → ℝ^n) (c : ℝ^n → ℝ → ℝ)
    {u : ℝ^n → ℝ → ℝ} {x : ℝ^n} {t : ℝ}
    (hu : ContDiffAt ℝ 2 (fun y ↦ u y t) x)
    (hut : DifferentiableAt ℝ (u x) t) (M : ℝ) :
    matrixParabolicOperator a b c (fun y s ↦ u y s + M) x t =
      matrixParabolicOperator a b c u x t + c x t * M := by
  have h := matrixParabolicOperator_sub a b c hu contDiffAt_const hut
    (differentiableAt_const (-M))
  simpa only [sub_neg_eq_add, matrixParabolicOperator_const, mul_neg] using h

/-- Changing only the potential changes the residual by multiplication. -/
theorem matrixParabolicOperator_sub_potential
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ → ℝ^n) (c d : ℝ^n → ℝ → ℝ)
    (u : ℝ^n → ℝ → ℝ) (x : ℝ^n) (t : ℝ) :
    matrixParabolicOperator a b (fun y s ↦ c y s - d y s) u x t =
      matrixParabolicOperator a b c u x t - d x t * u x t := by
  simp only [matrixParabolicOperator, EllipticMaximum.matrixOperator_apply]
  ring

/-- Wherever the field is nonzero, subtracting residual divided by value
from the potential makes its residual exactly zero. -/
theorem matrixParabolicOperator_correct_potential
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ → ℝ^n) (c : ℝ^n → ℝ → ℝ)
    (u : ℝ^n → ℝ → ℝ) {x : ℝ^n} {t : ℝ} (hu : u x t ≠ 0) :
    matrixParabolicOperator a b
      (fun y s ↦ c y s - matrixParabolicOperator a b c u y s / u y s) u x t = 0 := by
  rw [matrixParabolicOperator_sub_potential, div_mul_cancel₀ _ hu, sub_self]

/-- A lower value bound controls the potential correction by the corresponding
relative residual bound. The original potential may have either sign. -/
theorem abs_corrected_potential_le
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ → ℝ^n) (c : ℝ^n → ℝ → ℝ)
    (u : ℝ^n → ℝ → ℝ) {x : ℝ^n} {t ε K R : ℝ}
    (hε : 0 < ε) (hR : 0 ≤ R) (hu : ε ≤ u x t)
    (hc : |c x t| ≤ K) (hres : |matrixParabolicOperator a b c u x t| ≤ R * ε) :
    |c x t - matrixParabolicOperator a b c u x t / u x t| ≤ K + R := by
  have hpos := hε.trans_le hu
  apply (abs_sub _ _).trans
  apply add_le_add hc
  rw [abs_div, abs_of_pos hpos]
  exact (div_le_iff₀ hpos).mpr (hres.trans (mul_le_mul_of_nonneg_left hu hR))

end ParabolicMaximum
