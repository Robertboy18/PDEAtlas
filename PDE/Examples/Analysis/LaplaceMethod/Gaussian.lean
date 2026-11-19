/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Gaussian.Quadratic
public import Mathlib.Algebra.Order.Star.Real
import CAS.ExactTactic

/-!
# Anisotropic Gaussian constants

A rotated positive-definite matrix with nonzero off-diagonal entries gives the
determinant normalization of the Gaussian integral.
-/

open MeasureTheory Matrix

@[expose] public noncomputable section

namespace PDE.Examples.LaplaceMethod

open PDE.Analysis

/-- The rotated form `!![5, 3; 3, 5]`, with eigenvalues `8` and `2` and nonzero off-diagonal
entries, is positive definite. -/
theorem rotated_posDef : (!![5, 3; 3, 5] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num
  intro x hx
  have hne : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    funext i
    fin_cases i <;> simp_all
  simp only [dotProduct, mulVec, Fin.sum_univ_two, star_trivial,
    Matrix.of_apply, cons_val_zero, cons_val_one]
  rcases hne with h | h
  · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x 0 + x 1), sq_nonneg (x 1)]
  · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x 0 + x 1), sq_nonneg (x 0)]

/-- The rotated anisotropic Gaussian has determinant `16` and integral `π/2`. -/
theorem integral_rotated :
    (∫ x : ℝ^2, Real.exp (-inner ℝ x
      (Matrix.toEuclideanLin !![5, 3; 3, 5] x) / 2)) = Real.pi / 2 := by
  rw [integral_gaussian_quadratic_rpow rotated_posDef]
  norm_num [Matrix.det_fin_two]
  cas

end PDE.Examples.LaplaceMethod
