/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Jacobian.Minors.Divergence
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# A nonaffine Jacobian and its determinant divergence

For `u(x,y) = (x² + y, xy + y²)`, the Jacobian is variable and nonsymmetric,
and is singular at the origin. Its first cofactor row is divergence free (the Piola
identity), and the determinant is the divergence `∑ⱼ ∂ⱼ (u₀ (adj Du)ⱼ₀)`, the identity
behind weak continuity of Sobolev minors.
-/

@[expose] public noncomputable section

open PDE.Analysis
open scoped Matrix.Norms.Elementwise

namespace PDE.Examples.Polyconvexity

/-- The polynomial map `(x₀² + x₁, x₀x₁ + x₁²)`. -/
def polynomialMap (x : ℝ^2) : ℝ^2 :=
  WithLp.toLp 2 ![x 0 ^ 2 + x 1, x 0 * x 1 + x 1 ^ 2]

/-- The map is `C²`. -/
theorem polynomialMap_contDiff : ContDiff ℝ 2 polynomialMap := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i <;> dsimp [polynomialMap] <;> cas

/-- The Jacobian matrix of `polynomialMap` is `!![2x₀, 1; x₁, x₀ + 2x₁]`. -/
theorem jacobianMatrix_polynomialMap (x : ℝ^2) :
    jacobianMatrix polynomialMap x = !![2 * x 0, 1; x 1, x 0 + 2 * x 1] := by
  ext k i
  fin_cases k <;> fin_cases i <;>
    dsimp [jacobianMatrix, jacobianColumn, polynomialMap] <;> cas

/-- The determinant is nonconstant and vanishes at the origin. -/
theorem det_jacobianMatrix_polynomialMap (x : ℝ^2) :
    (jacobianMatrix polynomialMap x).det = 2 * x 0 ^ 2 + 4 * x 0 * x 1 - x 1 := by
  rw [jacobianMatrix_polynomialMap, Matrix.det_fin_two]
  change 2 * x 0 * (x 0 + 2 * x 1) - 1 * x 1 = _
  cas

/-- The Jacobian of `polynomialMap` is singular at the origin. -/
theorem det_jacobianMatrix_polynomialMap_zero :
    (jacobianMatrix polynomialMap 0).det = 0 := by
  rw [det_jacobianMatrix_polynomialMap]
  simp

/-- The cofactor matrix (the transpose of the adjugate) is
`!![x₀ + 2x₁, -x₁; -1, 2x₀]`. -/
theorem cofactor_polynomialMap (x : ℝ^2) :
    (jacobianMatrix polynomialMap x).adjugate.transpose =
      !![x 0 + 2 * x 1, -x 1; -1, 2 * x 0] := by
  rw [jacobianMatrix_polynomialMap, Matrix.adjugate_fin_two]
  ext k i
  fin_cases k <;> fin_cases i <;> rfl

/-- The first cofactor row `(x₀ + 2x₁, -x₁)` is divergence free: its derivative terms
are `1` and `-1`. -/
theorem first_cofactor_row_divergence (x : ℝ^2) :
    (∂[0] (fun y ↦ (jacobianMatrix polynomialMap y).adjugate 0 0)) x +
      (∂[1] (fun y ↦ (jacobianMatrix polynomialMap y).adjugate 1 0)) x = 0 := by
  have h₀ : (fun y ↦ (jacobianMatrix polynomialMap y).adjugate 0 0) =
      fun y : ℝ^2 ↦ y 0 + 2 * y 1 :=
    funext fun y ↦ congrArg (fun P : Matrix (Fin 2) (Fin 2) ℝ ↦ P 0 0)
      (cofactor_polynomialMap y)
  have h₁ : (fun y ↦ (jacobianMatrix polynomialMap y).adjugate 1 0) =
      fun y : ℝ^2 ↦ -y 1 :=
    funext fun y ↦ congrArg (fun P : Matrix (Fin 2) (Fin 2) ℝ ↦ P 0 1)
      (cofactor_polynomialMap y)
  rw [h₀, h₁]
  cas

/-- The determinant is the divergence `∑ⱼ ∂ⱼ (u₀ (adj Du)ⱼ₀)`. -/
theorem polynomialMap_determinant_divergence (x : ℝ^2) :
    (jacobianMatrix polynomialMap x).det =
      ∑ j, (∂[j] (fun y ↦ polynomialMap y 0 *
        (jacobianMatrix polynomialMap y).adjugate j 0)) x := by
  simpa only [Matrix.submatrix_id_id, id_eq] using
    det_jacobianMatrix_submatrix_eq_sum_partialDeriv polynomialMap_contDiff.contDiffAt
      id (0 : Fin 2)

end PDE.Examples.Polyconvexity
