/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.InverseFunction.Chart

/-!
# Coordinate derivatives of local inverses

The coordinate Jacobian is the standard-basis matrix of the derivative. The inverse function
identities therefore give a matrix inverse, or equivalently the determinant-scaled adjugate.
The two-dimensional cofactor formula retains the sign of the determinant for PDE substitutions.
-/

@[expose] public noncomputable section

open Set

namespace PDE.Analysis

/-- The coordinate Jacobian is the matrix of the derivative in the standard bases.
Rows index the output coordinates and columns index the input directions. -/
theorem jacobianMatrix_eq_toMatrix
    {n m : ℕ} {f : ℝ^n → ℝ^m} {x : ℝ^n}
    (hf : DifferentiableAt ℝ f x) :
    jacobianMatrix f x =
      LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin m) ℝ).toBasis (fderiv ℝ f x).toLinearMap := by
  ext i j
  rw [jacobianMatrix_apply_eq_fderiv hf]
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply]
  rfl

/-- The coordinate Jacobian of an inverse chart is the matrix inverse of the
original Jacobian. Both matrices are formed from actual coordinate derivatives. -/
theorem inverse_chart_jacobian_symm
    {n : ℕ} (e : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    {y : ℝ^n} (hy : y ∈ e.target)
    (hf : DifferentiableAt ℝ e (e.symm y))
    (hi : DifferentiableAt ℝ e.symm y) :
    jacobianMatrix e.symm y = (jacobianMatrix e (e.symm y))⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [jacobianMatrix_eq_toMatrix hf, jacobianMatrix_eq_toMatrix hi,
    ← LinearMap.toMatrix_comp]
  change LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      ((fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y)).toLinearMap = 1
  rw [inverse_chart_fderiv_comp e hy hf hi]
  exact LinearMap.toMatrix_id _

/-- Multiplying the inverse Jacobian by the signed original determinant gives
the adjugate. This form avoids divisions in subsequent PDE substitutions. -/
theorem inverse_chart_det_smul_jacobian
    {n : ℕ} (e : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    {y : ℝ^n} (hy : y ∈ e.target)
    (hf : DifferentiableAt ℝ e (e.symm y))
    (hi : DifferentiableAt ℝ e.symm y) :
    (jacobianMatrix e (e.symm y)).det • jacobianMatrix e.symm y =
      (jacobianMatrix e (e.symm y)).adjugate := by
  have hdet := left_ne_zero_of_mul_eq_one (inverse_chart_det_mul e hy hf hi)
  rw [inverse_chart_jacobian_symm e hy hf hi, Matrix.inv_def, Ring.inverse_eq_inv,
    smul_smul, mul_inv_cancel₀ hdet, one_smul]

/-- In two dimensions the inverse coordinate derivatives are the signed cofactors
of the original Jacobian, divided by its determinant. -/
theorem inverse_chart_jacobian_cofactors
    (e : OpenPartialHomeomorph (ℝ^2) (ℝ^2))
    {y : ℝ^2} (hy : y ∈ e.target)
    (hf : DifferentiableAt ℝ e (e.symm y))
    (hi : DifferentiableAt ℝ e.symm y) :
    (jacobianMatrix e (e.symm y)).det • jacobianMatrix e.symm y =
      !![(jacobianMatrix e (e.symm y)) 1 1,
          -(jacobianMatrix e (e.symm y)) 0 1;
        -(jacobianMatrix e (e.symm y)) 1 0,
          (jacobianMatrix e (e.symm y)) 0 0] := by
  rw [inverse_chart_det_smul_jacobian e hy hf hi, Matrix.adjugate_fin_two]

end PDE.Analysis
