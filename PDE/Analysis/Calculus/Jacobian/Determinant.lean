/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Jacobian.Basic
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Determinant of the coordinate Jacobian

The coordinate Jacobian is the matrix of the Fréchet derivative in the
standard orthonormal basis. Their determinants therefore agree, with sign.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

/-- The coordinate Jacobian has the signed determinant of the actual derivative. -/
theorem det_jacobianMatrix {n : ℕ} {f : ℝ^n → ℝ^n} {p : ℝ^n}
    (hf : DifferentiableAt ℝ f p) :
    (jacobianMatrix f p).det = (fderiv ℝ f p).det := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
  congr 1
  ext i j
  rw [jacobianMatrix_apply_eq_fderiv hf]
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply]
  rfl

end PDE.Analysis
