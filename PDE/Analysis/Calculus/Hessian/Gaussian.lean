/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Gaussian.Quadratic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The Gaussian associated with a Hessian

We represent the second Fréchet derivative of `f` at `x` in the standard orthonormal basis of
`ℝ^n` as `hessianMatrix f x`. Schwarz symmetry, Mathlib's `ContDiffAt.isSymmSndFDerivAt`, and
positivity of the second derivative make this matrix positive definite, and its determinant
computes the Gaussian constant used in Laplace asymptotics.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open MeasureTheory Matrix

variable {n : ℕ}

/-- The matrix of the second derivative of `f` at `x` in the standard orthonormal basis
of `ℝ^n`. -/
def hessianMatrix (f : ℝ^n → ℝ)
    (x : ℝ^n) : Matrix (Fin n) (Fin n) ℝ :=
  (fderiv ℝ (fderiv ℝ f) x).toBilinForm.toMatrix
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis

/-- If `f` is `C²` at `x` and its second derivative is positive on nonzero vectors, the
Hessian matrix is positive definite. -/
theorem hessianMatrix_posDef {f : ℝ^n → ℝ}
    {x : ℝ^n} (hf : ContDiffAt ℝ 2 f x)
    (hH : ∀ v : ℝ^n, v ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ f) x v v) : (hessianMatrix f x).PosDef := by
  have hs : (fderiv ℝ (fderiv ℝ f) x).toBilinForm.IsSymm :=
    ⟨hf.isSymmSndFDerivAt (by norm_num)⟩
  exact ((fderiv ℝ (fderiv ℝ f) x).toBilinForm.posDef_toQuadraticMap_iff_matrix
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis hs).mp hH

/-- The quadratic form of the Hessian matrix at `v` is the second derivative of `f` at `x`
applied to `(v, v)`. -/
theorem inner_hessianMatrix (f : ℝ^n → ℝ)
    (x v : ℝ^n) :
    inner ℝ v (Matrix.toEuclideanLin (hessianMatrix f x) v) =
      fderiv ℝ (fderiv ℝ f) x v v := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin,
    Matrix.toLin'_apply, star_trivial, dotProduct_comm]
  have hrepr : ⇑((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.repr v) = v.ofLp := by
    funext i
    exact (EuclideanSpace.basisFun (Fin n) ℝ).coe_toBasis_repr_apply v i
  simpa only [hessianMatrix, ContinuousLinearMap.toBilinForm_apply, hrepr] using
    ((fderiv ℝ (fderiv ℝ f) x).toBilinForm.apply_eq_dotProduct_toMatrix_mulVec
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis v v).symm

/-- If `f` is `C²` at `x` and its second derivative is positive on nonzero vectors, the
integral of `exp (-D²f(x)(v, v) / 2)` over `ℝ^n` is `(2π)^(n/2)` divided by the square root
of the determinant of the Hessian matrix. -/
theorem integral_actual_hessian_gaussian {f : ℝ^n → ℝ}
    {x : ℝ^n} (hf : ContDiffAt ℝ 2 f x)
    (hH : ∀ v : ℝ^n, v ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ f) x v v) :
    (∫ v : ℝ^n,
      Real.exp (-fderiv ℝ (fderiv ℝ f) x v v / 2)) =
        (2 * Real.pi) ^ ((n : ℝ) / 2) / Real.sqrt (hessianMatrix f x).det := by
  simpa only [inner_hessianMatrix] using
    integral_gaussian_quadratic_rpow (hessianMatrix_posDef hf hH)

end PDE.Analysis
