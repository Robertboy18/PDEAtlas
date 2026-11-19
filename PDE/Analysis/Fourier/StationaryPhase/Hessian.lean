/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Hessian.Gaussian
public import PDE.Analysis.Calculus.Gradient
public import PDE.Analysis.Calculus.Jacobian.Determinant
public import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# Nondegeneracy and signature of the Hessian

The matrix of the second derivative agrees with the coordinate Jacobian of the
gradient. Thus a nonzero Hessian determinant gives an invertible derivative of
the gradient. The signature uses the positive and negative inertia indices of
the Hessian quadratic form.
-/

@[expose] public noncomputable section

open scoped Gradient

namespace PDE.Analysis.StationaryPhase

variable {n : ℕ}

/-- The signature of the Hessian, independent of a diagonalizing basis. -/
def hessianSignature (f : ℝ^n → ℝ) (p : ℝ^n) : ℤ :=
  (sigPos (fderiv ℝ (fderiv ℝ f) p).toBilinForm.toQuadraticMap : ℤ) -
    (sigNeg (fderiv ℝ (fderiv ℝ f) p).toBilinForm.toQuadraticMap : ℤ)

/-- Schwarz symmetry makes the Hessian matrix of a `C²` function Hermitian. -/
theorem hessianMatrix_isHermitian {f : ℝ^n → ℝ} {p : ℝ^n}
    (hf : ContDiffAt ℝ 2 f p) : (PDE.Analysis.hessianMatrix f p).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  apply (LinearMap.BilinForm.isSymm_toMatrix_iff_isSymm
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis).mpr
  exact ⟨hf.isSymmSndFDerivAt (by norm_num)⟩

/-- The Hessian matrix is the coordinate derivative of the gradient. -/
theorem jacobianMatrix_gradient {f : ℝ^n → ℝ} {p : ℝ^n}
    (hf : ContDiffAt ℝ 2 f p) :
    PDE.Analysis.jacobianMatrix (∇ f) p = PDE.Analysis.hessianMatrix f p := by
  have hg : ContDiffAt ℝ 1 (∇ f) p :=
    PDE.Analysis.contDiffAt_gradient (m := 1) (by convert hf using 1; norm_num)
  ext i j
  rw [PDE.Analysis.jacobianMatrix_apply_eq_fderiv (hg.differentiableAt one_ne_zero)]
  change (fderiv ℝ (∇ f) p (EuclideanSpace.single j 1)) i =
    fderiv ℝ (fderiv ℝ f) p (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  have h := PDE.Analysis.inner_fderiv_gradient_at hf
    (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)
  simp only [EuclideanSpace.inner_single_right, one_mul, RCLike.conj_to_real] at h
  rw [h]
  exact (hf.isSymmSndFDerivAt (by norm_num)).eq _ _

/-- A nonzero Hessian determinant gives an invertible derivative of the
gradient. -/
theorem exists_hessian_continuousLinearEquiv {f : ℝ^n → ℝ} {p : ℝ^n}
    (hf : ContDiffAt ℝ 2 f p) (hdet : (PDE.Analysis.hessianMatrix f p).det ≠ 0) :
    ∃ H : ℝ^n ≃L[ℝ] ℝ^n, (H : ℝ^n →L[ℝ] ℝ^n) = fderiv ℝ (∇ f) p := by
  have hg : ContDiffAt ℝ 1 (∇ f) p :=
    PDE.Analysis.contDiffAt_gradient (m := 1) (by convert hf using 1; norm_num)
  have hu : IsUnit (LinearMap.det (fderiv ℝ (∇ f) p).toLinearMap) := by
    apply isUnit_iff_ne_zero.mpr
    change (fderiv ℝ (∇ f) p).det ≠ 0
    rw [← PDE.Analysis.det_jacobianMatrix (hg.differentiableAt one_ne_zero),
      jacobianMatrix_gradient hf]
    exact hdet
  refine ⟨(LinearMap.equivOfIsUnitDet hu).toContinuousLinearEquiv, ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun L : ℝ^n →ₗ[ℝ] ℝ^n ↦ L v) (LinearMap.coe_equivOfIsUnitDet hu)

end PDE.Analysis.StationaryPhase
