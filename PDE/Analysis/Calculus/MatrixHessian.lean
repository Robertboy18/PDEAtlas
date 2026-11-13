/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Contact.Hessian
public import PDE.Analysis.LinearAlgebra.EuclideanMatrix
public import PDE.FDeriv.Calculus

/-!
# Coordinate contractions of the Hessian

The trace of a matrix composed with the derivative of the gradient is exactly
the contraction with the coordinate second derivatives. All regularity is local
to the evaluation point; the matrix is not differentiated.
-/

@[expose] public section

open scoped Gradient

noncomputable section

namespace PDE.Analysis

open scoped Matrix RealInnerProductSpace

variable {n : ℕ}

/-- The Hessian trace contracts with the second coordinate derivatives. -/
theorem trace_toEuclideanLin_comp_fderiv_gradient
    (A : Matrix (Fin n) (Fin n) ℝ) {u : ℝ^n → ℝ} {x : ℝ^n}
    (hu : ContDiffAt ℝ 2 u x) :
    LinearMap.trace ℝ (ℝ^n)
      (A.toEuclideanLin.comp (fderiv ℝ (∇ u) x).toLinearMap) =
        ∑ i : Fin n, ∑ j : Fin n, A i j * (∂[i] (∂[j] u)) x := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin n) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [EuclideanSpace.basisFun_apply, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, EuclideanSpace.inner_single_left, map_one, one_mul]
  change (A *ᵥ ⇑((fderiv ℝ (∇ u) x) (EuclideanSpace.single i 1))) i = _
  rw [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have h := inner_fderiv_gradient_at hu (EuclideanSpace.single i 1)
    (EuclideanSpace.single j 1)
  simp only [EuclideanSpace.inner_single_right, one_mul, RCLike.conj_to_real] at h
  rw [h, ← secondPartialDeriv_eq_fderiv]
  exact (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt_one

end PDE.Analysis
