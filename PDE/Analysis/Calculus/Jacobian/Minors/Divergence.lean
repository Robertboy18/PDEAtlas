/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Jacobian.Piola

/-!
# Divergence form of Jacobian minors

Expansion along a row writes a determinant as a sum of first derivatives times
cofactors. The product rule and actual Piola cancellation turn it into a
divergence. This local identity applies to square minors of rectangular maps,
including repeated directions and singular Jacobians.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

variable {m n : ℕ}

/-- A selected Jacobian minor is the divergence of one component times its
cofactor row. All derivatives are actual coordinate derivatives. -/
theorem det_jacobianMatrix_submatrix_eq_sum_partialDeriv
    {u : ℝ^n → ℝ^m} {x : ℝ^n} (hu : ContDiffAt ℝ 2 u x)
    (σ : Fin m → Fin n) (k : Fin m) :
    ((jacobianMatrix u x).submatrix id σ).det =
      ∑ j, (∂[(σ j)] (fun y ↦ u y k * ((jacobianMatrix u y).submatrix id σ).adjugate j k)) x := by
  have hk : DifferentiableAt ℝ (fun y ↦ u y k) x :=
    ((EuclideanSpace.proj k : ℝ^m →L[ℝ] ℝ).differentiableAt).comp x
      (hu.differentiableAt (by norm_num))
  have hcofactor (j : Fin m) :
      DifferentiableAt ℝ
        (fun y ↦ ((jacobianMatrix u y).submatrix id σ).adjugate j k) x :=
    (contDiffAt_adjugate_jacobianMatrix_submatrix 1 hu σ k j).differentiableAt
      (by norm_num)
  simp_rw [partialDeriv_mul hk (hcofactor _)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_partialDeriv_adjugate_jacobianMatrix_submatrix_eq_zero hu σ k,
    mul_zero, add_zero]
  exact Matrix.det_eq_sum_mul_adjugate_row _ k

end PDE.Analysis
