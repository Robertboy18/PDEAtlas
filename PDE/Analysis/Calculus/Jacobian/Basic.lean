/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Calculus

/-!
# Jacobian matrices of Euclidean maps

Rows index the components of the map and columns index spatial directions. Each entry is
an actual coordinate derivative. On a `C²` germ the columns are differentiable, and their
directional derivatives form a symmetric family by commutation of mixed partial derivatives.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

variable {n m : ℕ}

/-- A spatial derivative of a map, expressed as its family of scalar component derivatives. -/
def jacobianColumn (u : ℝ^n → ℝ^m) (i : Fin n) (x : ℝ^n) : Fin m → ℝ :=
  fun k ↦ (∂[i] (fun y ↦ u y k)) x

/-- The Jacobian matrix has the scalar derivative `∂ᵢuᵏ` in row `k`, column `i`. -/
def jacobianMatrix (u : ℝ^n → ℝ^m) (x : ℝ^n) : Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun k i ↦ jacobianColumn u i x k

/-- The scalar-coordinate Jacobian agrees with the matrix of the actual Fréchet derivative. -/
theorem jacobianMatrix_apply_eq_fderiv {u : ℝ^n → ℝ^m} {x : ℝ^n}
    (hu : DifferentiableAt ℝ u x) (k : Fin m) (i : Fin n) :
    jacobianMatrix u x k i =
      fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ)) k :=
  (partialDeriv_apply i k hu).symm

/-- Forming a Jacobian column lowers finite local regularity by one order. -/
theorem contDiffAt_jacobianColumn {u : ℝ^n → ℝ^m} {x : ℝ^n}
    (r : ℕ) (hu : ContDiffAt ℝ (r + 1) u x) (j : Fin n) :
    ContDiffAt ℝ r (jacobianColumn u j) x := by
  apply contDiffAt_pi.mpr
  intro k
  have hk : ContDiffAt ℝ (r + 1) (fun y ↦ u y k) x :=
    (EuclideanSpace.proj k : ℝ^m →L[ℝ] ℝ).contDiff.contDiffAt.comp x hu
  exact contDiffAt_partialDeriv r hk j

/-- Each Jacobian column is differentiable at a point where the original map has a `C²` germ. -/
theorem differentiableAt_jacobianColumn {u : ℝ^n → ℝ^m} {x : ℝ^n}
    (hu : ContDiffAt ℝ 2 u x) (j : Fin n) :
    DifferentiableAt ℝ (jacobianColumn u j) x :=
  (contDiffAt_jacobianColumn 1 hu j).differentiableAt (by norm_num)

/-- The derivative of one Jacobian column in another coordinate direction is symmetric.
This is Clairaut's theorem applied to each component of the map. -/
theorem fderiv_jacobianColumn_comm {u : ℝ^n → ℝ^m} {x : ℝ^n}
    (hu : ContDiffAt ℝ 2 u x) (i j : Fin n) :
    fderiv ℝ (jacobianColumn u j) x
        (EuclideanSpace.single i (1 : ℝ)) =
      fderiv ℝ (jacobianColumn u i) x
        (EuclideanSpace.single j (1 : ℝ)) := by
  have hcolumn (a : Fin n) := differentiableAt_jacobianColumn hu a
  rw [fderiv_pi (differentiableAt_pi.mp (hcolumn j)),
    fderiv_pi (differentiableAt_pi.mp (hcolumn i))]
  ext k
  have hk : ContDiffAt ℝ 2 (fun y ↦ u y k) x :=
    (EuclideanSpace.proj k : ℝ^m →L[ℝ] ℝ).contDiff.contDiffAt.comp x hu
  exact partialDeriv_partialDeriv_comm_at i j hk

end PDE.Analysis
