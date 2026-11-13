/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.NormDet

/-!
# Surface Jacobians and cofactors

The Gram determinant of the first `m` columns of an `(m+1)`-square matrix is
the squared Euclidean norm of its final adjugate row. This identifies the
tangential area factor with the cofactor normal, including singular matrices
and zero-dimensional tangent spaces.
-/

@[expose] public section

namespace Matrix

open scoped Matrix

variable {m : ℕ}

/-- A codimension-one Gram minor is the sum of squares of the corresponding
adjugate row. Invertibility is unnecessary. -/
theorem det_gram_castSucc_eq_sum_sq_adjugate
    {R : Type*} [CommRing R] (A : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    ((Aᵀ * A).submatrix Fin.castSucc Fin.castSucc).det =
      ∑ i, A.adjugate (Fin.last m) i ^ 2 := by
  have hminor := adjugate_fin_succ_eq_det_submatrix (Aᵀ * A) (Fin.last m) (Fin.last m)
  have hsign : (-1 : R) ^ (m + m) = 1 := by
    rw [← two_mul, pow_mul]
    simp
  simp only [Fin.val_last, Fin.succAbove_last, hsign, one_mul] at hminor
  rw [← hminor, adjugate_mul_distrib, ← adjugate_transpose, mul_apply]
  simp only [transpose_apply, sq]

/-- The area factor of the first `m` columns equals the length of the final
cofactor row. -/
theorem normDet_castSucc_eq_norm_adjugate
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) :
    (A.submatrix id Fin.castSucc).toEuclideanLin.normDet =
      ‖WithLp.toLp 2 (A.adjugate (Fin.last m))‖ := by
  apply (sq_eq_sq₀ (LinearMap.normDet_nonneg _) (norm_nonneg _)).mp
  have hdet : (A.submatrix id Fin.castSucc).toEuclideanLin.normDet ^ 2 =
      (Matrix.gram ℝ (fun i ↦ (A.submatrix id Fin.castSucc).toEuclideanLin
        (EuclideanSpace.basisFun (Fin m) ℝ i))).det :=
    (A.submatrix id Fin.castSucc).toEuclideanLin.normDet_sq_eq_det_gram
      (EuclideanSpace.basisFun (Fin m) ℝ)
  rw [hdet]
  have hgram :
      Matrix.gram ℝ (fun i ↦ (A.submatrix id Fin.castSucc).toEuclideanLin
        (EuclideanSpace.basisFun (Fin m) ℝ i)) =
        (Aᵀ * A).submatrix Fin.castSucc Fin.castSucc := by
    ext i j
    simp [Matrix.gram_apply, Matrix.toLpLin_apply, EuclideanSpace.basisFun_apply,
      EuclideanSpace.single, PiLp.inner_apply, Matrix.mul_apply, mul_comm]
  rw [hgram, det_gram_castSucc_eq_sum_sq_adjugate, EuclideanSpace.real_norm_sq_eq]

/-- An inverse frame expresses its cofactor matrix through its determinant.
The explicit inverse makes this identity useful without matrix division. -/
theorem adjugate_eq_det_smul_of_mul_eq_one
    {R : Type*} [CommRing R] {A C : Matrix (Fin (m + 1)) (Fin (m + 1)) R}
    (hAC : A * C = 1) : A.adjugate = A.det • C := by
  calc
    A.adjugate = A.adjugate * (A * C) := by rw [hAC, mul_one]
    _ = (A.adjugate * A) * C := (mul_assoc _ _ _).symm
    _ = A.det • C := by rw [adjugate_mul, smul_mul_assoc, one_mul]

/-- For an invertible frame, the tangential area factor is the absolute
volume determinant times the length of its inverse normal covector. -/
theorem normDet_castSucc_eq_abs_det_mul_norm_of_mul_eq_one
    {A C : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hAC : A * C = 1) :
    (A.submatrix id Fin.castSucc).toEuclideanLin.normDet =
      |A.det| * ‖WithLp.toLp 2 (C (Fin.last m))‖ := by
  rw [normDet_castSucc_eq_norm_adjugate, adjugate_eq_det_smul_of_mul_eq_one hAC]
  change ‖A.det • WithLp.toLp 2 (C (Fin.last m))‖ = _
  rw [norm_smul, Real.norm_eq_abs]

end Matrix
