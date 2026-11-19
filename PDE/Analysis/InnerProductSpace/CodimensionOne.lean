/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Matrix.SurfaceJacobian
public import PDE.Common.Euclidean

/-!
# Tangential area and an inverse normal covector

A frame and its inverse determine the surface Jacobian of the first frame
vectors. The last coordinate of the inverse is the normal covector; its
Riesz vector supplies the normal length. No orthogonality of the frame is
required, and the tangent space may have dimension zero.
-/

@[expose] public section

noncomputable section

namespace ContinuousLinearMap

variable {m : ℕ}

/-- The area factor of a tangential frame is the volume determinant times
the length of its inverse normal covector. -/
theorem normDet_eq_abs_det_mul_norm_of_normal_covector
    (A C : ℝ^(m + 1) →L[ℝ] ℝ^(m + 1))
    (hAC : A.comp C = .id ℝ _)
    (T : ℝ^m →L[ℝ] ℝ^(m + 1))
    (hT : ∀ i, T (EuclideanSpace.basisFun (Fin m) ℝ i) =
      A (EuclideanSpace.basisFun (Fin (m + 1)) ℝ i.castSucc))
    (c : ℝ^(m + 1))
    (hc : ∀ x, inner ℝ c x = C x (Fin.last m)) :
    T.toLinearMap.normDet = |A.toLinearMap.det| * ‖c‖ := by
  let b := (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis
  let a := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
  let M := LinearMap.toMatrix b b A.toLinearMap
  let N := LinearMap.toMatrix b b C.toLinearMap
  have hMN : M * N = 1 := by
    rw [← LinearMap.toMatrix_comp]
    have hcomp : A.toLinearMap.comp C.toLinearMap = LinearMap.id := by
      exact congrArg ContinuousLinearMap.toLinearMap hAC
    rw [hcomp, LinearMap.toMatrix_id]
  have hTmatrix : T.toLinearMap = (M.submatrix id Fin.castSucc).toEuclideanLin := by
    apply (LinearMap.toMatrix a b).injective
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]
    ext i j
    simpa [M, a, b, LinearMap.toMatrix_apply] using
      congrArg (fun v ↦ b.repr v i) (hT j)
  have hcN : WithLp.toLp 2 (N (Fin.last m)) = c := by
    ext i
    have hi := hc (EuclideanSpace.basisFun (Fin (m + 1)) ℝ i)
    simpa [N, b, LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_right] using hi.symm
  rw [hTmatrix, Matrix.normDet_castSucc_eq_abs_det_mul_norm_of_mul_eq_one hMN,
    hcN, LinearMap.det_toMatrix]

end ContinuousLinearMap
