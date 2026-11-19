/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.NormDet

/-!
# Continuity of the volume factor of a linear map

The square of `LinearMap.normDet` is a Gram determinant. This description proves
continuity even where the rank drops, without choosing a basis of the varying range.
-/

@[expose] public section

noncomputable section

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

namespace ContinuousLinearMap

/-- The volume factor is continuous in the operator norm, including at singular maps. -/
theorem continuous_normDet :
    Continuous (fun A : E →L[ℝ] F ↦ A.toLinearMap.normDet) := by
  let b := stdOrthonormalBasis ℝ E
  have hgram : Continuous (fun A : E →L[ℝ] F ↦
      Matrix.gram ℝ (fun j ↦ A (b j))) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (continuous_id.clm_apply continuous_const).inner
      (continuous_id.clm_apply continuous_const)
  convert Real.continuous_sqrt.comp hgram.matrix_det using 1
  funext A
  change A.toLinearMap.normDet =
    √(Matrix.gram ℝ (fun j ↦ A.toLinearMap (b j))).det
  rw [← A.toLinearMap.normDet_sq_eq_det_gram b]
  exact (Real.sqrt_sq A.toLinearMap.normDet_nonneg).symm

end ContinuousLinearMap
