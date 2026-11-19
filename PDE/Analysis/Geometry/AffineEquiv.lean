/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.ContinuousAffineEquiv

/-!
# Continuous affine equivalences between normed spaces

The linear part of a continuous affine equivalence is a continuous linear equivalence.
Mathlib provides the algebraic linear part `AffineEquiv.linear` and the continuous linear
parts of the affine maps in both directions. `ContinuousAffineEquiv.continuousLinearPart`
combines them into a continuous linear equivalence, given by `x ↦ A x - A 0`.
-/

@[expose] public section

noncomputable section

namespace ContinuousAffineEquiv

variable {D E G : Type*}
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The continuous linear equivalence underlying a continuous affine equivalence. -/
def continuousLinearPart (A : D ≃ᴬ[ℝ] E) : D ≃L[ℝ] E where
  toLinearEquiv := A.toAffineEquiv.linear
  continuous_toFun := A.toContinuousAffineMap.contLinear.continuous
  continuous_invFun := A.symm.toContinuousAffineMap.contLinear.continuous

/-- The linear part of an affine equivalence is the map with the translation removed:
`L x = A x - A 0`. -/
@[simp]
theorem continuousLinearPart_apply (A : D ≃ᴬ[ℝ] E) (x : D) :
    A.continuousLinearPart x = A x - A 0 := by
  change A.toContinuousAffineMap.contLinear x = A x - A 0
  have h := congrFun A.toContinuousAffineMap.decomp x
  exact eq_sub_of_add_eq (by simpa using h.symm)

/-- Decomposition of an affine equivalence into its linear part and translation:
`A x = L x + A 0`. -/
theorem apply_eq_continuousLinearPart_add (A : D ≃ᴬ[ℝ] E) (x : D) :
    A x = A.continuousLinearPart x + A 0 := by
  rw [continuousLinearPart_apply]
  exact (sub_add_cancel _ _).symm

/-- The linear part of the identity affine equivalence is the identity. -/
@[simp]
theorem continuousLinearPart_refl :
    (ContinuousAffineEquiv.refl ℝ D).continuousLinearPart =
      ContinuousLinearEquiv.refl ℝ D := by
  rfl

/-- The linear part of the inverse is the inverse of the linear part. -/
@[simp]
theorem continuousLinearPart_symm (A : D ≃ᴬ[ℝ] E) :
    A.symm.continuousLinearPart = A.continuousLinearPart.symm := by
  ext x
  rfl

/-- Taking linear parts is functorial: the linear part of a composite is the composite of the
linear parts. -/
@[simp]
theorem continuousLinearPart_trans (A : D ≃ᴬ[ℝ] E) (B : E ≃ᴬ[ℝ] G) :
    (A.trans B).continuousLinearPart =
      A.continuousLinearPart.trans B.continuousLinearPart := by
  ext x
  rfl

end ContinuousAffineEquiv
