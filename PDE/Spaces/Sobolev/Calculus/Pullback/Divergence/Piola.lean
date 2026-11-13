/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.ChangeOfVariables
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Piola transport of weak flux pairings

For a coordinate change `y = E x`, the flux becomes
`|det D(E⁻¹)(y)| DE(E⁻¹ y) q(E⁻¹ y)`.
The adjoint in the test-gradient chain rule gives its exact weak pairing.
This transport uses change of variables and does not differentiate the flux.
-/

@[expose] public noncomputable section

namespace SobolevSpace.WeakChangeOfVariables

open MeasureTheory Set
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- The volume-weighted pushforward of a vector flux by a coordinate chart. -/
def piolaTransform (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (q : ℝ^n → ℝ^n) (y : ℝ^n) : ℝ^n :=
  |(fderiv ℝ (fun z ↦ E.symm z) y).det| •
    fderiv ℝ (fun x ↦ E x) (E.symm y) (q (E.symm y))

/-- The adjoint pairing in coordinates, with derivative direction in the first index. -/
theorem inner_adjoint_eq_sum_coordinates (T : ℝ^n →L[ℝ] ℝ^n) (v w : ℝ^n) :
    ⟪v, T.adjoint w⟫ =
      ∑ i : Fin n, v i * ∑ j : Fin n, w j * (T (EuclideanSpace.single i 1)) j := by
  have hcoord (i : Fin n) :
      T.adjoint w i = ∑ j : Fin n, w j * (T (EuclideanSpace.single i 1)) j := by
    rw [← EuclideanSpace.inner_basisFun_real (i := i) (x := T.adjoint w)]
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp only [PiLp.inner_apply, EuclideanSpace.basisFun_apply, RCLike.inner_apply,
      conj_trivial, mul_comm]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, hcoord, mul_comm]

/-- The exact flux-pairing change of variables, valid without any derivative
of the vector field. The total Bochner integral convention is preserved. -/
theorem integral_source_flux_pairing_eq
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (q η : ℝ^n → ℝ^n) :
    (∫ x in E.source,
      ⟪q x, (fderiv ℝ (fun z ↦ E z) x).adjoint (η (E x))⟫) =
      ∫ y in E.target, ⟪piolaTransform E q y, η y⟫ := by
  rw [integral_source_eq_integral_abs_det_fderiv_mul
    (E' := fun y ↦ fderiv ℝ (fun z ↦ E.symm z) y)
    (fun y _ ↦ (hSymm.differentiable (by norm_num) y).hasFDerivAt)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem E.open_target.measurableSet] with y hy
  rw [E.right_inv hy]
  simp only [piolaTransform, real_inner_smul_left, ContinuousLinearMap.adjoint_inner_right]

/-- The scalar forcing transforms with the same absolute Jacobian determinant. -/
theorem integral_source_load_pairing_eq
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (f φ : ℝ^n → ℝ) :
    (∫ x in E.source, f x * φ (E x)) =
      ∫ y in E.target, (|(fderiv ℝ (fun z ↦ E.symm z) y).det| * f (E.symm y)) * φ y := by
  rw [integral_source_eq_integral_abs_det_fderiv_mul
    (E' := fun y ↦ fderiv ℝ (fun z ↦ E.symm z) y)
    (fun y _ ↦ (hSymm.differentiable (by norm_num) y).hasFDerivAt)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem E.open_target.measurableSet] with y hy
  rw [E.right_inv hy, mul_assoc]

end SobolevSpace.WeakChangeOfVariables
