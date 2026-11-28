/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.InnerProductSpace.Complexification.Operator

/-!
# The universal property of the complexification

A real-linear map `φ` from a real inner product space `H` to a complex vector space `V` extends
to a complex-linear map on the complexification `H + iH`, in exactly one way:
`x + i y ↦ φ x + i φ y`. The extension `lift φ` is continuous when `φ` is, and the
complexification `complexify T` of a bounded operator `T` is the lift of `x ↦ ofReal (T x)`.
The norm of the lift is not computed here.

## Main results

* `lift`: the complex-linear extension of every real-linear map into a complex vector space
  whose real scalar action is the restriction of the complex one, with `lift_apply` and
  `lift_ofReal`.
* `eq_lift`: a complex-linear map that agrees with `φ` on the real elements is `lift φ`.
* `continuous_lift`: the lift of a continuous map into a topological vector space is continuous.
* `complexify_eq_lift`: for every bounded operator `T` on `H`, `complexify T` is the lift of
  `x ↦ ofReal (T x)`.

## How it works

Additivity is clear. For a complex scalar `c = a + b i` the product `c (x + i y)` is
`(a x - b y) + i (a y + b x)`, and applying `φ` to the two parts gives `c (φ x + i φ y)`,
because `i² = -1` in `V`. Every element is `x + i y` with `x` and `y` real
(`ofReal_re_add_I_smul_ofReal_im`), so a complex-linear map is determined by its values on the
real elements, which gives uniqueness.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Complexification

variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [AddCommGroup V]
  [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V]

/-- **The complex-linear extension of a real-linear map** from `H` to a complex vector space:
`x + i y ↦ φ x + i φ y`. -/
def lift (φ : H →ₗ[ℝ] V) : Complexification H →ₗ[ℂ] V where
  toFun z := φ z.re + Complex.I • φ z.im
  map_add' z w := by
    simp only [re_add, im_add, map_add, smul_add]
    abel
  map_smul' c z := by
    have hI (v : V) : Complex.I • Complex.I • v = -v := by
      rw [smul_smul, Complex.I_mul_I, neg_one_smul]
    have hr (r : ℝ) (v : V) : r • v = (r : ℂ) • v := (algebraMap_smul ℂ r v).symm
    simp only [re_smul, im_smul, map_sub, map_add, map_smul, RingHom.id_apply, hr]
    conv_rhs => rw [← Complex.re_add_im c]
    simp only [add_smul, smul_add, mul_smul, hI,
      smul_comm Complex.I ((c.re : ℂ)) (φ _), smul_comm Complex.I ((c.im : ℂ)) (φ _), smul_neg]
    abel

/-- The lift sends `x + i y` to `φ x + i φ y`. -/
@[simp]
theorem lift_apply (φ : H →ₗ[ℝ] V) (z : Complexification H) :
    lift φ z = φ z.re + Complex.I • φ z.im := rfl

/-- The lift extends `φ`: on a real element `x` it is `φ x`. -/
@[simp]
theorem lift_ofReal (φ : H →ₗ[ℝ] V) (x : H) : lift φ (ofReal x) = φ x := by
  rw [lift_apply, re_ofReal, im_ofReal, map_zero, smul_zero, add_zero]

/-- **The lift is the only complex-linear extension**: a complex-linear map that agrees with
`φ` on the real elements is `lift φ`, because every element is `x + i y` with `x`, `y` real. -/
theorem eq_lift {φ : H →ₗ[ℝ] V} {ψ : Complexification H →ₗ[ℂ] V}
    (h : ∀ x, ψ (ofReal x) = φ x) : ψ = lift φ := by
  refine LinearMap.ext fun z ↦ ?_
  conv_lhs => rw [← ofReal_re_add_I_smul_ofReal_im z]
  rw [map_add, map_smul, h, h, lift_apply]

/-- **The complexification of a bounded operator is a lift**: `complexify T` is the
complex-linear extension of `x ↦ ofReal (T x)`. -/
theorem complexify_eq_lift (T : H →L[ℝ] H) :
    (complexify T).toLinearMap = lift (ofRealLI.toLinearMap ∘ₗ T.toLinearMap) :=
  eq_lift fun x ↦ complexify_ofReal T x

/-- The lift of a continuous map into a topological vector space is continuous. -/
theorem continuous_lift [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul ℂ V]
    {φ : H →ₗ[ℝ] V} (hφ : Continuous φ) : Continuous (lift φ) :=
  (hφ.comp reCLM.continuous).add ((hφ.comp imCLM.continuous).const_smul Complex.I)

end PDE.Analysis.Complexification
