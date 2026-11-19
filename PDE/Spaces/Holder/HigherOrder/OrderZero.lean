/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Holder.HigherOrder.Norm

/-!
# Order zero agrees with the scalar Hölder space

At order zero there are no derivative relations. The continuous field agrees
with its Hölder field, so the higher-order construction recovers `C0GammaOn`
isometrically.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.1, (3), p. 255.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace HolderSpace.CKGammaOn

variable {n : ℕ} {Ω : Set (ℝ^n)} {γ : Exponent}

/-- A scalar Hölder function is a compatible graph of order zero. -/
def ofOrderZero (f : C0GammaOn (closure Ω) γ) : CKGammaOn n 0 Ω γ :=
  ⟨(fun _ ↦ f.toBoundedContinuousFunction, fun _ ↦ f),
    fun _ ↦ rfl,
    fun _ ha ↦ (Nat.not_lt_zero _ ha).elim⟩

/-- At order zero the complete graph norm is precisely the scalar Hölder norm. -/
theorem norm_orderZero (f : CKGammaOn n 0 Ω γ) :
    ‖f‖ = ‖f.topDerivative default‖ := by
  apply le_antisymm _ (f.norm_topDerivative_le default)
  change ‖f.1‖ ≤ ‖f.topDerivative default‖
  apply norm_prod_le_iff.mpr
  constructor
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro a
    have ha : a = (default : MultiIndex.Top n 0).1 := Subsingleton.elim _ _
    change ‖f.derivative a‖ ≤ _
    rw [ha, ← topDerivative_toBoundedContinuousFunction]
    exact (f.topDerivative default).norm_toBoundedContinuousFunction_le
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro a
    rw [Subsingleton.elim a default]
    exact le_rfl

/-- Order zero recovers `C0GammaOn` as a real Banach space, with exactly the same norm. -/
def orderZeroLinearIsometryEquiv :
    CKGammaOn n 0 Ω γ ≃ₗᵢ[ℝ] C0GammaOn (closure Ω) γ where
  toFun f := f.topDerivative default
  invFun := ofOrderZero
  left_inv f := by
    apply ext_of_eqOn
    intro x hx
    rw [interiorDerivative_apply _ _ (subset_closure hx),
      interiorDerivative_apply _ _ (subset_closure hx)]
    change (f.topDerivative default).toBoundedContinuousFunction ⟨x, subset_closure hx⟩ =
      f.derivative 0 ⟨x, subset_closure hx⟩
    rw [topDerivative_toBoundedContinuousFunction]
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' f := f.norm_orderZero.symm

/-- At order zero, `evansNorm` (the norm (3) of Evans §5.1, which for `k = 0` is
`‖u‖_{C(Ū)} + [u]_{C^{0,γ}(Ū)}`) equals the Hölder norm of the image in `C0GammaOn`. -/
theorem evansNorm_orderZero (f : CKGammaOn n 0 Ω γ) :
    f.evansNorm = ‖orderZeroLinearIsometryEquiv f‖ := by
  simp only [evansNorm, Finset.univ_unique, Finset.sum_singleton]
  change ‖f.derivative default‖ + (f.topDerivative default).holderSeminorm =
    ‖f.topDerivative default‖
  rw [C0GammaOn.norm_def, topDerivative_toBoundedContinuousFunction]
  rfl

end HolderSpace.CKGammaOn
