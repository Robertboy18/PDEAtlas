/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Product.LocalizedMixed
public import PDE.Spaces.Sobolev.Calculus.Differentiation.SecondDerivatives.Assembly
import PDE.Spaces.Sobolev.Variational.Spaces.ZeroBoundaryCoordinates

/-!
# Second-order assembly after localizing the gradient

If each component of `η Du` is first-order Sobolev, then so is each component
of `D(ηu) = η Du + (Dη)u`. The second-derivative constructor therefore
gives an `H²` representative of `ηu`. No trace or boundary geometry is used.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Distributions Sobolev

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Second-order assembly with the same base representative as
the cutoff and a bound from the localized gradient fields. The
estimate uses one canonical representative per second-order index. -/
theorem exists_H2_cutoff_of_localized_gradient_H1
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (U : H¹(Ω))
    (W : Fin n → H¹(Ω))
    (hW : ∀ i, (W i).val (baseIndex n 1) =
      testFunctionLpTop (Ω := Ω) η • U.val (singleDerivIndex n i)) :
    ∃ V : W^{2,2}(Ω),
      V.val (baseIndex n 2) = (cutoffCLM η U).val (baseIndex n 1) ∧
      ‖V‖ ≤ Fintype.card (DerivIndex n 2) *
        (‖cutoffCLM (p := 2) (Ω := Ω) η‖ * ‖U‖ +
          ∑ i : Fin n, (‖W i‖ + ‖cutoffCLM (p := 2) (Ω := Ω)
            (_root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i 1) η)‖ * ‖U‖)) := by
  let Z (i : Fin n) := W i + cutoffCLM
    (_root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i 1) η) U
  have hZ (i : Fin n) : (Z i).val (baseIndex n 1) =
      (cutoffCLM η U).val (singleDerivIndex n i) := by
    rw [cutoffCLM_singleDeriv_eq]
    change (W i).val (baseIndex n 1) + _ = _
    rw [hW]
    rfl
  obtain ⟨V, hV, _, hnorm⟩ := exists_H2_of_gradient_H1 (cutoffCLM η U) Z hZ
  refine ⟨V, ?_, ?_⟩
  · simpa only [lowerOrderCLM_apply, DerivIndex.castOrder_baseIndex] using
      congrArg (fun Q : H¹(Ω) ↦ Q.val (baseIndex n 1)) hV
  have hnormZ (i : Fin n) : ‖Z i‖ ≤ ‖W i‖ + ‖cutoffCLM (p := 2) (Ω := Ω)
      (_root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i 1) η)‖ * ‖U‖ :=
    (norm_add_le _ _).trans (add_le_add le_rfl ((cutoffCLM _).le_opNorm U))
  exact hnorm.trans (mul_le_mul_of_nonneg_left
      (add_le_add ((cutoffCLM η).le_opNorm U) (Finset.sum_le_sum fun i _ ↦
        (norm_wkpGradientCLM_apply_le (Z i)).trans (hnormZ i)))
      (Nat.cast_nonneg _))

end SobolevSpace.GraphSpace
