/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Constant.Derivative
import PDE.Elliptic.Regularity.Interior.DivergenceForm.H2
import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity

/-!
# Interior gradient equations from H¹ constant coefficient data

Interior H² regularity constructs the first derivatives as H¹ fields. Their
homogeneous weak equations follow by differentiating the original equation.
This supplies weak solutions to which uniform energy and local
boundedness estimates can be applied, without an H² assumption on the input.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace
open scoped Sobolev ENNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω V : Set (ℝ^n)}

/-- A raw H¹ constant coefficient solution has an H² lift on each relatively
compact open set, and its first derivatives solve the same equation there.
Both regularity and the differentiated weak equations are conclusions. -/
theorem exists_interior_gradient_solutions_of_constant_coefficients
    (A : Fin n → Fin n → DerivLp n ∞ Ω) (a : Fin n → Fin n → ℝ)
    (hrep : ∀ i j, (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun _ ↦ a i j)
    {α : ℝ} (hA : AEUniformlyElliptic A α)
    (u : H¹(Ω)) (hu : IsInteriorWeakDivergenceSolution A 0 u)
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω) :
    ∃ W : W^{2,2}(V),
      lowerOrderCLM (by omega : 1 ≤ 2) W =
        restrictCLM hV.measurableSet (subset_closure.trans hVΩ) u ∧
      ∀ k, IsInteriorWeakDivergenceSolution
        (fun i j ↦ restrictDerivLp (subset_closure.trans hVΩ) (A i j)) 0 (∂[k] W) := by
  have hfull : IsInteriorWeakFullDivergenceSolution A (fun _ ↦ 0) 0 0 u := by
    apply (isInteriorWeakFullDivergenceSolution_iff _ _ _ _ _).mpr
    simpa only [interiorLowerOrderOperator_apply, Lp.zero_smul,
      Finset.sum_const_zero, zero_add, sub_zero] using hu
  obtain ⟨W, hW⟩ := exists_interior_h2_of_contDiffOn hu.isOpen A
    (fun i j _ ↦ a i j) (fun _ _ ↦ contDiffOn_const) hrep hA
    (fun _ ↦ 0) 0 0 u hfull hV hVc hVΩ
  have hWlower : lowerOrderCLM (by omega : 1 ≤ 2) W =
      restrictCLM hV.measurableSet (subset_closure.trans hVΩ) u := by
    apply wkpBaseCoordinateCLM_injective hV
    rw [wkpBaseCoordinateCLM_restrictCLM]
    simpa only [wkpBaseCoordinateCLM_apply, lowerOrderCLM_apply,
      DerivIndex.castOrder_baseIndex] using hW
  refine ⟨W, hWlower, ?_⟩
  intro k
  apply IsInteriorWeakDivergenceSolution.partialDeriv_of_constant_representatives
    (fun i j ↦ restrictDerivLp (subset_closure.trans hVΩ) (A i j)) a
    (fun i j ↦ (restrictDerivLp_apply_ae (subset_closure.trans hVΩ) (A i j)).trans
      ((hrep i j).filter_mono (ae_mono (domainMeasure_le (subset_closure.trans hVΩ))))) W
  rw [hWlower]
  simpa only [map_zero] using hu.restrict hV (subset_closure.trans hVΩ)

end SobolevSpace.GraphSpace
