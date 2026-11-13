/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.Triple
public import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity
public import PDE.Spaces.Sobolev.Calculus.IntegrationByParts.LaplacianH10

/-!
# The H¹–L² triple and whole-space weak Laplacian

The H¹ base-coordinate map is a dense inclusion on every open domain.
The negative gradient pairing defines a bounded map from H¹ to its dual.
On the whole space this map agrees with the L² Laplacian for H² data,
by integration by parts against arbitrary H¹ functions.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory PDE.Analysis.Evolution
open scoped ENNReal InnerProductSpace Sobolev Laplacian

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The dense base-coordinate inclusion of H¹ into L² on an open domain. -/
def hOneLTwoGelfandTriple (hΩ : IsOpen Ω) :
    GelfandTriple (V := W^{1,2}(Ω)) (H := DerivLp n 2 Ω) where
  inclusion := wkpBaseCoordinateCLM
  injective := wkpBaseCoordinateCLM_injective hΩ
  denseRange := (baseCoordCLM_denseRange hΩ).mono (by
    rintro y ⟨v, rfl⟩
    exact ⟨h10SubtypeL v, rfl⟩)

/-- The bounded weak Laplacian defined by the negative gradient pairing. -/
def weakLaplacianCLM : W^{1,2}(Ω) →L[ℝ] StrongDual ℝ (W^{1,2}(Ω)) :=
  -∑ i : Fin n, (ContinuousLinearMap.toSesqForm
    (wkpCoordinateCLM (singleDerivIndex n i))).comp
      (wkpCoordinateCLM (singleDerivIndex n i))

/-- The weak Laplacian pairs as minus the inner product of the gradients. -/
theorem weakLaplacianCLM_apply (U V : W^{1,2}(Ω)) :
    weakLaplacianCLM U V = -∑ i : Fin n,
      ⟪wkpCoordinateCLM (singleDerivIndex n i) U,
        wkpCoordinateCLM (singleDerivIndex n i) V⟫_ℝ := by
  simp [weakLaplacianCLM, ContinuousLinearMap.toSesqForm_apply_coe]

/-- The weak Laplacian is dissipative in the pairing between H¹ and its dual. -/
theorem weakLaplacianCLM_apply_self_nonpos (U : W^{1,2}(Ω)) :
    weakLaplacianCLM U U ≤ 0 := by
  rw [weakLaplacianCLM_apply, neg_nonpos]
  exact Finset.sum_nonneg fun _ _ ↦ real_inner_self_nonneg

/-- On the whole space the H¹ dual Laplacian of H² data is the canonical
embedding of its actual L² Laplacian. -/
theorem weakLaplacianCLM_lowerOrder_univ (U : W^{2,2}(ℝ^n)) :
    weakLaplacianCLM (lowerOrderCLM (show 1 ≤ 2 by omega) U) =
      (hOneLTwoGelfandTriple isOpen_univ).pivotToDual (Δ U) := by
  ext V
  have hV : V ∈ (h10SubmoduleOn (n := n) (Ω := Set.univ)).toSubmodule := by
    simpa [h10SubmoduleOn] using wkpSpace_mem_Wkp0_univ (by norm_num) V
  have h := sum_inner_gradient_eq_neg_inner_laplacian U ⟨V, hV⟩
  rw [weakLaplacianCLM_apply]
  change -(∑ i, inner ℝ
    (wkpCoordinateCLM (singleDerivIndex n i) (lowerOrderCLM (by omega) U))
      (derivCoordCLM i ⟨V, hV⟩)) = inner ℝ (Δ U) (baseCoordCLM ⟨V, hV⟩)
  rw [h, neg_neg]

end SobolevSpace.GraphSpace
