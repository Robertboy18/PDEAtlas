/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.HigherOrderRegularity
public import PDE.Spaces.Sobolev.Calculus.IntegrationByParts.WholeSpace

/-!
# Mollified whole-space heat generators

The bounded generator is the operator `Jδ Δ Jδ` on each finite-order
Sobolev space. Its dissipated energy controls derivatives of `Jδ U`. The
unmollified state `U` need not have those extra derivatives.

The smoothing scale `δ` is independent of the physical diffusion coefficient.
The latter multiplies this generator in the evolution equation.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Heat

open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation
open scoped ENNReal InnerProductSpace Laplacian Sobolev

variable {n r : ℕ}

/-- The bounded operator `Jδ Δ Jδ` on the native whole-space Hʳ graph. -/
def regularizedLaplacianCLM (r : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    W^{r,2}(ℝ^n) →L[ℝ] W^{r,2}(ℝ^n) :=
  (mollifierHkCLM (standardMollifier n) hδ).comp
    ((higherOrderLaplacianCLM (show r + 2 ≤ r + 2 by omega)).comp
      ((mollifierSmoothingCLM (r + 2) (standardMollifier n) hδ).comp
        wkpBaseCoordinateCLM))

/-- The base coordinate is the ordinary mollifier applied to the weak
Laplacian of the smoothed H² state. -/
theorem regularizedLaplacianCLM_base {δ : ℝ} (hδ : 0 < δ) (U : W^{r,2}(ℝ^n)) :
    wkpBaseCoordinateCLM (regularizedLaplacianCLM r hδ U) =
      mollifierRowCLM (standardMollifier n) hδ
        (Δ (mollifierSmoothingCLM 2 (standardMollifier n) hδ
          (wkpBaseCoordinateCLM U))) := by
  change mollifierRowCLM (standardMollifier n) hδ
    (wkpBaseCoordinateCLM
      (higherOrderLaplacianCLM (show r + 2 ≤ r + 2 by omega)
        (mollifierSmoothingCLM (r + 2) (standardMollifier n) hδ
          (wkpBaseCoordinateCLM U)))) = _
  rw [higherOrderLaplacianCLM_base, lowerOrderCLM_mollifierSmoothingCLM,
    laplacian_eq_wkpLaplacianCLM]

/-- Dissipation of the bounded regularization equals the derivative energy
of the smoothed state. This is an identity for every input Hʳ state. -/
theorem inner_regularizedLaplacianCLM {δ : ℝ} (hδ : 0 < δ) (U : W^{r,2}(ℝ^n)) :
    ⟪U, regularizedLaplacianCLM r hδ U⟫_ℝ =
      -(∑ a : DerivIndex n r, ∑ i : Fin n,
        ‖(mollifierSmoothingCLM (r + 2) (standardMollifier n) hδ
            (wkpBaseCoordinateCLM U) : WkpAmbientOn n (r + 2) 2 Set.univ)
          (derivIndexOfList (a.toList ++ [i]) (by
            simp only [List.length_append, List.length_singleton]
            have := a.toList_length_le
            omega))‖ ^ 2) := by
  simp only [regularizedLaplacianCLM, ContinuousLinearMap.comp_apply]
  rw [← inner_standardMollifierHkCLM_left]
  rw [← mollifierSmoothingCLM_baseCoordinate,
    ← lowerOrderCLM_mollifierSmoothingCLM (show r ≤ r + 2 by omega)]
  exact inner_higherOrderLaplacianCLM (show r + 2 ≤ r + 2 by omega) _

/-- The H¹ dissipation counts all ordered second derivatives of the smoothed
state, including both orders of mixed derivatives. -/
theorem inner_regularizedLaplacianCLM_one {δ : ℝ} (hδ : 0 < δ)
    (U : W^{1,2}(ℝ^n)) :
    ⟪U, regularizedLaplacianCLM 1 hδ U⟫_ℝ =
      -((∑ i : Fin n,
          ‖(mollifierSmoothingCLM 2 (standardMollifier n) hδ
              (wkpBaseCoordinateCLM U) : WkpAmbientOn n 2 2 Set.univ)
            (firstDerivIndex n 2 (by omega) i)‖ ^ 2) +
        ∑ i : Fin n, ∑ j : Fin n,
          ‖(mollifierSmoothingCLM 2 (standardMollifier n) hδ
              (wkpBaseCoordinateCLM U) : WkpAmbientOn n 2 2 Set.univ)
            (pairDerivIndex n i j)‖ ^ 2) := by
  have hc (a : DerivIndex n 2) :
      (mollifierSmoothingCLM 2 (standardMollifier n) hδ
          (wkpBaseCoordinateCLM U) : WkpAmbientOn n 2 2 Set.univ) a =
        (mollifierSmoothingCLM 3 (standardMollifier n) hδ
          (wkpBaseCoordinateCLM U) : WkpAmbientOn n 3 2 Set.univ)
          (a.castOrder (show 2 ≤ 3 by omega)) := by
    rw [← lowerOrderCLM_mollifierSmoothingCLM (show 2 ≤ 3 by omega)]
    rfl
  simp only [hc, DerivIndex.castOrder_pairDerivIndex,
    DerivIndex.castOrder_firstDerivIndex]
  simp only [regularizedLaplacianCLM, ContinuousLinearMap.comp_apply]
  rw [← inner_standardMollifierHkCLM_left,
    ← mollifierSmoothingCLM_baseCoordinate,
    ← lowerOrderCLM_mollifierSmoothingCLM (show 1 ≤ 3 by omega)]
  exact inner_hOne_laplacian_eq_neg_gradient_hessian _

/-- The native H² norm of `Jδ U` is controlled by the original H¹ norm and
the regularized dissipation. No H² bound on the original state is asserted. -/
theorem norm_mollifierSmoothingCLM_two_sq_le {δ : ℝ} (hδ : 0 < δ)
    (U : W^{1,2}(ℝ^n)) :
    ‖mollifierSmoothingCLM 2 (standardMollifier n) hδ
        (wkpBaseCoordinateCLM U)‖ ^ 2 ≤
      ‖U‖ ^ 2 - ⟪U, regularizedLaplacianCLM 1 hδ U⟫_ℝ := by
  have hnorm :
      ‖wkpBaseCoordinateCLM (mollifierSmoothingCLM 2 (standardMollifier n) hδ
        (wkpBaseCoordinateCLM U))‖ ≤ ‖U‖ := by
    rw [mollifierSmoothingCLM_base]
    exact (norm_mollifierRowCLM_apply_le _ _ _).trans
      (wkpBaseCoordinateCLM_norm_le U)
  have hsq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm
  have hh := ambient_norm_sq_le_base_add_first_add_hessian
    (mollifierSmoothingCLM 2 (standardMollifier n) hδ (wkpBaseCoordinateCLM U)).val
  rw [inner_regularizedLaplacianCLM_one]
  change _ ≤ ‖U‖ ^ 2 - _
  change ‖(mollifierSmoothingCLM 2 (standardMollifier n) hδ
    (wkpBaseCoordinateCLM U)).val (baseIndex n 2)‖ ^ 2 ≤ ‖U‖ ^ 2 at hsq
  change ‖mollifierSmoothingCLM 2 (standardMollifier n) hδ
    (wkpBaseCoordinateCLM U)‖ ^ 2 ≤ _ at hh
  linarith

end PDE.Parabolic.Heat
