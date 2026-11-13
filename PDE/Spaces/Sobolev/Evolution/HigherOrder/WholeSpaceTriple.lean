/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.Triple
public import PDE.Spaces.Sobolev.GraphSpace.Topology.OrderDensity
public import PDE.Spaces.Sobolev.Calculus.Slicing.HigherOrder
import PDE.Spaces.Sobolev.GraphSpace.Norms
import PDE.Spaces.Sobolev.Calculus.Product.FirstOrder

/-!
# The whole-space Sobolev triple with H¹ pivot

The dense inclusion `H²(ℝⁿ) → H¹(ℝⁿ)` is a Gelfand triple. Its energy map
factors through `L²(ℝⁿ)`: integration by parts transfers the derivatives
in the H¹ pairing to the H² test function. This is the spatial identity
behind time continuity for an H² trajectory with an L² time derivative.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory PDE.Analysis.Evolution
open scoped ENNReal InnerProductSpace Sobolev

variable {n : ℕ}

/-- The dense whole-space inclusion from H² into the H¹ pivot space. -/
def hTwoHOneTriple (n : ℕ) :
    GelfandTriple (V := W^{2,2}(ℝ^n)) (H := W^{1,2}(ℝ^n)) where
  inclusion := lowerOrderCLM (by omega)
  injective := lowerOrderCLM_injective (by omega) isOpen_univ
  denseRange := denseRange_lowerOrderCLM (by omega) (by norm_num)

/-- The bounded map `v ↦ v - Δv` from H² to L². -/
def identitySubLaplacianCLM (n : ℕ) : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 Set.univ :=
  wkpBaseCoordinateCLM - ∑ i : Fin n, wkpCoordinateCLM (pairDerivIndex n i i)

/-- An L² function acts on H² by pairing against `v - Δv`. -/
def lTwoToHTwoDual (n : ℕ) : DerivLp n 2 Set.univ →L[ℝ] StrongDual ℝ (W^{2,2}(ℝ^n)) :=
  ContinuousLinearMap.toSesqForm (identitySubLaplacianCLM n)

/-- Whole-space integration by parts identifies the H¹ pairing with `v - Δv`. -/
theorem inner_lowerOrder_eq_identitySubLaplacian (U V : W^{2,2}(ℝ^n)) :
    ⟪lowerOrderCLM (show 1 ≤ 2 by omega) U,
      lowerOrderCLM (show 1 ≤ 2 by omega) V⟫_ℝ =
      ⟪wkpBaseCoordinateCLM U, identitySubLaplacianCLM n V⟫_ℝ := by
  let u : W^{1,2}(ℝ^n) := lowerOrderCLM (by omega) U
  have hu : u ∈ (h10SubmoduleOn (n := n) (Ω := Set.univ)).toSubmodule := by
    simpa [h10SubmoduleOn] using wkpSpace_mem_Wkp0_univ (by norm_num) u
  have hparts (i : Fin n) :
      ⟪U.val (firstDerivIndex n 2 (by omega) i),
        V.val (firstDerivIndex n 2 (by omega) i)⟫_ℝ =
        -⟪wkpBaseCoordinateCLM U, V.val (pairDerivIndex n i i)⟫_ℝ := by
    have hweak := V.property.hasWeakDerivativeOn_from_coordinate [i] [i]
      (by simp)
    have h := weakDerivative_integrationByParts_H10 i
      (V.val (firstDerivIndex n 2 (by omega) i))
      (V.val (pairDerivIndex n i i))
      (by simpa only [List.cons_append, List.nil_append, derivIndexOfList_singleton,
        derivIndexOfList_pair, secondDerivIndex_two] using hweak) ⟨u, hu⟩
    simpa [derivCoordCLM, baseCoordCLM, u, lowerOrderCLM_apply,
      real_inner_comm] using h
  change inner ℝ (lowerOrderCLM (show 1 ≤ 2 by omega) U).val
    (lowerOrderCLM (show 1 ≤ 2 by omega) V).val = _
  rw [ambient_inner_eq_base_add_sum_deriv]
  have heval : identitySubLaplacianCLM n V = wkpBaseCoordinateCLM V -
      ∑ i : Fin n, V.val (pairDerivIndex n i i) := by
    simp [identitySubLaplacianCLM, sub_apply, sum_apply]
  rw [heval, inner_sub_right, inner_sum]
  simp only [lowerOrderCLM_apply, DerivIndex.castOrder_baseIndex,
    DerivIndex.castOrder_singleDerivIndex, hparts, wkpBaseCoordinateCLM_apply,
    Finset.sum_neg_distrib, sub_eq_add_neg]

/-- The Gelfand energy map factors through the L² base coordinate. -/
theorem hTwoHOneTriple_energyToDual (U : W^{2,2}(ℝ^n)) :
    (hTwoHOneTriple n).energyToDual U = lTwoToHTwoDual n (wkpBaseCoordinateCLM U) := by
  ext V
  exact inner_lowerOrder_eq_identitySubLaplacian U V

end SobolevSpace.GraphSpace
