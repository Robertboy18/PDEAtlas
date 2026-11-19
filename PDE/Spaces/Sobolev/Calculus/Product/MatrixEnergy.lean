/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Product.IntegrationByParts

/-!
# Symmetric matrix integration by parts

A finite symmetric W¹,∞ matrix acting on one coordinate derivative has a
quadratic bound determined by the coefficient derivative. These spatial
identities apply to whole-space H¹ fields without compact support.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal InnerProductSpace Sobolev

variable {n : ℕ}

/-- For a symmetric matrix of W1,infinity coefficients, the transport energy in one spatial
coordinate equals half the quadratic pairing with the differentiated coefficient matrix.
Symmetry is required only of the base coefficient rows, as equality of L-infinity classes. -/
theorem symmetric_matrix_transport_energy_identity {ι : Type*} [Fintype ι]
    (A : ι → ι → W^{1,∞}(ℝ^n))
    (hA : ∀ p q, (A p q : WkpAmbientOn n 1 ∞ Set.univ) (baseIndex n 1) =
      (A q p : WkpAmbientOn n 1 ∞ Set.univ) (baseIndex n 1))
    (i : Fin n) (U : ι → W^{1,2}(ℝ^n)) :
    let u := fun p ↦ (U p : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1);
    let du := fun p ↦ (U p : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i);
    let a := fun p q ↦ (A p q : WkpAmbientOn n 1 ∞ Set.univ) (baseIndex n 1);
    let da := fun p q ↦ (A p q : WkpAmbientOn n 1 ∞ Set.univ) (singleDerivIndex n i);
    -(∑ p, ∑ q, ⟪a p q • du q, u p⟫_ℝ) =
      (1 / 2 : ℝ) * ∑ p, ∑ q, ⟪da p q • u q, u p⟫_ℝ := by
  classical
  let u := fun p ↦ (U p : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1)
  let du := fun p ↦ (U p : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i)
  let a := fun p q ↦ (A p q : WkpAmbientOn n 1 ∞ Set.univ) (baseIndex n 1)
  let da := fun p q ↦ (A p q : WkpAmbientOn n 1 ∞ Set.univ) (singleDerivIndex n i)
  change -(∑ p, ∑ q, ⟪a p q • du q, u p⟫_ℝ) =
    (1 / 2 : ℝ) * ∑ p, ∑ q, ⟪da p q • u q, u p⟫_ℝ
  have hswap :
      (∑ p, ∑ q, ⟪a p q • du p, u q⟫_ℝ) =
        ∑ p, ∑ q, ⟪a p q • du q, u p⟫_ℝ := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    rw [show a q p = a p q from hA q p]
  have hsum :
      (∑ p, ∑ q, ⟪a p q • du q, u p⟫_ℝ) +
        (∑ p, ∑ q, ⟪a p q • du p, u q⟫_ℝ) =
          -(∑ p, ∑ q, ⟪da p q • u q, u p⟫_ℝ) := by
    calc
      _ = ∑ p, ∑ q, (⟪a p q • du q, u p⟫_ℝ + ⟪a p q • du p, u q⟫_ℝ) := by
        simp only [Finset.sum_add_distrib]
      _ = ∑ p, ∑ q, -⟪da p q • u q, u p⟫_ℝ := by
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro q _
        exact inner_mul_deriv_add_inner_mul_deriv_univ (A p q) i (U q) (U p)
      _ = -(∑ p, ∑ q, ⟪da p q • u q, u p⟫_ℝ) := by
        simp only [Finset.sum_neg_distrib]
  rw [hswap] at hsum
  linarith only [hsum]

/-- Symmetric first-order transport has an energy bound depending only on the bounded
coefficient derivatives and the squared L2 norms of the fields, not their H1 norms. -/
theorem symmetric_matrix_transport_energy_le {ι : Type*} [Fintype ι]
    (A : ι → ι → W^{1,∞}(ℝ^n))
    (hA : ∀ p q, (A p q : WkpAmbientOn n 1 ∞ Set.univ) (baseIndex n 1) =
      (A q p : WkpAmbientOn n 1 ∞ Set.univ) (baseIndex n 1))
    (i : Fin n) (U : ι → W^{1,2}(ℝ^n)) :
    let u := fun p ↦ (U p : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1);
    let du := fun p ↦ (U p : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i);
    let a := fun p q ↦ (A p q : WkpAmbientOn n 1 ∞ Set.univ) (baseIndex n 1);
    let da := fun p q ↦ (A p q : WkpAmbientOn n 1 ∞ Set.univ) (singleDerivIndex n i);
    -(∑ p, ∑ q, ⟪a p q • du q, u p⟫_ℝ) ≤
      (1 / 2 : ℝ) * (∑ p, ∑ q, ‖da p q‖) * (∑ p, ‖u p‖ ^ 2) := by
  classical
  let u := fun p ↦ (U p : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1)
  let du := fun p ↦ (U p : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i)
  let a := fun p q ↦ (A p q : WkpAmbientOn n 1 ∞ Set.univ) (baseIndex n 1)
  let da := fun p q ↦ (A p q : WkpAmbientOn n 1 ∞ Set.univ) (singleDerivIndex n i)
  change -(∑ p, ∑ q, ⟪a p q • du q, u p⟫_ℝ) ≤
    (1 / 2 : ℝ) * (∑ p, ∑ q, ‖da p q‖) * (∑ p, ‖u p‖ ^ 2)
  calc
    _ = (1 / 2 : ℝ) * ∑ p, ∑ q, ⟪da p q • u q, u p⟫_ℝ :=
      symmetric_matrix_transport_energy_identity A hA i U
    _ ≤ (1 / 2 : ℝ) * ((∑ p, ∑ q, ‖da p q‖) * (∑ p, ‖u p‖ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (le_abs_self _).trans (MeasureTheory.Lp.abs_sum_inner_lpSMul_le da u)
    _ = (1 / 2 : ℝ) * (∑ p, ∑ q, ‖da p q‖) * (∑ p, ‖u p‖ ^ 2) :=
      (mul_assoc _ _ _).symm

end SobolevSpace.GraphSpace
