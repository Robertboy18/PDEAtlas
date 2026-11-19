/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.Regularity.IntegratedTime
public import PDE.Spaces.Sobolev.Calculus.Product.IntegrationByParts

/-!
# Weighted cancellation of the weak wave operator

The H² Laplacian and the H¹ velocity satisfy the localized energy cancellation
for every W¹,infinity weight. The remaining spatial term differentiates only
the weight. This uses the Sobolev multiplier and weak integration by
parts, with no classical representative or compact support hypothesis.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace

variable {n : ℕ}

/-- The weighted Laplacian pairing cancels the differentiated velocity pairing,
leaving only the spatial derivative of the weight. -/
theorem weighted_laplacian_pairing (χ : W^{1,∞}(ℝ^n))
    (U : W^{2,2}(ℝ^n)) (V : H¹(ℝ^n)) :
    let u := lowerOrderCLM (by decide : 1 ≤ 2) U
    let a := (χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)
    (∑ i : Fin n, ⟪a • wkpCoordinateCLM (singleDerivIndex n i) u,
        wkpCoordinateCLM (singleDerivIndex n i) V⟫_ℝ) +
      ⟪a • wkpLaplacianCLM U, wkpBaseCoordinateCLM V⟫_ℝ =
      -(∑ i : Fin n, ⟪(χ : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n i) •
        wkpCoordinateCLM (singleDerivIndex n i) u, wkpBaseCoordinateCLM V⟫_ℝ) := by
  let u := lowerOrderCLM (by decide : 1 ≤ 2) U
  let a := (χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)
  have h := gradientForm_h2 U (w1TopMultiplierCLM isOpen_univ χ V)
  rw [gradientForm_apply] at h
  simp only [energyTriple, wkpBaseCoordinateCLM_apply,
    w1TopMultiplierCLM_apply_coe, w1TopMultiplierAmbient_base,
    w1TopMultiplierAmbient_singleDeriv, laplacian_eq_wkpLaplacianCLM] at h
  change (∑ i : Fin n, ⟪wkpCoordinateCLM (singleDerivIndex n i) u,
      a • wkpCoordinateCLM (singleDerivIndex n i) V +
        (χ : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n i) • wkpBaseCoordinateCLM V⟫_ℝ) =
    -⟪wkpLaplacianCLM U, a • wkpBaseCoordinateCLM V⟫_ℝ at h
  simp only [inner_add_right, ← Lp.inner_lpSMul_left, Finset.sum_add_distrib] at h
  dsimp only
  linarith only [h]

/-- The weighted spatial cancellation applies to the full-jet reaction,
including differences of two states. Only the two L² reaction values enter. -/
theorem weighted_wave_pairing (χ : W^{1,∞}(ℝ^n))
    (U : W^{2,2}(ℝ^n)) (V : H¹(ℝ^n)) (r : DerivLp n 2 univ) :
    let u := lowerOrderCLM (by decide : 1 ≤ 2) U
    let a := (χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)
    (∑ i : Fin n, ⟪a • wkpCoordinateCLM (singleDerivIndex n i) u,
        wkpCoordinateCLM (singleDerivIndex n i) V⟫_ℝ) +
      ⟪a • (wkpLaplacianCLM U - r), wkpBaseCoordinateCLM V⟫_ℝ +
      ⟪a • wkpBaseCoordinateCLM U, wkpBaseCoordinateCLM V⟫_ℝ =
      ⟪a • (wkpBaseCoordinateCLM U - r), wkpBaseCoordinateCLM V⟫_ℝ -
        ∑ i : Fin n, ⟪(χ : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n i) •
          wkpCoordinateCLM (singleDerivIndex n i) u, wkpBaseCoordinateCLM V⟫_ℝ := by
  have h := weighted_laplacian_pairing χ U V
  dsimp only at h ⊢
  simp only [sub_eq_add_neg, Lp.add_smul, Lp.smul_neg, inner_add_left, inner_neg_left]
  linarith only [h]

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
