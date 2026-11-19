/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.C1.Assembly.Operator
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Laplacian
import PDE.Spaces.Sobolev.Calculus.Composition.AbsoluteValue
import PDE.Spaces.Sobolev.Calculus.Composition.DomainCore

/-!
# Weak derivatives on level sets

Extension transfers Stampacchia's zero-set theorem to a domain with a C¹
extension atlas. Applying it again to the first derivatives of an H² field
shows that its Laplacian vanishes almost everywhere on its zero set. Hence two
H² fields have equal Laplacians almost everywhere on their coincidence set.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev Laplacian

namespace SobolevSpace.GraphSpace

section Coincidence

variable {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n}
  [H : Boundary.C1ExtensionAtlas n Ω]

/-- The weak derivative of a domain `H¹` field vanishes almost everywhere
on its zero set, by extension and the whole-space level-set theorem. -/
theorem derivative_eq_zero_ae_on_zero_set (U : H¹(Ω)) (i : Fin n) :
    ∀ᵐ x ∂domainMeasure n Ω, wkpBaseCoordinateCLM U x = 0 →
      wkpCoordinateCLM (singleDerivIndex n i) U x = 0 := by
  have hmeasure : domainMeasure n Ω ≤ domainMeasure n univ := by
    simp only [domainMeasure, Measure.restrict_univ]
    exact Measure.restrict_le_self
  have hz := (derivative_eq_zero_ae_of_base_eq_zero (Extension.C1.extensionCLM U) i).filter_mono
      (ae_mono hmeasure)
  have hb := DomainComposition.extension_coordinate_ae H.isOpen Extension.C1.operator
    U (baseIndex n 1)
  have hd := DomainComposition.extension_coordinate_ae H.isOpen Extension.C1.operator
    U (singleDerivIndex n i)
  simp only [Extension.C1.operator] at hb hd
  filter_upwards [hz, hb, hd] with x hx hbx hdx
  intro hu
  exact hdx.symm.trans (hx (hbx.trans hu))

/-- An `H²` field has zero weak Laplacian almost everywhere on its zero set.
No openness of the zero set is required. -/
theorem laplacian_eq_zero_ae_on_zero_set (U : W^{2,2}(Ω)) :
    ∀ᵐ x ∂domainMeasure n Ω, wkpBaseCoordinateCLM U x = 0 → (Δ U) x = 0 := by
  have hfirst (i : Fin n) :
      ∀ᵐ x ∂domainMeasure n Ω, wkpBaseCoordinateCLM U x = 0 →
        (U : WkpAmbientOn n 2 2 Ω) (firstDerivIndex n 2 (by omega) i) x = 0 := by
    have hz := derivative_eq_zero_ae_on_zero_set
      (lowerOrderCLM (by norm_num : 1 ≤ 2) U) i
    simpa only [wkpBaseCoordinateCLM_apply, wkpCoordinateCLM_apply, lowerOrderCLM_apply,
      DerivIndex.castOrder_baseIndex, DerivIndex.castOrder_singleDerivIndex] using hz
  have hsecond (i : Fin n) :
      ∀ᵐ x ∂domainMeasure n Ω,
        (U : WkpAmbientOn n 2 2 Ω) (firstDerivIndex n 2 (by omega) i) x = 0 →
        (U : WkpAmbientOn n 2 2 Ω) (pairDerivIndex n i i) x = 0 := by
    have hz := derivative_eq_zero_ae_on_zero_set (derivativeSlice [i] (by simp) U) i
    simpa [wkpBaseCoordinateCLM_apply, wkpCoordinateCLM_apply,
      derivativeSliceIndex, derivIndexOfList_singleton, derivIndexOfList_pair,
      secondDerivIndex_two] using hz
  filter_upwards [ae_all_iff.mpr hfirst, ae_all_iff.mpr hsecond, wkpLaplacianCLM_coeFn U]
    with x h₁ h₂ hΔ
  intro hu
  change wkpLaplacianCLM U x = 0
  rw [hΔ]
  exact Finset.sum_eq_zero fun i _ ↦ h₂ i (h₁ i hu)

/-- Two `H²` fields have equal Laplacians almost everywhere on their coincidence set. -/
theorem laplacian_eq_ae_on_coincidence_set (U V : W^{2,2}(Ω)) :
    ∀ᵐ x ∂domainMeasure n Ω,
      wkpBaseCoordinateCLM U x = wkpBaseCoordinateCLM V x → (Δ U) x = (Δ V) x := by
  have hz := laplacian_eq_zero_ae_on_zero_set (U - V)
  have hb : (wkpBaseCoordinateCLM (U - V) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦ wkpBaseCoordinateCLM U x - wkpBaseCoordinateCLM V x := by
    rw [map_sub]
    exact Lp.coeFn_sub _ _
  have hd : ((Δ (U - V) : DerivLp n 2 Ω) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦ (Δ U) x - (Δ V) x := by
    simp only [laplacian_eq_wkpLaplacianCLM, map_sub]
    exact Lp.coeFn_sub _ _
  filter_upwards [hz, hb, hd] with x hx hbx hdx
  intro hu
  exact sub_eq_zero.mp (hdx.symm.trans (hx (hbx.trans (sub_eq_zero.mpr hu))))

end Coincidence

end SobolevSpace.GraphSpace
