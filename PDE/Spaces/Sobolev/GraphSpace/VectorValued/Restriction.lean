/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Restriction
public import PDE.Spaces.Sobolev.Foundations.VectorValued.Duality
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Notation
import PDE.Analysis.Normed.PiLp.Coordinatewise

/-!
# Restriction of Banach-valued Sobolev graphs

Restriction of the underlying measure acts continuously on each derivative coordinate.
The scalar weak restriction theorem, tested by the continuous dual, preserves the vector
graph relation. Restriction is a contraction for every derivative order and every
`1 ≤ p ≤ ∞`, and successive restrictions agree with direct restriction.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω Ω' : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Weak derivatives restrict to every smaller open domain. -/
theorem HasWeakDerivativeOn.restrict {α : List (Fin n)} {f g : ℝ^n → F}
    (h : HasWeakDerivativeOn Ω α f g) (hΩ : Ω' ≤ Ω) :
    HasWeakDerivativeOn Ω' α f g := by
  apply (hasWeakDerivativeOn_iff_forall_dual
    (h.locallyIntegrable_f.mono_set hΩ) (h.locallyIntegrable_g.mono_set hΩ)).mpr
  intro L
  exact (hasWeakDerivativeOn_real_iff.mp (h.map L)).mono Ω'.isOpen.measurableSet hΩ

/-- Restrict each `Lp` derivative coordinate to the smaller open domain. -/
def restrictAmbientCLM (hΩ : Ω' ≤ Ω) :
    WkpAmbientOn n k p Ω F →L[ℝ] WkpAmbientOn n k p Ω' F :=
  (PiLp.continuousLinearEquiv p ℝ
    (fun _ : DerivIndex n k ↦ Lp F p (domainMeasure n Ω'))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a ↦
      (Lp.restrictionCLMOfLE (E := F) (p := p)
        (Measure.restrict_mono hΩ le_rfl)).comp
          (PiLp.proj p (fun _ : DerivIndex n k ↦ Lp F p (domainMeasure n Ω)) a))

omit [CompleteSpace F] in
/-- A restricted derivative coordinate is Mathlib's restriction of its `Lp` class. -/
@[simp] theorem restrictAmbientCLM_apply (hΩ : Ω' ≤ Ω)
    (U : WkpAmbientOn n k p Ω F) (a : DerivIndex n k) :
    restrictAmbientCLM hΩ U a =
      Lp.restrictionCLMOfLE (Measure.restrict_mono hΩ le_rfl) (U a) :=
  rfl

omit [CompleteSpace F] in
/-- Every restricted ambient coordinate agrees almost everywhere with the original. -/
theorem restrictAmbientCLM_apply_ae (hΩ : Ω' ≤ Ω)
    (U : WkpAmbientOn n k p Ω F) (a : DerivIndex n k) :
    (restrictAmbientCLM hΩ U a : ℝ^n → F) =ᵐ[domainMeasure n Ω'] U a :=
  Lp.restrictionCLMOfLE_apply_ae (Measure.restrict_mono hΩ le_rfl) (U a)

/-- Restriction is a continuous linear map between Banach-valued Sobolev graphs. -/
def restrictCLM (hΩ : Ω' ≤ Ω) :
    W^{k,p}(Ω; F) →L[ℝ] W^{k,p}(Ω'; F) :=
  ((restrictAmbientCLM hΩ).comp (wkpSubmoduleOn n k p Ω F).subtypeL).codRestrict
    (wkpSubmoduleOn n k p Ω' F) (fun U a ↦
      ((U.property a).restrict hΩ).congr_ae
        (restrictAmbientCLM_apply_ae hΩ U.val (baseIndex n k)).symm
        (restrictAmbientCLM_apply_ae hΩ U.val a).symm)

/-- Sobolev restriction preserves each represented derivative on the smaller domain. -/
theorem restrictCLM_apply_ae (hΩ : Ω' ≤ Ω) (U : W^{k,p}(Ω; F))
    (a : DerivIndex n k) :
    ((restrictCLM hΩ U).val a : ℝ^n → F) =ᵐ[domainMeasure n Ω'] U.val a :=
  restrictAmbientCLM_apply_ae hΩ U.val a

/-- Restriction does not increase the Sobolev norm, including at both exponent endpoints. -/
theorem norm_restrictCLM_apply_le (hΩ : Ω' ≤ Ω) (U : W^{k,p}(Ω; F)) :
    ‖restrictCLM hΩ U‖ ≤ ‖U‖ :=
  PiLp.norm_mono _ _ fun _ ↦
    Lp.norm_restrictionCLMOfLE_apply_le (Measure.restrict_mono hΩ le_rfl) _

/-- The restriction operator has norm at most one. -/
theorem norm_restrictCLM_le (hΩ : Ω' ≤ Ω) :
    ‖restrictCLM (F := F) (k := k) (p := p) hΩ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro U
  simpa only [one_mul] using norm_restrictCLM_apply_le hΩ U

/-- Restricting to the same open domain leaves a Sobolev function unchanged. -/
@[simp] theorem restrictCLM_refl :
    restrictCLM (F := F) (k := k) (p := p) (le_refl Ω) =
      ContinuousLinearMap.id ℝ W^{k,p}(Ω; F) := by
  ext U : 1
  apply WkpSpaceOn.ext_of_base_ae
  exact restrictCLM_apply_ae (le_refl Ω) U (baseIndex n k)

/-- Restricting through an intermediate open domain agrees with direct restriction. -/
theorem restrictCLM_trans {Ω'' : Opens ℝ^n} (h₁ : Ω'' ≤ Ω') (h₂ : Ω' ≤ Ω) :
    (restrictCLM (F := F) (k := k) (p := p) h₁).comp (restrictCLM h₂) =
      restrictCLM (h₁.trans h₂) := by
  ext U : 1
  apply WkpSpaceOn.ext_of_base_ae
  have hinner :
      ((restrictCLM h₂ U).val (baseIndex n k) : ℝ^n → F) =ᵐ[domainMeasure n Ω'']
        U.val (baseIndex n k) :=
    ae_mono (Measure.restrict_mono h₁ le_rfl)
      (restrictCLM_apply_ae h₂ U (baseIndex n k))
  exact (restrictCLM_apply_ae h₁ (restrictCLM h₂ U) (baseIndex n k)).trans
    (hinner.trans
      (restrictCLM_apply_ae (h₁.trans h₂) U (baseIndex n k)).symm)

end SobolevSpace.VectorValued
