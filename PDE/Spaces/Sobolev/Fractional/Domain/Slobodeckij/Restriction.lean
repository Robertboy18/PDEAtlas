/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Restriction
public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Notation

/-!
# Restriction of Sobolev–Slobodeckij graph spaces

Restriction to a smaller domain contracts both `Lᵖ` coordinates: the function and its
weighted difference on the domain square. It therefore contracts the `WithLp p` graph
norm, including its maximum-norm interpretation at infinity.

`GagliardoSpace.restrictCLM` commutes with the physical coordinates and with building an
element from a raw function. These restriction maps satisfy the identity and composition laws. The
construction works for arbitrary domains and real orders, with no completeness
assumption on the normed real codomain.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FractionalSobolev

namespace SobolevSpace.Fractional.GagliardoSpace

variable {n : ℕ} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Restricting the base coordinate preserves membership in the weighted-difference domain. -/
theorem restrict_toLp_mem_domain
    {Ω₁ Ω₂ : Set (ℝ^n)} (hΩ : Ω₁ ⊆ Ω₂)
    (u : W^{s,p}(Ω₂; F)) :
    Lp.restrictionCLMOfLE (Measure.restrict_mono hΩ le_rfl) (toLp n s Ω₂ u) ∈
      gagliardoDomain n s Ω₁ (p := p) (F := F) := by
  have hsource :
      MemLp (diffQuot n s (toLp n s Ω₂ u : ℝ^n → F) (p := p)) p
        (gagliardoProductMeasure n Ω₂) :=
    toLp_mem_domain u
  have hsourceSmall := hsource.mono_measure (gagliardoProductMeasure_mono hΩ)
  exact (memLp_congr_ae (diffQuot_congr_ae (n := n) (s := s) (Ω := Ω₁) (p := p)
    (Lp.restrictionCLMOfLE_apply_ae (Measure.restrict_mono hΩ le_rfl)
      (toLp n s Ω₂ u)))).2 hsourceSmall

/-- Restriction of Gagliardo-space elements to a subdomain as a linear map. -/
def restrictionLinearMap {Ω₁ Ω₂ : Set (ℝ^n)} (hΩ : Ω₁ ⊆ Ω₂) :
    W^{s,p}(Ω₂; F) →ₗ[ℝ]
      W^{s,p}(Ω₁; F) where
  toFun u := ofLp
    (Lp.restrictionCLMOfLE (Measure.restrict_mono hΩ le_rfl) (toLp n s Ω₂ u))
    (restrict_toLp_mem_domain hΩ u)
  map_add' u v := by
    apply toLp_injective
    simp
  map_smul' c u := by
    apply toLp_injective
    simp

private theorem differenceQuotient_restrictionLinearMap
    {Ω₁ Ω₂ : Set (ℝ^n)} (hΩ : Ω₁ ⊆ Ω₂)
    (u : W^{s,p}(Ω₂; F)) :
    differenceQuotient n s Ω₁ (restrictionLinearMap hΩ u) =
      Lp.restrictionCLMOfLE (gagliardoProductMeasure_mono hΩ)
        (differenceQuotient n s Ω₂ u) := by
  apply Lp.ext
  have hsourceSmall :
      (differenceQuotient n s Ω₂ u : ℝ^n × ℝ^n → F)
        =ᵐ[gagliardoProductMeasure n Ω₁]
          diffQuot n s (toLp n s Ω₂ u : ℝ^n → F) (p := p) :=
    ae_mono (gagliardoProductMeasure_mono hΩ) (differenceQuotient_apply_ae u)
  exact (differenceQuotient_apply_ae (restrictionLinearMap hΩ u)).trans
    ((diffQuot_congr_ae (n := n) (s := s) (Ω := Ω₁) (p := p)
      (Lp.restrictionCLMOfLE_apply_ae (Measure.restrict_mono hΩ le_rfl)
        (toLp n s Ω₂ u))).trans
      (hsourceSmall.symm.trans
        (Lp.restrictionCLMOfLE_apply_ae (gagliardoProductMeasure_mono hΩ)
          (differenceQuotient n s Ω₂ u)).symm))

private theorem norm_restrictionLinearMap_le
    {Ω₁ Ω₂ : Set (ℝ^n)} (hΩ : Ω₁ ⊆ Ω₂)
    (u : W^{s,p}(Ω₂; F)) :
    ‖restrictionLinearMap hΩ u‖ ≤ ‖u‖ := by
  have hbase :
      ‖toLp n s Ω₁ (restrictionLinearMap hΩ u)‖ ≤ ‖toLp n s Ω₂ u‖ :=
    Lp.norm_restrictionCLMOfLE_apply_le (Measure.restrict_mono hΩ le_rfl) _
  have hdifference :
      ‖differenceQuotient n s Ω₁ (restrictionLinearMap hΩ u)‖ ≤
        ‖differenceQuotient n s Ω₂ u‖ := by
    rw [differenceQuotient_restrictionLinearMap]
    exact Lp.norm_restrictionCLMOfLE_apply_le _ _
  by_cases hp : p = ∞
  · subst p
    rw [norm_top, norm_top]
    exact max_le_max hbase hdifference
  · have hp0 : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hp
    apply (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hp0).mp
    rw [norm_rpow_eq hp, norm_rpow_eq hp]
    exact add_le_add
      (Real.rpow_le_rpow (norm_nonneg _) hbase hp0.le)
      (Real.rpow_le_rpow (norm_nonneg _) hdifference hp0.le)

/-- Continuous restriction to a subdomain, with operator norm at most one. -/
def restrictCLM {Ω₁ Ω₂ : Set (ℝ^n)} (hΩ : Ω₁ ⊆ Ω₂) :
    W^{s,p}(Ω₂; F) →L[ℝ]
      W^{s,p}(Ω₁; F) :=
  LinearMap.mkContinuous (restrictionLinearMap hΩ) 1 fun u ↦ by
    simpa only [one_mul] using norm_restrictionLinearMap_le hΩ u

/-- Restriction acts on the base coordinate by the canonical `Lᵖ` restriction. -/
@[simp] theorem toLp_restrictCLM
    {Ω₁ Ω₂ : Set (ℝ^n)} (hΩ : Ω₁ ⊆ Ω₂)
    (u : W^{s,p}(Ω₂; F)) :
    toLp n s Ω₁ (restrictCLM hΩ u) =
      Lp.restrictionCLMOfLE (Measure.restrict_mono hΩ le_rfl) (toLp n s Ω₂ u) :=
  rfl

/-- Restriction acts on the weighted-difference coordinate by the canonical
`Lᵖ` restriction on the domain square. -/
theorem differenceQuotient_restrictCLM
    {Ω₁ Ω₂ : Set (ℝ^n)} (hΩ : Ω₁ ⊆ Ω₂)
    (u : W^{s,p}(Ω₂; F)) :
    differenceQuotient n s Ω₁ (restrictCLM hΩ u) =
      Lp.restrictionCLMOfLE (gagliardoProductMeasure_mono hΩ)
        (differenceQuotient n s Ω₂ u) :=
  differenceQuotient_restrictionLinearMap hΩ u

/-- The restricted base coordinate represents the original function almost everywhere
on the smaller domain. -/
theorem toLp_restrictCLM_apply_ae
    {Ω₁ Ω₂ : Set (ℝ^n)} (hΩ : Ω₁ ⊆ Ω₂)
    (u : W^{s,p}(Ω₂; F)) :
    (toLp n s Ω₁ (restrictCLM hΩ u) : ℝ^n → F)
      =ᵐ[(volume : Measure (ℝ^n)).restrict Ω₁] (toLp n s Ω₂ u : ℝ^n → F) := by
  simpa only [toLp_restrictCLM] using
    Lp.restrictionCLMOfLE_apply_ae (Measure.restrict_mono hΩ le_rfl) (toLp n s Ω₂ u)

/-- The restricted weighted difference represents the original weighted difference
almost everywhere on the smaller domain square. -/
theorem differenceQuotient_restrictCLM_apply_ae
    {Ω₁ Ω₂ : Set (ℝ^n)} (hΩ : Ω₁ ⊆ Ω₂)
    (u : W^{s,p}(Ω₂; F)) :
    (differenceQuotient n s Ω₁ (restrictCLM hΩ u) : ℝ^n × ℝ^n → F)
      =ᵐ[gagliardoProductMeasure n Ω₁]
        (differenceQuotient n s Ω₂ u : ℝ^n × ℝ^n → F) := by
  rw [differenceQuotient_restrictCLM]
  exact Lp.restrictionCLMOfLE_apply_ae _ _

/-- Packaging a raw Gagliardo function commutes with restriction to a subdomain. -/
theorem restrictCLM_ofFunction
    {Ω₁ Ω₂ : Set (ℝ^n)} (hΩ : Ω₁ ⊆ Ω₂)
    (u : ℝ^n → F) (hu : MemGagliardo n s Ω₂ u (p := p)) :
    restrictCLM hΩ (ofFunction (n := n) (s := s) (Ω := Ω₂) u hu) =
      ofFunction (n := n) (s := s) (Ω := Ω₁) u (hu.mono hΩ) := by
  apply toLp_injective
  apply Lp.ext
  have hsourceSmall :
      (toLp n s Ω₂ (ofFunction (n := n) (s := s) (Ω := Ω₂) u hu) : ℝ^n → F)
        =ᵐ[(volume : Measure (ℝ^n)).restrict Ω₁] u :=
    ae_mono (Measure.restrict_mono hΩ le_rfl) (toLp_ofFunction_apply_ae u hu)
  exact (toLp_restrictCLM_apply_ae hΩ (ofFunction u hu)).trans
    (hsourceSmall.trans (toLp_ofFunction_apply_ae u (hu.mono hΩ)).symm)

/-- Restriction does not increase the Gagliardo graph norm, also at `p = ∞`. -/
theorem norm_restrictCLM_apply_le
    {Ω₁ Ω₂ : Set (ℝ^n)} (hΩ : Ω₁ ⊆ Ω₂)
    (u : W^{s,p}(Ω₂; F)) :
    ‖restrictCLM hΩ u‖ ≤ ‖u‖ :=
  norm_restrictionLinearMap_le hΩ u

/-- The operator norm of Gagliardo restriction is at most one. -/
theorem norm_restrictCLM_le_one
    {Ω₁ Ω₂ : Set (ℝ^n)} (hΩ : Ω₁ ⊆ Ω₂) :
    ‖restrictCLM (n := n) (s := s) (p := p) (F := F) hΩ‖ ≤ 1 :=
  (restrictCLM (n := n) (s := s) (p := p) (F := F) hΩ).opNorm_le_bound zero_le_one
    fun u ↦ by simpa only [one_mul] using norm_restrictCLM_apply_le hΩ u

/-- Restricting to the same domain is the identity. -/
theorem restrictCLM_self (Ω : Set (ℝ^n)) :
    restrictCLM (n := n) (s := s) (p := p) (F := F) (Set.Subset.rfl : Ω ⊆ Ω) =
      ContinuousLinearMap.id ℝ (W^{s,p}(Ω; F)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply toLp_injective
  simp only [toLp_restrictCLM, Lp.restrictionCLMOfLE_refl, ContinuousLinearMap.id_apply]

/-- Restriction is functorial under a chain of domain inclusions. -/
theorem restrictCLM_comp
    {Ω₁ Ω₂ Ω₃ : Set (ℝ^n)} (h₁₂ : Ω₁ ⊆ Ω₂) (h₂₃ : Ω₂ ⊆ Ω₃) :
    (restrictCLM (n := n) (s := s) (p := p) (F := F) h₁₂).comp
        (restrictCLM (n := n) (s := s) (p := p) (F := F) h₂₃) =
      restrictCLM (n := n) (s := s) (p := p) (F := F) (h₁₂.trans h₂₃) := by
  apply ContinuousLinearMap.ext
  intro u
  apply toLp_injective
  simp only [ContinuousLinearMap.comp_apply, toLp_restrictCLM]
  exact congrArg (fun T ↦ T (toLp n s Ω₃ u))
    (Lp.restrictionCLMOfLE_trans
      (Measure.restrict_mono h₁₂ le_rfl) (Measure.restrict_mono h₂₃ le_rfl))

end SobolevSpace.Fractional.GagliardoSpace
