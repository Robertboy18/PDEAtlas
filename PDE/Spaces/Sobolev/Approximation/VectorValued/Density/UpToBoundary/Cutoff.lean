/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.IndicatorExtension
public import PDE.Analysis.MeasureTheory.Lp.Restriction
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.SmoothMultiplier
import PDE.Analysis.Normed.PiLp.Coordinatewise
import PDE.DistributionTheory.TestFunction.CompactCutoff
import PDE.Spaces.Sobolev.Localization.Cutoff.CompactSupport

/-!
# Boundary-relative cutoff multiplication for Banach-valued Sobolev functions

A smooth cutoff supported in an ambient neighborhood `V` localizes a Sobolev
function on `V ∩ Ω` to one on `Ω`. Its finite Leibniz rows extend across the
artificial edge of `V`; the cutoff may remain nonzero at the physical boundary.
Coordinatewise extension preserves the multiplier bound for every order and
every `1 ≤ p ≤ ∞`.
-/

@[expose] public noncomputable section

open Function MeasureTheory TopologicalSpace
open scoped Distributions ENNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {V Ω : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [Fact (1 ≤ p)] [NormedSpace ℝ F] [CompleteSpace F] in
private theorem memLp_of_inter_support {f : ℝ^n → F}
    (hf : MemLp f p (domainMeasure n (V ⊓ Ω))) (hsupp : support f ⊆ V) :
    MemLp f p (domainMeasure n Ω) := by
  have hmeasure : (domainMeasure n Ω).restrict V = domainMeasure n (V ⊓ Ω) := by
    rw [domainMeasure, Measure.restrict_restrict V.isOpen.measurableSet]
    rfl
  have hmem : MemLp ((V : Set ℝ^n).indicator f) p (domainMeasure n Ω) := by
    rw [memLp_indicator_iff_restrict V.isOpen.measurableSet.nullMeasurableSet, hmeasure]
    exact hf
  simpa only [Set.indicator_eq_self.2 hsupp] using hmem

private theorem hasWeakDerivativeOn_inter_support {α : List (Fin n)} {f g : ℝ^n → F}
    (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (hψ : tsupport ψ.toFun ⊆ V)
    (hf : support f ⊆ tsupport ψ.toFun) (hg : support g ⊆ tsupport ψ.toFun)
    (hfLp : MemLp f p (domainMeasure n Ω)) (hgLp : MemLp g p (domainMeasure n Ω))
    (hweak : HasWeakDerivativeOn (V ⊓ Ω) α f g) :
    HasWeakDerivativeOn Ω α f g := by
  obtain ⟨χ, hχ, _, hχone, _⟩ := TestFunction.exists_eq_one_on_compact
    V.isOpen ψ.hasCompactSupport hψ
  apply (hasWeakDerivativeOn_iff_forall_dual
    (locallyIntegrableOn_of_locallyIntegrable_restrict (hfLp.locallyIntegrable Fact.out))
    (locallyIntegrableOn_of_locallyIntegrable_restrict (hgLp.locallyIntegrable Fact.out))).mpr
  intro L
  apply CompactSupportLocalization.hasWeakDerivativeOn_word_of_inter_of_cutoff_one_nhds
    V.isOpen Ω.isOpen α _ _ χ hχ hχone (L.comp_memLp' hfLp) (L.comp_memLp' hgLp)
    (hasWeakDerivativeOn_real_iff.mp (hweak.map L))
  · intro x hx
    apply hf
    intro hzero
    exact hx (by simp only [comp_apply, hzero, map_zero])
  · intro x hx
    apply hg
    intro hzero
    exact hx (by simp only [comp_apply, hzero, map_zero])

private def interRowExtension :
    Lp F p (domainMeasure n (V ⊓ Ω)) →L[ℝ] Lp F p (domainMeasure n Ω) :=
  (Lp.restrictionCLMOfLE (E := F) (p := p) Measure.restrict_le_self).comp
    (Lp.extendByZeroₗᵢ (𝕜 := ℝ) (E := F) (p := p) (μ := volume)
      (V ⊓ Ω).isOpen.measurableSet).toContinuousLinearMap

omit [CompleteSpace F] in
private theorem interRowExtension_ae (u : Lp F p (domainMeasure n (V ⊓ Ω)))
    {f : ℝ^n → F} (hu : (u : ℝ^n → F) =ᵐ[domainMeasure n (V ⊓ Ω)] f)
    (hf : support f ⊆ V) :
    (interRowExtension u : ℝ^n → F) =ᵐ[domainMeasure n Ω] f := by
  have hind := (ae_eq_restrict_iff_indicator_ae_eq (V ⊓ Ω).isOpen.measurableSet).mp hu
  have hz := Lp.extendByZeroₗᵢ_apply_ae (𝕜 := ℝ) (V ⊓ Ω).isOpen.measurableSet u
  have hr := Lp.restrictionCLMOfLE_apply_ae (E := F) (p := p)
    (show domainMeasure n Ω ≤ volume from Measure.restrict_le_self)
    (Lp.extendByZeroₗᵢ (𝕜 := ℝ) (V ⊓ Ω).isOpen.measurableSet u)
  filter_upwards [hr, ae_mono Measure.restrict_le_self hz,
    ae_mono Measure.restrict_le_self hind, ae_restrict_mem Ω.isOpen.measurableSet]
    with x hxr hxz hxi hxΩ
  change interRowExtension u x = _ at hxr
  rw [hxr, hxz, hxi]
  by_cases hxV : x ∈ V
  · exact Set.indicator_of_mem (show x ∈ (V ⊓ Ω : Opens ℝ^n) from ⟨hxV, hxΩ⟩) f
  · rw [Set.indicator_of_notMem
      (show x ∉ (V ⊓ Ω : Opens ℝ^n) from fun hx ↦ hxV hx.1)]
    exact (notMem_support.mp (fun hx ↦ hxV (hf hx))).symm

private def interMultiplierFamily (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) :
    W^{k,p}((V ⊓ Ω); F) →L[ℝ] WkpAmbientOn n k p Ω F :=
  (PiLp.continuousLinearEquiv p ℝ
    (fun _ : DerivIndex n k ↦ Lp F p (domainMeasure n Ω))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a ↦ interRowExtension.comp
      ((coordinateCLM a).comp
        (compactSmoothMultiplierCLM ψ.toFun ψ.contDiff ψ.hasCompactSupport)))

private theorem interMultiplierFamily_ae
    (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (hψ : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}((V ⊓ Ω); F)) (a : DerivIndex n k) :
    (interMultiplierFamily ψ U a : ℝ^n → F) =ᵐ[domainMeasure n Ω]
      smoothLeibnizRepresentative ψ.toFun U a.toList :=
  interRowExtension_ae _
    (compactSmoothMultiplierCLM_coordinate_ae ψ.toFun ψ.contDiff ψ.hasCompactSupport U a)
    (((subset_tsupport _).trans
      (tsupport_smoothLeibnizRepresentative_subset ψ.toFun U a.toList)).trans hψ)

private theorem inter_leibniz_weak
    (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (hψ : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}((V ⊓ Ω); F)) (a : DerivIndex n k) :
    HasWeakDerivativeOn Ω a.toList
      (smoothLeibnizRepresentative ψ.toFun U (baseIndex n k).toList)
      (smoothLeibnizRepresentative ψ.toFun U a.toList) := by
  let d := fun a : DerivIndex n k ↦ smoothLeibnizRepresentative ψ.toFun U a.toList
  let T : W^{k,p}((V ⊓ Ω); F) :=
    compactSmoothMultiplierCLM ψ.toFun ψ.contDiff ψ.hasCompactSupport U
  have hrow (b : DerivIndex n k) :
      (T.val b : ℝ^n → F) =ᵐ[domainMeasure n (V ⊓ Ω)] d b :=
    compactSmoothMultiplierCLM_coordinate_ae ψ.toFun ψ.contDiff ψ.hasCompactSupport U b
  have hsupp (a : DerivIndex n k) : support (d a) ⊆ tsupport ψ.toFun :=
    (subset_tsupport _).trans (tsupport_smoothLeibnizRepresentative_subset ψ.toFun U a.toList)
  have hmem (a : DerivIndex n k) : MemLp (d a) p (domainMeasure n Ω) :=
    memLp_of_inter_support (V := V) (Ω := Ω)
      ((Lp.memLp (T.val a)).ae_eq (hrow a))
      ((hsupp a).trans hψ)
  have hlocal : HasWeakDerivativeOn (V ⊓ Ω) a.toList (d (baseIndex n k)) (d a) :=
    (T.property a).congr_ae (hrow (baseIndex n k)) (hrow a)
  exact hasWeakDerivativeOn_inter_support ψ hψ (hsupp _) (hsupp _)
    (hmem _) (hmem _) hlocal

private theorem interMultiplierFamily_mem
    (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (hψ : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}((V ⊓ Ω); F)) : IsWkpOn (interMultiplierFamily ψ U) := by
  intro a
  exact (inter_leibniz_weak ψ hψ U a).congr_ae
      (interMultiplierFamily_ae ψ hψ U (baseIndex n k)).symm
      (interMultiplierFamily_ae ψ hψ U a).symm

/-- Cutoff multiplication from an ambient neighborhood intersected with the physical domain.
The cutoff is supported in `V` and may be nonzero on the boundary of `Ω`. -/
def interMultiplier (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (hψ : tsupport ψ.toFun ⊆ V) :
    W^{k,p}((V ⊓ Ω); F) →L[ℝ] W^{k,p}(Ω; F) :=
  let Z := (Lp.extendByZeroₗᵢ (𝕜 := ℝ) (E := F) (p := p) (μ := volume)
    (V ⊓ Ω).isOpen.measurableSet).toContinuousLinearMap
  let R := Lp.restrictionCLMOfLE (E := F) (p := p)
    (show domainMeasure n Ω ≤ volume from Measure.restrict_le_self)
  let A := (PiLp.continuousLinearEquiv p ℝ
    (fun _ : DerivIndex n k ↦ Lp F p (domainMeasure n Ω))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a ↦ (R.comp Z).comp
      ((coordinateCLM a).comp
        (compactSmoothMultiplierCLM ψ.toFun ψ.contDiff ψ.hasCompactSupport)))
  A.codRestrict (wkpSubmoduleOn n k p Ω F) (by
    exact interMultiplierFamily_mem ψ hψ)

/-- Every coordinate of the relative multiplier is the finite Leibniz representative. -/
theorem interMultiplier_coordinate_ae
    (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (hψ : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}((V ⊓ Ω); F)) (a : DerivIndex n k) :
    ((interMultiplier ψ hψ U).val a : ℝ^n → F) =ᵐ[domainMeasure n Ω]
      smoothLeibnizRepresentative ψ.toFun U a.toList :=
  interMultiplierFamily_ae ψ hψ U a

/-- The base action is cutoff multiplication for any supplied almost-everywhere representative.
Values of that representative outside `V ∩ Ω` do not affect the result on `Ω`. -/
theorem interMultiplier_base_ae
    (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (hψ : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}((V ⊓ Ω); F)) {f : ℝ^n → F}
    (hU : (U.val (baseIndex n k) : ℝ^n → F) =ᵐ[domainMeasure n (V ⊓ Ω)] f) :
    ((interMultiplier ψ hψ U).val (baseIndex n k) : ℝ^n → F) =ᵐ[domainMeasure n Ω]
      fun x ↦ ψ.toFun x • f x := by
  have hbase := interMultiplier_coordinate_ae ψ hψ U (baseIndex n k)
  simp only [baseIndex_toList, smoothLeibnizRepresentative_nil] at hbase
  apply hbase.trans
  apply ae_of_ae_restrict_of_ae_restrict_compl (V : Set ℝ^n)
  · have hmeasure : (domainMeasure n Ω).restrict V = domainMeasure n (V ⊓ Ω) := by
      rw [domainMeasure, Measure.restrict_restrict V.isOpen.measurableSet]
      rfl
    rw [hmeasure]
    filter_upwards [hU] with x hx
    rw [hx]
  · filter_upwards [ae_restrict_mem V.isOpen.measurableSet.compl] with x hx
    have hzero : ψ.toFun x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hs ↦ hx (hψ hs))
    simp only [hzero, zero_smul]

/-- Extending the localized rows does not increase their Sobolev norm. -/
theorem norm_interMultiplier_apply_le
    (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (hψ : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}((V ⊓ Ω); F)) :
    ‖interMultiplier ψ hψ U‖ ≤
      ‖compactSmoothMultiplierCLM ψ.toFun ψ.contDiff ψ.hasCompactSupport U‖ := by
  apply PiLp.norm_mono
  intro a
  change ‖interRowExtension
    ((compactSmoothMultiplierCLM ψ.toFun ψ.contDiff ψ.hasCompactSupport U).val a)‖ ≤ _
  exact (Lp.norm_restrictionCLMOfLE_apply_le Measure.restrict_le_self _).trans_eq
    ((Lp.extendByZeroₗᵢ (𝕜 := ℝ) (V ⊓ Ω).isOpen.measurableSet).norm_map _)

/-- The relative multiplier has at most the norm of the multiplier on the intersection. -/
theorem norm_interMultiplier_le
    (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (hψ : tsupport ψ.toFun ⊆ V) :
    ‖interMultiplier (F := F) (k := k) (p := p) (Ω := Ω) ψ hψ‖ ≤
      ‖compactSmoothMultiplierCLM (F := F) (k := k) (p := p) (Ω := V ⊓ Ω)
        ψ.toFun ψ.contDiff ψ.hasCompactSupport‖ := by
  refine ContinuousLinearMap.opNorm_le_bound
    (interMultiplier (F := F) (k := k) (p := p) (Ω := Ω) ψ hψ)
    (ContinuousLinearMap.opNorm_nonneg _) ?_
  intro U
  exact (norm_interMultiplier_apply_le ψ hψ U).trans
    (ContinuousLinearMap.le_opNorm _ U)

end SobolevSpace.VectorValued
