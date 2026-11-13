/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Cutoffs
public import PDE.Spaces.Sobolev.Calculus.Pullback.VectorValued.HigherOrder
public import PDE.Spaces.Sobolev.Extension.VectorValued.Geometric.Cutoff
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Restriction

/-!
# Flattening a Banach-valued boundary patch

Restrict to the domain part of a chart, pull back by its inverse, and use the
relative multiplier to extend into the upper half-space. Its auxiliary
cutoff equals one on the transported partition support. The physical `Lp` map
and every Sobolev order use this same cutoff and chart composition.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace Set
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued.GeometricExtension

open GraphSpace
open SobolevSpace.WeakChangeOfVariables
open Boundary.C1ExtensionAtlas.Charts Boundary.C1ExtensionAtlas.DerivedCutoffs

variable {n k : ℕ} [Fact (0 < n)] {Ω : Opens ℝ^n}
  [hΩ : Boundary.C1ExtensionAtlas n (Ω : Set ℝ^n)]

private theorem chartDomain_source_le (i : Fin hΩ.N) :
    (chartOnΩ (Ω := (Ω : Set ℝ^n)) i).source ⊆ (Ω : Set ℝ^n) := by
  rw [chartOnΩ_source]
  exact inter_subset_right

private theorem chartDomain_target_le (i : Fin hΩ.N) :
    (hΩ.chart i).target ∩ ℝ^n₊ ⊆ (chartOnΩ (Ω := (Ω : Set ℝ^n)) i).target := by
  rw [chartOnΩ_target_eq_target_inter_upper]

private theorem chartDomain_source_bounded (i : Fin hΩ.N) :
    Bornology.IsBounded (chartOnΩ (Ω := (Ω : Set ℝ^n)) i).source := by
  apply (isBounded_source_of_isBounded_target
    (hΩ.chart_symm_contDiff i).continuous (hΩ.chart_target_bounded i)).subset
  rw [chartOnΩ_source]
  exact inter_subset_left

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Inverse-chart composition and the auxiliary cutoff on physical `Lp` functions. -/
def flattenLp (i : Fin hΩ.N) :
    Lp F p (domainMeasure n Ω) →L[ℝ] Lp F p (domainMeasure n ℝ^n₊) :=
  (interMultiplierLp (V := ⟨(hΩ.chart i).target, (hΩ.chart i).open_target⟩)
    (Ω := ⟨ℝ^n₊, HalfSpace.isOpen_upper n⟩)
    (targetSupportCutoff (Ω := (Ω : Set ℝ^n)) i)
    (tsupport_targetSupportCutoff_subset_target (Ω := (Ω : Set ℝ^n)) i)).comp
    ((Lp.restrictionCLMOfLE
      (Measure.restrict_mono (by exact chartDomain_target_le (Ω := Ω) i) le_rfl)).comp
      ((boundedPullbackCLM (F := F)
        (show ContDiff ℝ 1 (chartOnΩ (Ω := (Ω : Set ℝ^n)) i).symm by
          simpa [chartOnΩ] using hΩ.chart_symm_contDiff i)
        (show ContDiff ℝ 1 (chartOnΩ (Ω := (Ω : Set ℝ^n)) i).symm.symm by
          simpa [chartOnΩ] using hΩ.chart_contDiff i)
        (by exact chartDomain_source_bounded (Ω := Ω) i)).comp
        (Lp.restrictionCLMOfLE
          (Measure.restrict_mono (by exact chartDomain_source_le (Ω := Ω) i) le_rfl))))

/-- Flatten a Sobolev boundary patch without extending across the physical boundary. -/
def flattenSobolev (hk : 0 < k)
    (hEinv : ∀ i, ContDiff ℝ k (hΩ.chart i).symm) (i : Fin hΩ.N) :
    W^{k,p}(Ω; F) →L[ℝ]
      W^{k,p}(⟨ℝ^n₊, HalfSpace.isOpen_upper n⟩; F) :=
  (interMultiplier (V := ⟨(hΩ.chart i).target, (hΩ.chart i).open_target⟩)
    (Ω := ⟨ℝ^n₊, HalfSpace.isOpen_upper n⟩)
    (targetSupportCutoff (Ω := (Ω : Set ℝ^n)) i)
    (tsupport_targetSupportCutoff_subset_target (Ω := (Ω : Set ℝ^n)) i)).comp
    ((VectorValued.restrictCLM (show
      (⟨(hΩ.chart i).target, (hΩ.chart i).open_target⟩ ⊓
        ⟨ℝ^n₊, HalfSpace.isOpen_upper n⟩ : Opens ℝ^n) ≤
          ⟨(chartOnΩ (Ω := (Ω : Set ℝ^n)) i).target,
            (chartOnΩ (Ω := (Ω : Set ℝ^n)) i).open_target⟩ from by
      exact chartDomain_target_le (Ω := Ω) i)).comp
      ((WeakChangeOfVariables.pullbackCLM
        (show ContDiff ℝ (max k 1 : ℕ) (chartOnΩ (Ω := (Ω : Set ℝ^n)) i).symm by
          simpa [chartOnΩ, max_eq_left (Nat.succ_le_iff.mpr hk)] using hEinv i)
        (show ContDiff ℝ 1 (chartOnΩ (Ω := (Ω : Set ℝ^n)) i).symm.symm by
          simpa [chartOnΩ] using hΩ.chart_contDiff i)
        (by exact chartDomain_source_bounded (Ω := Ω) i)).comp
        (VectorValued.restrictCLM (show
          (⟨(chartOnΩ (Ω := (Ω : Set ℝ^n)) i).source,
            (chartOnΩ (Ω := (Ω : Set ℝ^n)) i).open_source⟩ :
            Opens ℝ^n) ≤ Ω from by exact chartDomain_source_le (Ω := Ω) i))))

/-- Sobolev flattening commutes with the physical `Lp` base projection. -/
theorem flattenSobolev_base (hk : 0 < k)
    (hEinv : ∀ i, ContDiff ℝ k (hΩ.chart i).symm) (i : Fin hΩ.N)
    (U : W^{k,p}(Ω; F)) :
    coordinateCLM (baseIndex n k) (flattenSobolev hk hEinv i U) =
      flattenLp i (coordinateCLM (baseIndex n k) U) := by
  dsimp only [flattenSobolev, flattenLp, ContinuousLinearMap.comp_apply]
  rw [interMultiplier_base_eq]
  congr 1
  exact congrArg (Lp.restrictionCLMOfLE
    (Measure.restrict_mono (chartDomain_target_le (Ω := Ω) i) le_rfl))
    (WeakChangeOfVariables.pullbackCLM_base _ _ _ _)

/-- Flattening composes a chosen representative with the inverse chart and applies
the target cutoff on the whole upper half-space. -/
theorem flattenLp_ae_eq (i : Fin hΩ.N) (u : Lp F p (domainMeasure n Ω))
    {f : ℝ^n → F} (hu : (u : ℝ^n → F) =ᵐ[domainMeasure n Ω] f) :
    (flattenLp i u : ℝ^n → F) =ᵐ[domainMeasure n ℝ^n₊]
      fun y ↦ targetSupportCutoff (Ω := (Ω : Set ℝ^n)) i y • f ((hΩ.chart i).symm y) := by
  let E := chartOnΩ (Ω := (Ω : Set ℝ^n)) i
  have hsource : E.source ⊆ (Ω : Set ℝ^n) := chartDomain_source_le (Ω := Ω) i
  have htarget : (hΩ.chart i).target ∩ ℝ^n₊ ⊆ E.target := chartDomain_target_le (Ω := Ω) i
  have hbound : Bornology.IsBounded E.source := chartDomain_source_bounded (Ω := Ω) i
  have hE : ContDiff ℝ 1 E := by
    simpa [E, chartOnΩ] using hΩ.chart_contDiff i
  have hEinv : ContDiff ℝ 1 E.symm := by
    simpa [E, chartOnΩ] using hΩ.chart_symm_contDiff i
  let r := Lp.restrictionCLMOfLE (Measure.restrict_mono hsource le_rfl) u
  let q := boundedPullbackCLM hEinv hE hbound r
  let s := Lp.restrictionCLMOfLE (Measure.restrict_mono htarget le_rfl) q
  have hr : (r : ℝ^n → F) =ᵐ[domainMeasure n E.source] f :=
    (Lp.restrictionCLMOfLE_apply_ae (Measure.restrict_mono hsource le_rfl) u).trans
      (hu.filter_mono (ae_mono (Measure.restrict_mono hsource le_rfl)))
  have hq := boundedPullbackCLM_ae_eq_comp hEinv hE hbound r hr
  have hs : (s : ℝ^n → F) =ᵐ[domainMeasure n ((hΩ.chart i).target ∩ ℝ^n₊)]
      fun y ↦ f ((hΩ.chart i).symm y) :=
    (Lp.restrictionCLMOfLE_apply_ae (Measure.restrict_mono htarget le_rfl) q).trans
      (hq.filter_mono (ae_mono (Measure.restrict_mono htarget le_rfl)))
  exact interMultiplierLp_apply_ae
    (V := ⟨(hΩ.chart i).target, (hΩ.chart i).open_target⟩)
    (Ω := ⟨ℝ^n₊, HalfSpace.isOpen_upper n⟩)
    (targetSupportCutoff (Ω := (Ω : Set ℝ^n)) i)
    (tsupport_targetSupportCutoff_subset_target (Ω := (Ω : Set ℝ^n)) i) s hs

/-- Above the flattened boundary, the physical field is inverse-chart composition
multiplied by the auxiliary target cutoff. -/
theorem flattenLp_apply_ae (i : Fin hΩ.N) (u : Lp F p (domainMeasure n Ω)) :
    (flattenLp i u : ℝ^n → F) =ᵐ[domainMeasure n ((hΩ.chart i).target ∩ ℝ^n₊)]
      fun y ↦ targetSupportCutoff (Ω := (Ω : Set ℝ^n)) i y • u ((hΩ.chart i).symm y) := by
  exact (flattenLp_ae_eq i u Filter.EventuallyEq.rfl).filter_mono
    (ae_mono (Measure.restrict_mono
      (inter_subset_right : (hΩ.chart i).target ∩ ℝ^n₊ ⊆ ℝ^n₊) le_rfl))

end SobolevSpace.VectorValued.GeometricExtension
