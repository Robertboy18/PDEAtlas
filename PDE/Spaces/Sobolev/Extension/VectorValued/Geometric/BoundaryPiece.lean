/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.VectorValued.Geometric.Localization
public import PDE.Spaces.Sobolev.Extension.VectorValued.HalfSpace.Operator

/-!
# A reflected Banach-valued boundary piece

Flattening, the weighted half-space reflection, and localization back
through the chart give a bounded extension of one partition piece. The auxiliary
target cutoff is one on the transported partition support, so the physical
restriction contains exactly one factor of the partition function.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace Set
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued.GeometricExtension

open GraphSpace
open SobolevSpace.VectorValued.HigherOrderReflection
open SobolevSpace.WeakChangeOfVariables
open Boundary.C1ExtensionAtlas.Charts Boundary.C1ExtensionAtlas.DerivedCutoffs

variable {n k : ℕ} [Fact (0 < n)] {Ω : Opens ℝ^n}
  [hΩ : Boundary.C1ExtensionAtlas n (Ω : Set ℝ^n)]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Extend one physical `Lp` boundary patch by weighted reflection in chart coordinates. -/
def boundaryExtensionLp (k : ℕ) (i : Fin hΩ.N) :
    Lp F p (domainMeasure n Ω) →L[ℝ] Lp F p (domainMeasure n univ) :=
  (localizeLp i).comp ((weightedExtendLp n k p 0).comp (flattenLp i))

/-- Extend one Banach-valued Sobolev boundary patch using the same reflection. -/
def boundaryExtensionSobolev (hk : 0 < k)
    (hE : ∀ i, ContDiff ℝ k (hΩ.chart i))
    (hEinv : ∀ i, ContDiff ℝ k (hΩ.chart i).symm) (i : Fin hΩ.N) :
    W^{k,p}(Ω; F) →L[ℝ] W^{k,p}(ℝ^n; F) :=
  (localizeSobolev hk hE i).comp
    ((weightedReflection n k p).comp (flattenSobolev hk hEinv i))

/-- The reflected boundary piece commutes with the physical base projection. -/
theorem boundaryExtensionSobolev_base (hk : 0 < k)
    (hE : ∀ i, ContDiff ℝ k (hΩ.chart i))
    (hEinv : ∀ i, ContDiff ℝ k (hΩ.chart i).symm) (i : Fin hΩ.N)
    (U : W^{k,p}(Ω; F)) :
    coordinateCLM (baseIndex n k) (boundaryExtensionSobolev hk hE hEinv i U) =
      boundaryExtensionLp k i (coordinateCLM (baseIndex n k) U) := by
  dsimp only [boundaryExtensionSobolev, boundaryExtensionLp, ContinuousLinearMap.comp_apply]
  rw [localizeSobolev_base]
  have hbase (V : W^{k,p}(⟨ℝ^n₊, HalfSpace.isOpen_upper n⟩; F)) :
      coordinateCLM (baseIndex n k) (weightedReflection n k p V) =
        weightedExtendLp n k p 0 (coordinateCLM (baseIndex n k) V) := by
    simp only [coordinateCLM_apply, weightedReflection_coordinate, baseIndex_multiplicity]
  rw [hbase, flattenSobolev_base]

/-- On the physical domain, a reflected boundary piece equals its partition contribution. -/
theorem boundaryExtensionLp_apply_ae (k : ℕ) (i : Fin hΩ.N)
    (u : Lp F p (domainMeasure n Ω)) :
    (boundaryExtensionLp k i u : ℝ^n → F) =ᵐ[domainMeasure n Ω]
      fun x ↦ hΩ.boundaryCutoff i x • u x := by
  let E := chartOnΩ (Ω := (Ω : Set ℝ^n)) i
  let f := flattenLp i u
  let w := weightedExtendLp n k p 0 f
  have hr : (w : ℝ^n → F) =ᵐ[domainMeasure n ℝ^n₊] f := by
    have h := Lp.restrictionCLMOfLE_apply_ae
      (Measure.restrict_mono (subset_univ ℝ^n₊) le_rfl) w
    rw [show Lp.restrictionCLMOfLE
        (Measure.restrict_mono (subset_univ ℝ^n₊) le_rfl) w = f from
      restrict_weightedExtendLp n k p 0 f] at h
    exact h.symm
  have hrD := hr.filter_mono
    (ae_mono (Measure.restrict_mono
      (inter_subset_right : (hΩ.chart i).target ∩ ℝ^n₊ ⊆ ℝ^n₊) le_rfl))
  have hwE : (w : ℝ^n → F) =ᵐ[domainMeasure n E.target]
      fun y ↦ targetSupportCutoff (Ω := (Ω : Set ℝ^n)) i y • u (E.symm y) := by
    change (w : ℝ^n → F) =ᵐ[domainMeasure n (chartOnΩ (Ω := (Ω : Set ℝ^n)) i).target]
      fun y ↦ targetSupportCutoff (Ω := (Ω : Set ℝ^n)) i y • u ((hΩ.chart i).symm y)
    rw [chartOnΩ_target_eq_target_inter_upper]
    exact hrD.trans (flattenLp_apply_ae i u)
  have hE : ContDiff ℝ 1 E := by
    simpa [E, chartOnΩ] using hΩ.chart_contDiff i
  have hEinv : ContDiff ℝ 1 E.symm := by
    simpa [E, chartOnΩ] using hΩ.chart_symm_contDiff i
  have hpull := (quasiMeasurePreserving_partialHomeomorph hE hEinv).ae_eq_comp hwE
  have hsource : (fun x ↦ w (hΩ.chart i x)) =ᵐ[domainMeasure n E.source]
      fun x ↦ targetSupportCutoff (Ω := (Ω : Set ℝ^n)) i (hΩ.chart i x) • u x := by
    filter_upwards [hpull, ae_restrict_mem E.open_source.measurableSet] with x hx hxE
    change w (E x) = targetSupportCutoff (Ω := (Ω : Set ℝ^n)) i (E x) • u x
    simpa only [Function.comp_apply, E.left_inv hxE] using hx
  have himp := (ae_restrict_iff' E.open_source.measurableSet).mp hsource
  have hΩimp := himp.filter_mono
    (ae_mono (Measure.restrict_le_self : domainMeasure n Ω ≤ volume))
  have hlocal := (localizeLp_apply_ae i w).filter_mono
    (ae_mono (Measure.restrict_mono (subset_univ (Ω : Set ℝ^n)) le_rfl))
  filter_upwards [hlocal, hΩimp, ae_restrict_mem Ω.isOpen.measurableSet]
    with x hloc hx hxΩ
  change localizeLp i w x = _
  rw [hloc]
  by_cases hψ : hΩ.boundaryCutoff i x = 0
  · simp [hψ]
  · have hxE : x ∈ E.source := by
      rw [chartOnΩ_source]
      exact ⟨hΩ.boundaryCutoff_support i (subset_tsupport _ hψ), hxΩ⟩
    rw [hx hxE]
    have hη : targetSupportCutoff (Ω := (Ω : Set ℝ^n)) i (hΩ.chart i x) = 1 :=
      targetSupportCutoff_eq_one_on_boundarySupportInTarget i (hΩ.chart i x)
        ⟨x, subset_tsupport _ hψ, rfl⟩
    rw [hη, one_smul]

end SobolevSpace.VectorValued.GeometricExtension
