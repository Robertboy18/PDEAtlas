/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.VectorValued.Geometric.Flattening

/-!
# Returning a Banach-valued boundary patch to physical coordinates

Pull a whole-space function through a chart and apply its partition cutoff.
The relative multiplier extends the localized result across the
artificial chart edge. Its physical formula is the partition function times
the chart composition, at every exponent endpoint.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace Set
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued.GeometricExtension

open GraphSpace
open SobolevSpace.WeakChangeOfVariables

variable {n k : ℕ} [Fact (0 < n)] {Ω : Opens ℝ^n}
  [hΩ : Boundary.C1ExtensionAtlas n (Ω : Set ℝ^n)]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Return a whole-space physical field through the chart and apply its partition cutoff. -/
def localizeLp (i : Fin hΩ.N) :
    Lp F p (domainMeasure n univ) →L[ℝ] Lp F p (domainMeasure n univ) :=
  (interMultiplierLp (Ω := ⊤)
    (V := ⟨(hΩ.chart i).source, (hΩ.chart i).open_source⟩)
    (hΩ.boundaryCutoff i) (hΩ.boundaryCutoff_support i)).comp
    ((Lp.restrictionCLMOfLE (Measure.restrict_mono
      (inter_subset_left : (hΩ.chart i).source ∩ univ ⊆ (hΩ.chart i).source) le_rfl)).comp
      ((boundedPullbackCLM (F := F) (hΩ.chart_contDiff i)
        (hΩ.chart_symm_contDiff i) (hΩ.chart_target_bounded i)).comp
        (Lp.restrictionCLMOfLE
          (Measure.restrict_mono (subset_univ (hΩ.chart i).target) le_rfl))))

/-- Return a Sobolev field through a chart and localize it to the partition support. -/
def localizeSobolev (hk : 0 < k)
    (hE : ∀ i, ContDiff ℝ k (hΩ.chart i)) (i : Fin hΩ.N) :
    W^{k,p}(ℝ^n; F) →L[ℝ] W^{k,p}(ℝ^n; F) :=
  (interMultiplier (Ω := ⊤)
    (V := ⟨(hΩ.chart i).source, (hΩ.chart i).open_source⟩)
    (hΩ.boundaryCutoff i) (hΩ.boundaryCutoff_support i)).comp
    ((VectorValued.restrictCLM (show
      (⟨(hΩ.chart i).source, (hΩ.chart i).open_source⟩ ⊓ ⊤ : Opens ℝ^n) ≤
        ⟨(hΩ.chart i).source, (hΩ.chart i).open_source⟩ from inf_le_left)).comp
      ((WeakChangeOfVariables.pullbackCLM
        (show ContDiff ℝ (max k 1 : ℕ) (hΩ.chart i) by
          simpa only [max_eq_left (Nat.succ_le_iff.mpr hk)] using hE i)
        (hΩ.chart_symm_contDiff i) (hΩ.chart_target_bounded i)).comp
        (VectorValued.restrictCLM (show
          (⟨(hΩ.chart i).target, (hΩ.chart i).open_target⟩ : Opens ℝ^n) ≤ ⊤
          from le_top))))

/-- Chart localization uses the same physical map at every Sobolev order. -/
theorem localizeSobolev_base (hk : 0 < k)
    (hE : ∀ i, ContDiff ℝ k (hΩ.chart i)) (i : Fin hΩ.N)
    (U : W^{k,p}(ℝ^n; F)) :
    coordinateCLM (baseIndex n k) (localizeSobolev hk hE i U) =
      localizeLp i (coordinateCLM (baseIndex n k) U) := by
  dsimp only [localizeSobolev, localizeLp, ContinuousLinearMap.comp_apply]
  rw [interMultiplier_base_eq]
  congr 1
  exact congrArg (Lp.restrictionCLMOfLE (Measure.restrict_mono
    (inter_subset_left : (hΩ.chart i).source ∩ univ ⊆ (hΩ.chart i).source) le_rfl))
    (WeakChangeOfVariables.pullbackCLM_base _ _ _ _)

/-- Physical formula for returning and localizing a whole-space field. -/
theorem localizeLp_apply_ae (i : Fin hΩ.N) (u : Lp F p (domainMeasure n univ)) :
    (localizeLp i u : ℝ^n → F) =ᵐ[domainMeasure n univ]
      fun x ↦ hΩ.boundaryCutoff i x • u (hΩ.chart i x) := by
  let r := Lp.restrictionCLMOfLE
    (Measure.restrict_mono (subset_univ (hΩ.chart i).target) le_rfl) u
  let q := boundedPullbackCLM (F := F)
    (hΩ.chart_contDiff i) (hΩ.chart_symm_contDiff i) (hΩ.chart_target_bounded i) r
  let s := Lp.restrictionCLMOfLE (Measure.restrict_mono
    (inter_subset_left : (hΩ.chart i).source ∩ univ ⊆ (hΩ.chart i).source) le_rfl) q
  have hr := Lp.restrictionCLMOfLE_apply_ae
    (Measure.restrict_mono (subset_univ (hΩ.chart i).target) le_rfl) u
  have hpull := (quasiMeasurePreserving_partialHomeomorph
    (hΩ.chart_contDiff i) (hΩ.chart_symm_contDiff i)).ae_eq_comp hr
  have hq := boundedPullbackLp_apply_ae
    (hΩ.chart_contDiff i) (hΩ.chart_symm_contDiff i) (hΩ.chart_target_bounded i) r
  have hs := Lp.restrictionCLMOfLE_apply_ae (Measure.restrict_mono
    (inter_subset_left : (hΩ.chart i).source ∩ univ ⊆ (hΩ.chart i).source) le_rfl) q
  have hqS := (hq.trans hpull).filter_mono (ae_mono (Measure.restrict_mono
    (inter_subset_left : (hΩ.chart i).source ∩ univ ⊆ (hΩ.chart i).source) le_rfl))
  exact interMultiplierLp_apply_ae (Ω := ⊤)
    (V := ⟨(hΩ.chart i).source, (hΩ.chart i).open_source⟩)
    (hΩ.boundaryCutoff i) (hΩ.boundaryCutoff_support i) s (hs.trans hqS)

end SobolevSpace.VectorValued.GeometricExtension
