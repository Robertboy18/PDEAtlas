/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.AtlasOperator
public import PDE.Spaces.Sobolev.Fractional.Domain.Extension.Reflection

/-!
# Bounded extension of an atlas boundary piece

The source cutoff is flattened onto the exact upper-half-space patch. Its
transported support gap permits relative zero extension. Even reflection and
the target cutoff then give a bounded whole-space map with the original
partition product as its physical restriction.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FractionalSobolev

namespace SobolevSpace.Fractional.Localization

open SobolevSpace.Boundary SobolevSpace.Boundary.C1ExtensionAtlas.Charts
open SobolevSpace.Boundary.C1ExtensionAtlas.DerivedCutoffs SobolevSpace.HalfSpace
open GagliardoSpace GagliardoSpace.ZeroExtension

variable {n : ℕ} [Fact (0 < n)] {s : ℝ} {Ω : Set (ℝ^n)}
variable [hΩ : C1ExtensionAtlas n Ω]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The inverse chart transports almost-everywhere statements on the physical patch. -/
private theorem quasiMeasurePreserving_chartOnΩ_symm (i : Fin hΩ.N) :
    QuasiMeasurePreserving (fun y ↦ (hΩ.chart i).symm y)
      (volume.restrict ((hΩ.chart i).target ∩ upper n))
      (volume.restrict ((hΩ.chart i).source ∩ Ω)) := by
  have h := WeakChangeOfVariables.quasiMeasurePreserving_partialHomeomorph
    (E := (chartOnΩ (n := n) (Ω := Ω) i).symm)
    (hΩ.chart_symm_contDiff i) (hΩ.chart_contDiff i)
  change QuasiMeasurePreserving
    (fun y ↦ (chartOnΩ (n := n) (Ω := Ω) i).symm y)
    (volume.restrict (chartOnΩ (n := n) (Ω := Ω) i).target)
    (volume.restrict (chartOnΩ (n := n) (Ω := Ω) i).source) at h
  rw [chartOnΩ_source, chartOnΩ_target_eq_target_inter_upper] at h
  simpa only [chartOnΩ, OpenPartialHomeomorph.coe_restrOpen_symm] using h

/-- The cutoff product, transported to the upper patch before zero extension. -/
private theorem exists_flattenedBoundaryCutoffOnPatchCLM
    (hs0 : 0 < s) (hs1 : s < 1) (i : Fin hΩ.N) (hp : p ≠ ∞) :
    ∃ T : W^{s,p}(Ω; F) →L[ℝ]
        W^{s,p}((hΩ.chart i).target ∩ upper n; F),
      ∀ u, (toLp n s ((hΩ.chart i).target ∩ upper n) (T u) : ℝ^n → F)
        =ᵐ[volume.restrict ((hΩ.chart i).target ∩ upper n)]
          fun y ↦ (hΩ.boundaryCutoff i).toFun ((hΩ.chart i).symm y) •
            toLp n s Ω u ((hΩ.chart i).symm y) := by
  obtain ⟨L, M, hL, hM⟩ := exists_cutoff_bounds_of_contDiff
    ((hΩ.boundaryCutoff i).contDiff.of_le (by simp))
    (hΩ.boundaryCutoff i).hasCompactSupport
  obtain ⟨P, _, hP⟩ := Pullback.exists_atlasChart_pullbackEquiv (s := s)
    (p := p) (F := F) (by positivity) i hp
  let Q : W^{s,p}(Ω; F) →L[ℝ]
      W^{s,p}((hΩ.chart i).source ∩ Ω; F) :=
    (smulCutoffL hs0 hs1 hp hL hM).comp (restrictCLM inter_subset_right)
  let T : W^{s,p}(Ω; F) →L[ℝ]
      W^{s,p}((hΩ.chart i).target ∩ upper n; F) :=
    P.symm.toContinuousLinearMap.comp Q
  let f : W^{s,p}(Ω; F) → ℝ^n → F := fun u y ↦
    (hΩ.boundaryCutoff i).toFun ((hΩ.chart i).symm y) •
      toLp n s Ω u ((hΩ.chart i).symm y)
  have hq := quasiMeasurePreserving_chartOnΩ_symm (n := n) (Ω := Ω) i
  have hTf : ∀ u, (toLp n s ((hΩ.chart i).target ∩ upper n) (T u) : ℝ^n → F)
      =ᵐ[volume.restrict ((hΩ.chart i).target ∩ upper n)] f u := by
    intro u
    have hQ : (toLp n s ((hΩ.chart i).source ∩ Ω) (Q u) : ℝ^n → F)
        =ᵐ[volume.restrict ((hΩ.chart i).source ∩ Ω)]
          fun x ↦ (hΩ.boundaryCutoff i).toFun x • toLp n s Ω u x := by
      filter_upwards [
        toLp_smulCutoffL_apply_ae hs0 hs1 hp hL hM (restrictCLM inter_subset_right u),
        toLp_restrictCLM_apply_ae
          (show (hΩ.chart i).source ∩ Ω ⊆ Ω from inter_subset_right) u] with x hx hr
      exact hx.trans (congrArg ((hΩ.boundaryCutoff i).toFun x • ·) hr)
    exact (hP (Q u)).trans (hq.ae hQ)
  exact ⟨T, hTf⟩

/-- Flattening the boundary partition product gives a bounded map into the
intrinsic upper-half-space space, including the artificial-edge extension. -/
theorem exists_flattenedBoundaryCutoffCLM
    (hs0 : 0 < s) (hs1 : s < 1) (i : Fin hΩ.N)
    (p : ℝ≥0∞ := 2) (F : Type* := by exact ℝ)
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Fact (1 ≤ p)]
    (hp : p ≠ ∞ := by norm_num) :
    ∃ T : W^{s,p}(Ω; F) →L[ℝ] W^{s,p}(upper n; F),
      ∀ u, (toLp n s (upper n) (T u) : ℝ^n → F) =ᵐ[volume.restrict (upper n)]
        ((hΩ.chart i).target ∩ upper n).indicator
          (fun y ↦ (hΩ.boundaryCutoff i).toFun ((hΩ.chart i).symm y) •
            toLp n s Ω u ((hΩ.chart i).symm y)) := by
  obtain ⟨T, hTf⟩ := exists_flattenedBoundaryCutoffOnPatchCLM (p := p) (F := F) hs0 hs1 i hp
  have hsupport : ∀ u, T u ∈ supportedSubmodule n s ((hΩ.chart i).target ∩ upper n)
      (boundarySupportInTarget (n := n) (Ω := Ω) i) p F := by
    intro u
    apply (mem_supportedSubmodule_iff_of_ae _ (hTf u)).2
    filter_upwards [self_mem_ae_restrict
      ((hΩ.chart i).open_target.measurableSet.inter (measurableSet_upper n))] with y hy
    intro hnot
    have hzero : (hΩ.boundaryCutoff i).toFun ((hΩ.chart i).symm y) = 0 := by
      by_contra hne
      exact hnot ⟨(hΩ.chart i).symm y, subset_closure hne, (hΩ.chart i).right_inv hy.1⟩
    simp only [hzero, zero_smul]
  obtain ⟨δ, hδ, hgap⟩ := exists_boundarySupportInTarget_gap (n := n) (Ω := Ω) i
  have hgap' : ∀ x ∈ ((hΩ.chart i).target ∩ upper n) ∩
      boundarySupportInTarget (n := n) (Ω := Ω) i,
      ∀ y ∈ upper n \ ((hΩ.chart i).target ∩ upper n), δ ≤ dist x y :=
    fun x hx y hy ↦ hgap x hx.2 y (fun hyTarget ↦ hy.2 ⟨hyTarget, hy.1⟩)
  let Z : supportedSubmodule n s ((hΩ.chart i).target ∩ upper n)
      (boundarySupportInTarget (n := n) (Ω := Ω) i) p F →L[ℝ] W^{s,p}(upper n; F) :=
    extendL hp hs0 hδ
      ((hΩ.chart i).open_target.measurableSet.inter (measurableSet_upper n))
      (measurableSet_upper n) inter_subset_right hgap'
  refine ⟨Z.comp (T.codRestrict _ hsupport), ?_⟩
  intro u
  exact toLp_extendL_of_ae hp hs0 hδ
    ((hΩ.chart i).open_target.measurableSet.inter (measurableSet_upper n))
    (measurableSet_upper n) inter_subset_right hgap' _ (hTf u)

/-- Reflection and the target cutoff preserve the original product inside its chart. -/
private theorem targetSupportCutoff_smul_flattened_eq
    (i : Fin hΩ.N) (v : ℝ^n → F) {x : ℝ^n}
    (hx : x ∈ (hΩ.chart i).source) (hxΩ : x ∈ Ω) :
    (targetSupportCutoff (n := n) (Ω := Ω) i).toFun (hΩ.chart i x) •
      ((hΩ.chart i).target ∩ upper n).indicator
        (fun y ↦ (hΩ.boundaryCutoff i).toFun ((hΩ.chart i).symm y) •
          v ((hΩ.chart i).symm y)) (Extension.foldUpper n (hΩ.chart i x)) =
      (hΩ.boundaryCutoff i).toFun x • v x := by
  have hupper : hΩ.chart i x ∈ upper n := (hΩ.chart_mem_iff_upper i x hx).mp hxΩ
  rw [Extension.foldUpper_of_mem_upper n hupper,
    flattenedBoundaryCutoff_apply_chart i v ⟨hx, hxΩ⟩]
  by_cases hψ : (hΩ.boundaryCutoff i).toFun x = 0
  · simp only [hψ, zero_smul, smul_zero]
  · have hsupport : hΩ.chart i x ∈ boundarySupportInTarget (n := n) (Ω := Ω) i :=
      ⟨x, subset_closure (show x ∈ Function.support (hΩ.boundaryCutoff i).toFun from hψ),
        rfl⟩
    rw [targetSupportCutoff_eq_one_on_boundarySupportInTarget i _ hsupport, one_smul]

/-- Restricting an even reflection preserves its folded physical representative. -/
private theorem toLp_restrict_evenReflectionCLM_apply_ae
    (hs : 0 ≤ (n : ℝ) / p.toReal + s) (A : Set (ℝ^n))
    (v : W^{s,p}(upper n; F)) {f : ℝ^n → F}
    (hv : (toLp n s (upper n) v : ℝ^n → F) =ᵐ[volume.restrict (upper n)] f) :
    (toLp n s A
        (restrictCLM (subset_univ A) (Extension.evenReflectionCLM hs v)) : ℝ^n → F)
      =ᵐ[volume.restrict A] fun y ↦ f (Extension.foldUpper n y) := by
  have hfold : (fun y ↦ toLp n s (upper n) v (Extension.foldUpper n y))
      =ᵐ[volume] fun y ↦ f (Extension.foldUpper n y) :=
    (Extension.measurePreserving_foldUpper n).quasiMeasurePreserving.ae
      (Measure.ae_smul_measure hv (2 : ℝ≥0∞))
  have hR : (toLp n s Set.univ (Extension.evenReflectionCLM hs v) : ℝ^n → F)
      =ᵐ[volume] fun y ↦ f (Extension.foldUpper n y) :=
    (Extension.toLp_evenReflectionCLM_apply_ae hs v).trans hfold
  exact (toLp_restrictCLM_apply_ae (subset_univ A)
    (Extension.evenReflectionCLM hs v)).trans (ae_restrict_of_ae hR)

/-- Each boundary partition product has a bounded intrinsic whole-space
extension. Its restriction is the physical product on the original domain. -/
theorem exists_boundaryPieceCLM
    (hs0 : 0 < s) (hs1 : s < 1) (i : Fin hΩ.N)
    (p : ℝ≥0∞ := 2) (F : Type* := by exact ℝ)
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Fact (1 ≤ p)]
    (hp : p ≠ ∞ := by norm_num) :
    ∃ T : W^{s,p}(Ω; F) →L[ℝ] W^{s,p}(ℝ^n; F),
      ∀ u, (toLp n s Set.univ (T u) : ℝ^n → F) =ᵐ[volume.restrict Ω]
        fun x ↦ (hΩ.boundaryCutoff i).toFun x • toLp n s Ω u x := by
  classical
  obtain ⟨Tflat, hF⟩ := exists_flattenedBoundaryCutoffCLM hs0 hs1 i p F hp
  obtain ⟨B, hB⟩ := exists_relocalizedPullbackCLM hs0 hs1 i p F hp
  let R := Extension.evenReflectionCLM (n := n) (s := s) (p := p) (F := F) (by positivity)
  let Q : W^{s,p}(ℝ^n; F) →L[ℝ]
      W^{s,p}((hΩ.chart i).target; F) :=
    restrictCLM (subset_univ _)
  let T := B.comp (Q.comp (R.comp Tflat))
  refine ⟨T, fun u ↦ ?_⟩
  let f : ℝ^n → F := ((hΩ.chart i).target ∩ upper n).indicator
    (fun y ↦ (hΩ.boundaryCutoff i).toFun ((hΩ.chart i).symm y) •
      toLp n s Ω u ((hΩ.chart i).symm y))
  have hQ : (toLp n s (hΩ.chart i).target (Q (R (Tflat u))) : ℝ^n → F)
      =ᵐ[volume.restrict (hΩ.chart i).target] fun y ↦ f (Extension.foldUpper n y) :=
    toLp_restrict_evenReflectionCLM_apply_ae (by positivity) _ (Tflat u) (hF u)
  have hq : QuasiMeasurePreserving (fun x ↦ hΩ.chart i x)
      (volume.restrict (hΩ.chart i).source) (volume.restrict (hΩ.chart i).target) :=
    WeakChangeOfVariables.quasiMeasurePreserving_partialHomeomorph
      (hΩ.chart_contDiff i) (hΩ.chart_symm_contDiff i)
  have hcomp : ∀ᵐ x ∂volume, x ∈ (hΩ.chart i).source →
      toLp n s (hΩ.chart i).target (Q (R (Tflat u))) (hΩ.chart i x) =
        f (Extension.foldUpper n (hΩ.chart i x)) :=
    (ae_restrict_iff' (hΩ.chart i).open_source.measurableSet).mp (hq.ae hQ)
  have hBvol : (toLp n s Set.univ (T u) : ℝ^n → F) =ᵐ[volume]
      (hΩ.chart i).source.indicator
        (fun x ↦ (targetSupportCutoff (n := n) (Ω := Ω) i).toFun (hΩ.chart i x) •
          toLp n s (hΩ.chart i).target (Q (R (Tflat u))) (hΩ.chart i x)) := by
    simpa only [T, ContinuousLinearMap.comp_apply, Measure.restrict_univ]
      using hB (Q (R (Tflat u)))
  filter_upwards [ae_restrict_of_ae hBvol, ae_restrict_of_ae hcomp,
    ae_restrict_mem hΩ.isOpen.measurableSet] with x hb hc hxΩ
  rw [hb]
  by_cases hx : x ∈ (hΩ.chart i).source
  · rw [indicator_of_mem hx, hc hx]
    exact targetSupportCutoff_smul_flattened_eq i (toLp n s Ω u) hx hxΩ
  · have hψ : (hΩ.boundaryCutoff i).toFun x = 0 := by
      by_contra h
      exact hx (hΩ.boundaryCutoff_support i
        (subset_closure (show x ∈ Function.support (hΩ.boundaryCutoff i).toFun from h)))
    rw [indicator_of_notMem hx, hψ, zero_smul]

end SobolevSpace.Fractional.Localization
