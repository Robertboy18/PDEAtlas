/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.AtlasExtension
public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.ZeroExtension.Operator

/-!
# Bounded local extension maps from the C1 atlas

The interior partition product extends directly by zero. At a boundary chart,
cutoff and pullback first give a bounded map into the intrinsic source-patch
space. The derived compact support gap then permits whole-space
extension, with the expected physical formula.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FractionalSobolev

namespace SobolevSpace.Fractional.Localization

open SobolevSpace.Boundary SobolevSpace.Boundary.C1ExtensionAtlas.DerivedCutoffs

variable {n : ℕ} [Fact (0 < n)] {s : ℝ} {Ω : Set (ℝ^n)}
variable [hΩ : C1ExtensionAtlas n Ω]

open GagliardoSpace.ZeroExtension

/-- The interior atlas piece is a bounded intrinsic whole-space extension. -/
theorem exists_interiorCutoffCLM (hs0 : 0 < s) (hs1 : s < 1)
    (p : ℝ≥0∞ := 2) (F : Type* := by exact ℝ)
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Fact (1 ≤ p)]
    (hp : p ≠ ∞ := by norm_num) :
    ∃ T : W^{s,p}(Ω; F) →L[ℝ] W^{s,p}(ℝ^n; F),
      ∀ u, (GagliardoSpace.toLp n s Set.univ (T u) : ℝ^n → F)
        =ᵐ[volume.restrict Set.univ]
          Ω.indicator (fun x ↦ hΩ.interiorCutoff.toFun x • GagliardoSpace.toLp n s Ω u x) := by
  obtain ⟨L, M, hL, hM⟩ := exists_cutoff_bounds_of_contDiff
    (hΩ.interiorCutoff.contDiff.of_le (by simp)) hΩ.interiorCutoff.hasCompactSupport
  let Q : W^{s,p}(Ω; F) →L[ℝ] W^{s,p}(Ω; F) :=
    GagliardoSpace.smulCutoffL hs0 hs1 hp hL hM
  have hQ : ∀ u, (GagliardoSpace.toLp n s Ω (Q u) : ℝ^n → F)
      =ᵐ[volume.restrict Ω]
        fun x ↦ hΩ.interiorCutoff.toFun x • GagliardoSpace.toLp n s Ω u x := by
    intro u
    simpa only [Q, TestFunction.toFun_eq_coe] using
      GagliardoSpace.toLp_smulCutoffL_apply_ae hs0 hs1 hp hL hM u
  have hsupport : ∀ u, Q u ∈ supportedSubmodule n s Ω
      (interiorSupport (n := n) (Ω := Ω)) p F := by
    intro u
    apply (mem_supportedSubmodule_iff_of_ae _ (hQ u)).2
    filter_upwards [] with x
    intro hx
    have hzero : hΩ.interiorCutoff.toFun x = 0 := by
      by_contra hne
      exact hx (subset_closure hne)
    rw [hzero, zero_smul]
  obtain ⟨δ, hδ, hgap⟩ := exists_interiorSupport_gap (n := n) (Ω := Ω)
  have hgap' : ∀ x ∈ Ω ∩ interiorSupport (n := n) (Ω := Ω),
      ∀ y ∈ Set.univ \ Ω, δ ≤ dist x y := fun x hx y hy ↦ hgap x hx.2 y hy.2
  let Z : supportedSubmodule n s Ω (interiorSupport (n := n) (Ω := Ω)) p F →L[ℝ]
      W^{s,p}(ℝ^n; F) := extendL hp hs0 hδ hΩ.isOpen.measurableSet MeasurableSet.univ
    (subset_univ Ω) hgap'
  refine ⟨Z.comp (Q.codRestrict _ hsupport), ?_⟩
  intro u
  exact toLp_extendL_of_ae hp hs0 hδ hΩ.isOpen.measurableSet MeasurableSet.univ
    (subset_univ Ω) hgap' _ (hQ u)

/-- The relocalized chart pullback extends to a bounded whole-space map. Its input
is the target-patch intrinsic space; the support gap depends only on the atlas. -/
theorem exists_relocalizedPullbackCLM
    (hs0 : 0 < s) (hs1 : s < 1) (i : Fin hΩ.N)
    (p : ℝ≥0∞ := 2) (F : Type* := by exact ℝ)
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Fact (1 ≤ p)]
    (hp : p ≠ ∞ := by norm_num) :
    ∃ T : W^{s,p}((hΩ.chart i).target; F) →L[ℝ] W^{s,p}(ℝ^n; F),
      ∀ u, (GagliardoSpace.toLp n s Set.univ (T u) : ℝ^n → F)
        =ᵐ[volume.restrict Set.univ] (hΩ.chart i).source.indicator
          (fun x ↦ (targetSupportCutoff (n := n) (Ω := Ω) i).toFun (hΩ.chart i x) •
            GagliardoSpace.toLp n s (hΩ.chart i).target u (hΩ.chart i x)) := by
  obtain ⟨L, M, hL, hM⟩ := exists_cutoff_bounds_of_contDiff
    ((targetSupportCutoff (n := n) (Ω := Ω) i).contDiff.of_le (by simp))
    (targetSupportCutoff (n := n) (Ω := Ω) i).hasCompactSupport
  obtain ⟨P, D, hP, hD⟩ := Pullback.exists_pullback_bounds_of_contDiff
    (E := hΩ.chart i) (hΩ.chart_contDiff i) (hΩ.chart_symm_contDiff i)
    (hΩ.chart_target_bounded i)
  let Q : W^{s,p}((hΩ.chart i).target; F) →L[ℝ] W^{s,p}((hΩ.chart i).target; F) :=
    GagliardoSpace.smulCutoffL hs0 hs1 hp hL hM
  let R := GagliardoSpace.pullbackL (s := s) (p := p) (F := F) (by positivity)
    (hΩ.chart_contDiff i).continuous.measurable hP hD hp
  let T : W^{s,p}((hΩ.chart i).target; F) →L[ℝ]
      W^{s,p}((hΩ.chart i).source; F) := R.comp Q
  let f : W^{s,p}((hΩ.chart i).target; F) → ℝ^n → F := fun u x ↦
    (targetSupportCutoff (n := n) (Ω := Ω) i).toFun (hΩ.chart i x) •
      GagliardoSpace.toLp n s (hΩ.chart i).target u (hΩ.chart i x)
  have hTf : ∀ u, (GagliardoSpace.toLp n s (hΩ.chart i).source (T u) : ℝ^n → F)
      =ᵐ[volume.restrict (hΩ.chart i).source] f u := by
    intro u
    simpa only [T, R, Q, f, ContinuousLinearMap.comp_apply, Function.comp_def,
      TestFunction.toFun_eq_coe] using
      GagliardoSpace.toLp_pullbackL_apply_ae_of_ae_eq (by positivity)
        (hΩ.chart_contDiff i).continuous.measurable hP hD hp (Q u)
        (GagliardoSpace.toLp_smulCutoffL_apply_ae hs0 hs1 hp hL hM u)
  have hsupport : ∀ u, T u ∈ supportedSubmodule n s (hΩ.chart i).source
      (pullbackSupport (n := n) (Ω := Ω) i) p F := by
    intro u
    apply (mem_supportedSubmodule_iff_of_ae _ (hTf u)).2
    filter_upwards [self_mem_ae_restrict (hΩ.chart i).open_source.measurableSet] with x hx
    intro hnot
    have hzero : (targetSupportCutoff (n := n) (Ω := Ω) i).toFun (hΩ.chart i x) = 0 := by
      by_contra hne
      exact hnot ⟨hΩ.chart i x, subset_closure hne, (hΩ.chart i).left_inv hx⟩
    simp only [f, hzero, zero_smul]
  obtain ⟨δ, hδ, hgap⟩ := exists_pullbackSupport_gap (n := n) (Ω := Ω) i
  have hgap' : ∀ x ∈ (hΩ.chart i).source ∩ pullbackSupport (n := n) (Ω := Ω) i,
      ∀ y ∈ Set.univ \ (hΩ.chart i).source, δ ≤ dist x y :=
    fun x hx y hy ↦ hgap x hx.2 y hy.2
  let Z : supportedSubmodule n s (hΩ.chart i).source
      (pullbackSupport (n := n) (Ω := Ω) i) p F →L[ℝ] W^{s,p}(ℝ^n; F) :=
    extendL hp hs0 hδ (hΩ.chart i).open_source.measurableSet MeasurableSet.univ
      (subset_univ _) hgap'
  refine ⟨Z.comp (T.codRestrict _ hsupport), ?_⟩
  intro u
  exact toLp_extendL_of_ae hp hs0 hδ (hΩ.chart i).open_source.measurableSet
    MeasurableSet.univ (subset_univ _) hgap' _ (hTf u)

end SobolevSpace.Fractional.Localization
