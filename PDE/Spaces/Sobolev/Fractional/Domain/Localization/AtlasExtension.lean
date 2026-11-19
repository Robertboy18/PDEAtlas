/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.AtlasGap
public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.RelativeExtension
public import PDE.Spaces.Sobolev.Fractional.Domain.Pullback.Atlas

/-!
# Local intrinsic extension steps for the C1 atlas

These function-level lemmas connect cutoff, chart transport, and support-gap
extension. The flattened boundary piece is extended only to the upper half-space.
After reflection, the target cutoff permits the inverse-chart piece to be
extended to the whole space. All cutoffs are those of the atlas.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FractionalSobolev

namespace SobolevSpace.Fractional

open SobolevSpace.Boundary SobolevSpace.Boundary.C1ExtensionAtlas.Charts
open SobolevSpace.Boundary.C1ExtensionAtlas.DerivedCutoffs SobolevSpace.HalfSpace

variable {n : ℕ} [Fact (0 < n)] {s : ℝ} {Ω : Set (ℝ^n)}
variable [hΩ : C1ExtensionAtlas n Ω]
variable {p : ℝ≥0∞}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace Pullback

/-- The inverse atlas chart transports intrinsic functions onto the exact
half-space patch. Bounded source geometry follows from the atlas. -/
theorem memGagliardo_comp_atlasChart_symm
    (hs : 0 ≤ (n : ℝ) / p.toReal + s) (i : Fin hΩ.N)
    {u : ℝ^n → F} (hu : MemGagliardo n s ((hΩ.chart i).source ∩ Ω) u (p := p)) :
    MemGagliardo n s ((hΩ.chart i).target ∩ upper n) (u ∘ (hΩ.chart i).symm) (p := p) := by
  have hE : ContDiff ℝ 1 (fun x ↦ chartOnΩ (n := n) (Ω := Ω) i x) :=
    hΩ.chart_contDiff i
  have hSymm : ContDiff ℝ 1 (fun y ↦ (chartOnΩ (n := n) (Ω := Ω) i).symm y) :=
    hΩ.chart_symm_contDiff i
  have hTarget : Bornology.IsBounded (chartOnΩ (n := n) (Ω := Ω) i).target := by
    rw [chartOnΩ_target_eq_target_inter_upper]
    exact (hΩ.chart_target_bounded i).subset inter_subset_left
  have hSource : Bornology.IsBounded (chartOnΩ (n := n) (Ω := Ω) i).source :=
    WeakChangeOfVariables.isBounded_source_of_isBounded_target hSymm.continuous hTarget
  have hu' : MemGagliardo n s (chartOnΩ (n := n) (Ω := Ω) i).source u (p := p) := by
    simpa only [chartOnΩ_source] using hu
  have hout := memGagliardo_comp_of_contDiff
    (E := (chartOnΩ (n := n) (Ω := Ω) i).symm) hs hSymm hE hSource hu'
  change MemGagliardo n s (chartOnΩ (n := n) (Ω := Ω) i).target
    (u ∘ (chartOnΩ (n := n) (Ω := Ω) i).symm) (p := p) at hout
  rw [chartOnΩ_target_eq_target_inter_upper] at hout
  simpa only [chartOnΩ, OpenPartialHomeomorph.coe_restrOpen_symm] using hout

end Pullback

namespace Localization

variable [Fact (1 ≤ p)]

/-- The interior partition piece has a whole-space intrinsic zero extension. -/
theorem memGagliardo_interiorCutoff_zeroExtension
    (hs0 : 0 < s) (hs1 : s < 1)
    {u : ℝ^n → F} (hu : MemGagliardo n s Ω u (p := p))
    (hp : p ≠ ∞ := by norm_num) :
    MemGagliardo n s Set.univ
      (Ω.indicator (fun x ↦ hΩ.interiorCutoff.toFun x • u x)) (p := p) := by
  have hu' : MemGagliardo n s (Ω ∩ Set.univ) u (p := p) := by simpa only [inter_univ] using hu
  simpa only [inter_univ, TestFunction.toFun_eq_coe] using
    memGagliardo_indicator_smul_of_contDiff hs0 hs1 hΩ.isOpen MeasurableSet.univ
      (hΩ.interiorCutoff.contDiff.of_le (by simp)) hΩ.interiorCutoff.hasCompactSupport
      hΩ.interiorCutoff_support hu'
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) hp

/-- The physical boundary partition product can be flattened and extended across
the artificial target edge to the entire upper half-space. -/
theorem memGagliardo_flattenedBoundaryCutoff
    (hs0 : 0 < s) (hs1 : s < 1) (i : Fin hΩ.N)
    {u : ℝ^n → F} (hu : MemGagliardo n s Ω u (p := p))
    (hp : p ≠ ∞ := by norm_num) :
    MemGagliardo n s (upper n)
      (((hΩ.chart i).target ∩ upper n).indicator
        (fun y ↦ (hΩ.boundaryCutoff i).toFun ((hΩ.chart i).symm y) •
          u ((hΩ.chart i).symm y))) (p := p) := by
  have hloc : MemGagliardo n s ((hΩ.chart i).source ∩ Ω)
      (fun x ↦ (hΩ.boundaryCutoff i).toFun x • u x) (p := p) :=
    memGagliardo_smul_of_contDiff_hasCompactSupport hs0 hs1
      ((hΩ.boundaryCutoff i).contDiff.of_le (by simp))
      (hΩ.boundaryCutoff i).hasCompactSupport (hu.mono inter_subset_right)
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) hp
  have hcomp := Pullback.memGagliardo_comp_atlasChart_symm (by positivity) i hloc
  obtain ⟨δ, hδ, hgap⟩ := exists_boundarySupportInTarget_gap (n := n) (Ω := Ω) i
  refine memGagliardo_indicator_of_gap hs0 hδ
    ((hΩ.chart i).open_target.measurableSet.inter (measurableSet_upper n))
    (measurableSet_upper n) inter_subset_right ?_ ?_
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) hp
  · intro x hx hactive y hy
    apply hgap x _ y (fun hyTarget ↦ hy.2 ⟨hyTarget, hy.1⟩)
    refine ⟨(hΩ.chart i).symm x, subset_closure ?_, (hΩ.chart i).right_inv hx.1⟩
    intro hzero
    exact hactive (by simp only [hzero, zero_smul])
  · simpa only [Function.comp_def] using hcomp

/-- On the physical chart patch, flattening retains the original partition product. -/
theorem flattenedBoundaryCutoff_apply_chart
    (i : Fin hΩ.N) (u : ℝ^n → F) {x : ℝ^n}
    (hx : x ∈ (hΩ.chart i).source ∩ Ω) :
    ((hΩ.chart i).target ∩ upper n).indicator
        (fun y ↦ (hΩ.boundaryCutoff i).toFun ((hΩ.chart i).symm y) •
          u ((hΩ.chart i).symm y)) (hΩ.chart i x) =
      (hΩ.boundaryCutoff i).toFun x • u x := by
  have htarget : hΩ.chart i x ∈ (hΩ.chart i).target ∩ upper n :=
    ⟨(hΩ.chart i).map_source hx.1, (hΩ.chart_mem_iff_upper i x hx.1).mp hx.2⟩
  rw [indicator_of_mem htarget, (hΩ.chart i).left_inv hx.1]

/-- A whole-space intrinsic function, relocalized by the target cutoff,
can be pulled back and extended across the artificial source edge. -/
theorem memGagliardo_relocalizedPullback_zeroExtension
    (hs0 : 0 < s) (hs1 : s < 1) (i : Fin hΩ.N)
    {v : ℝ^n → F} (hv : MemGagliardo n s Set.univ v (p := p))
    (hp : p ≠ ∞ := by norm_num) :
    MemGagliardo n s Set.univ
      ((hΩ.chart i).source.indicator
        (fun x ↦ (targetSupportCutoff (n := n) (Ω := Ω) i).toFun (hΩ.chart i x) •
          v (hΩ.chart i x))) (p := p) := by
  have hloc := memGagliardo_smul_of_contDiff_hasCompactSupport hs0 hs1
    ((targetSupportCutoff (n := n) (Ω := Ω) i).contDiff.of_le (by simp))
    (targetSupportCutoff (n := n) (Ω := Ω) i).hasCompactSupport
    (hv.mono (subset_univ (hΩ.chart i).target))
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) hp
  have hcomp := Pullback.memGagliardo_comp_of_contDiff (E := hΩ.chart i) (by positivity)
    (hΩ.chart_contDiff i) (hΩ.chart_symm_contDiff i) (hΩ.chart_target_bounded i) hloc
  obtain ⟨δ, hδ, hgap⟩ := exists_pullbackSupport_gap (n := n) (Ω := Ω) i
  refine memGagliardo_indicator_of_gap hs0 hδ (hΩ.chart i).open_source.measurableSet
    MeasurableSet.univ (subset_univ _) ?_ ?_
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) hp
  · intro x hx hactive y hy
    apply hgap x _ y hy.2
    refine ⟨hΩ.chart i x, subset_closure ?_, (hΩ.chart i).left_inv hx⟩
    intro hzero
    exact hactive (by simp only [hzero, zero_smul])
  · simpa only [Function.comp_def, TestFunction.toFun_eq_coe] using hcomp

end Localization

end SobolevSpace.Fractional
