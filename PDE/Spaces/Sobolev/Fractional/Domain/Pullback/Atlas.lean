/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Definitions
public import PDE.Spaces.Sobolev.Fractional.Domain.Pullback.C1

/-!
# Fractional pullback on the C1 atlas

Restricting an atlas chart to the physical domain gives a bounded equivalence
between the intrinsic space on `source ∩ Ω` and that on `target ∩ upper n`.
Both physical composition formulas are retained. The target remains the
halfspace patch: extension across its artificial edges is a separate step.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FractionalSobolev

namespace SobolevSpace.Fractional.Pullback

open SobolevSpace.Boundary SobolevSpace.Boundary.C1ExtensionAtlas.Charts
open SobolevSpace.HalfSpace GagliardoSpace

variable {n : ℕ} [Fact (0 < n)] {s : ℝ} {Ω : Set (ℝ^n)} [hΩ : C1ExtensionAtlas n Ω]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞}

/-- Pulling an intrinsic function back through a boundary chart preserves its
fractional condition on the physical part of that chart. -/
theorem memGagliardo_comp_atlasChart
    (hs : 0 ≤ (n : ℝ) / p.toReal + s) (i : Fin hΩ.N)
    {u : ℝ^n → F} (hu : MemGagliardo n s ((hΩ.chart i).target ∩ upper n) u (p := p)) :
    MemGagliardo n s ((hΩ.chart i).source ∩ Ω) (u ∘ hΩ.chart i) (p := p) := by
  have hE : ContDiff ℝ 1 (fun x ↦ chartOnΩ (n := n) (Ω := Ω) i x) :=
    hΩ.chart_contDiff i
  have hSymm : ContDiff ℝ 1 (fun y ↦ (chartOnΩ (n := n) (Ω := Ω) i).symm y) :=
    hΩ.chart_symm_contDiff i
  have hTarget : Bornology.IsBounded (chartOnΩ (n := n) (Ω := Ω) i).target := by
    rw [chartOnΩ_target_eq_target_inter_upper]
    exact (hΩ.chart_target_bounded i).subset inter_subset_left
  have hu' : MemGagliardo n s (chartOnΩ (n := n) (Ω := Ω) i).target u (p := p) := by
    simpa only [chartOnΩ_target_eq_target_inter_upper] using hu
  have hout := memGagliardo_comp_of_contDiff hs hE hSymm hTarget hu'
  rw [chartOnΩ_source] at hout
  simpa only [chartOnΩ, OpenPartialHomeomorph.coe_restrOpen] using hout

variable [Fact (1 ≤ p)]

/-- The chart equivalence first lives on the source and target of the restricted chart. -/
private theorem exists_chartOnΩ_pullbackEquiv
    (hs : 0 ≤ (n : ℝ) / p.toReal + s) (i : Fin hΩ.N) (hp : p ≠ ∞ := by norm_num) :
    ∃ T : W^{s,p}((chartOnΩ (n := n) (Ω := Ω) i).target; F) ≃L[ℝ]
        W^{s,p}((chartOnΩ (n := n) (Ω := Ω) i).source; F),
      (∀ u, (toLp n s (chartOnΩ (n := n) (Ω := Ω) i).source (T u) : ℝ^n → F)
        =ᵐ[volume.restrict (chartOnΩ (n := n) (Ω := Ω) i).source]
          (toLp n s (chartOnΩ (n := n) (Ω := Ω) i).target u : ℝ^n → F) ∘
            chartOnΩ (n := n) (Ω := Ω) i) ∧
      (∀ v, (toLp n s (chartOnΩ (n := n) (Ω := Ω) i).target (T.symm v) : ℝ^n → F)
        =ᵐ[volume.restrict (chartOnΩ (n := n) (Ω := Ω) i).target]
          (toLp n s (chartOnΩ (n := n) (Ω := Ω) i).source v : ℝ^n → F) ∘
            (chartOnΩ (n := n) (Ω := Ω) i).symm) := by
  have hE : ContDiff ℝ 1 (fun x ↦ chartOnΩ (n := n) (Ω := Ω) i x) :=
    hΩ.chart_contDiff i
  have hSymm : ContDiff ℝ 1 (fun y ↦ (chartOnΩ (n := n) (Ω := Ω) i).symm y) :=
    hΩ.chart_symm_contDiff i
  have hTarget : Bornology.IsBounded (chartOnΩ (n := n) (Ω := Ω) i).target := by
    rw [chartOnΩ_target_eq_target_inter_upper]
    exact (hΩ.chart_target_bounded i).subset inter_subset_left
  exact ⟨pullbackC1Equiv (p := p) (F := F) hs hE hSymm hTarget hp,
      fun u ↦ toLp_pullbackC1Equiv_apply_ae hs hE hSymm hTarget u hp,
      fun v ↦ toLp_pullbackC1Equiv_symm_apply_ae hs hE hSymm hTarget v hp⟩

/-- Every atlas boundary chart gives an intrinsic fractional equivalence,
with forward and inverse physical formulas on the exact domain patches. -/
theorem exists_atlasChart_pullbackEquiv
    (hs : 0 ≤ (n : ℝ) / p.toReal + s) (i : Fin hΩ.N) (hp : p ≠ ∞ := by norm_num) :
    ∃ T : W^{s,p}((hΩ.chart i).target ∩ upper n; F) ≃L[ℝ]
        W^{s,p}((hΩ.chart i).source ∩ Ω; F),
      (∀ u, (toLp n s ((hΩ.chart i).source ∩ Ω) (T u) : ℝ^n → F)
        =ᵐ[volume.restrict ((hΩ.chart i).source ∩ Ω)]
          (toLp n s ((hΩ.chart i).target ∩ upper n) u : ℝ^n → F) ∘ hΩ.chart i) ∧
      (∀ v, (toLp n s ((hΩ.chart i).target ∩ upper n) (T.symm v) : ℝ^n → F)
        =ᵐ[volume.restrict ((hΩ.chart i).target ∩ upper n)]
          (toLp n s ((hΩ.chart i).source ∩ Ω) v : ℝ^n → F) ∘ (hΩ.chart i).symm) := by
  let P (source target : Set (ℝ^n)) : Prop :=
    ∃ T : W^{s,p}(target; F) ≃L[ℝ] W^{s,p}(source; F),
      (∀ u, (toLp n s source (T u) : ℝ^n → F)
        =ᵐ[volume.restrict source] (toLp n s target u : ℝ^n → F) ∘ hΩ.chart i) ∧
      (∀ v, (toLp n s target (T.symm v) : ℝ^n → F)
        =ᵐ[volume.restrict target] (toLp n s source v : ℝ^n → F) ∘ (hΩ.chart i).symm)
  have h : P (chartOnΩ (n := n) (Ω := Ω) i).source
      (chartOnΩ (n := n) (Ω := Ω) i).target := by
    obtain ⟨T, hT, hTinv⟩ := exists_chartOnΩ_pullbackEquiv (F := F) hs i hp
    exact ⟨T, hT, hTinv⟩
  exact (congrArg₂ P (chartOnΩ_source (n := n) (Ω := Ω) i)
    (chartOnΩ_target_eq_target_inter_upper (n := n) (Ω := Ω) i)).mp h

end SobolevSpace.Fractional.Pullback
