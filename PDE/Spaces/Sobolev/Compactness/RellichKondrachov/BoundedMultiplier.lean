/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.Cutoff
public import PDE.DistributionTheory.TestFunction.CompactCutoff

/-!
# Compact multiplication by a bounded coefficient with compact support

An essentially bounded coefficient supported almost everywhere in a compact
set gives a compact operator from whole-space `W¹,p` to `Lp`, for finite `p`.
A smooth cutoff equal to one on that set factors the multiplier through the
compact cutoff observation. No regularity of the coefficient is assumed.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.RellichKondrachov

open MeasureTheory TopologicalSpace
open scoped ENNReal Distributions Sobolev

/-- A bounded multiplier with compact essential support is compact on whole-space `W¹,p`. -/
theorem isCompactOperator_mulLpLeft_comp_base {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (a : DerivLp n ∞ Set.univ) {K : Set (ℝ^n)} (hK : IsCompact K)
    (ha : ∀ᵐ x ∂volume, a x = 0 ∨ x ∈ K) :
    IsCompactOperator ((mulLpLeft (p := p) a).comp
      (wkpBaseCoordinateCLM (n := n) (m := 1) (p := p) (Ω := Set.univ))) := by
  obtain ⟨ψ, _, hψ, _, _⟩ := TestFunction.exists_eq_one_on_compact
    isOpen_univ hK (Set.subset_univ K)
  let F : W^{1,p}(ℝ^n) →L[ℝ] DerivLp n p Set.univ :=
    wkpBaseCoordinateCLM.comp (cutoffCLM (Ω := Set.univ) ψ)
  have hfactor : (mulLpLeft (p := p) a).comp wkpBaseCoordinateCLM =
      (mulLpLeft (p := p) a).comp F := by
    apply ContinuousLinearMap.ext
    intro U
    apply Lp.ext
    simp only [domainMeasure, Measure.restrict_univ]
    have hleft := mulLpLeft_apply_ae a (wkpBaseCoordinateCLM U)
    have hright := mulLpLeft_apply_ae a (F U)
    have hcut := cutoffCLM_base_apply_ae (Ω := Set.univ) ψ U
    simp only [domainMeasure, Measure.restrict_univ] at hleft hright hcut
    filter_upwards [ha, hleft, hright, hcut] with x hx hl hr hc
    change ((mulLpLeft a) (wkpBaseCoordinateCLM U)) x = ((mulLpLeft a) (F U)) x
    rw [hl, hr]
    change a x * wkpBaseCoordinateCLM U x =
      a x * wkpBaseCoordinateCLM (cutoffCLM ψ U) x
    change wkpBaseCoordinateCLM (cutoffCLM ψ U) x =
      ψ.toFun x * wkpBaseCoordinateCLM U x at hc
    rw [hc]
    rcases hx with hz | hx
    · rw [hz, zero_mul, zero_mul]
    · rw [hψ x hx, one_mul]
  rw [hfactor]
  exact (cutoffBaseCoordinate_isCompactOperator hp ψ).clm_comp (mulLpLeft a)

end SobolevSpace.GraphSpace.RellichKondrachov
