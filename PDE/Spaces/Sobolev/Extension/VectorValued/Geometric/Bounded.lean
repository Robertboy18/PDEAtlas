/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.VectorValued.Geometric.Extension
public import PDE.Spaces.Sobolev.Extension.VectorValued.HalfSpace.Bounded

/-!
# Essential boundedness of the geometric Sobolev extension

The physical extension on `Lp` preserves essential boundedness.
This is proved for that same operator from its cutoff, chart, and reflection
formulas, without assuming an extension or comparing existentially chosen maps.
-/

@[expose] public noncomputable section

open Filter MeasureTheory TopologicalSpace Set
open scoped Distributions ENNReal Sobolev

namespace SobolevSpace.VectorValued.GeometricExtension

open GraphSpace SobolevSpace.WeakChangeOfVariables
open Boundary.C1ExtensionAtlas.DerivedCutoffs

private theorem exists_bounded_representative
    {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
    {μ : Measure X} (f : X → F) {B : ℝ} (hB : ∀ᵐ x ∂μ, ‖f x‖ ≤ B) :
    ∃ g : X → F, ∃ R : ℝ, 0 ≤ R ∧ f =ᵐ[μ] g ∧ ∀ x, ‖g x‖ ≤ R := by
  classical
  let R := max B 0
  let g (x : X) := if ‖f x‖ ≤ R then f x else 0
  refine ⟨g, R, le_max_right _ _, ?_, ?_⟩
  · filter_upwards [hB] with x hx
    dsimp only [g]
    split_ifs with hg
    · rfl
    · exact (hg (hx.trans (le_max_left _ _))).elim
  · intro x
    dsimp only [g]
    split_ifs with hx
    · exact hx
    · simpa only [norm_zero] using le_max_right B 0

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Relative cutoff multiplication preserves essential boundedness, also
when its input is stored at a different exponent. -/
theorem exists_ae_bound_interMultiplierLp {V Ω : Opens ℝ^n}
    (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (hψ : tsupport ψ.toFun ⊆ V)
    (u : Lp F p (domainMeasure n (V ⊓ Ω))) {B : ℝ}
    (hB : ∀ᵐ x ∂domainMeasure n (V ⊓ Ω), ‖u x‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂domainMeasure n Ω,
      ‖interMultiplierLp ψ hψ u x‖ ≤ C := by
  obtain ⟨g, R, hR, hg, hgR⟩ := exists_bounded_representative u hB
  obtain ⟨D, hD⟩ := ψ.contDiff.continuous.bounded_above_of_compact_support ψ.hasCompactSupport
  refine ⟨max D 0 * R, mul_nonneg (le_max_right _ _) hR, ?_⟩
  filter_upwards [interMultiplierLp_apply_ae ψ hψ u hg] with x hx
  rw [hx, norm_smul]
  exact mul_le_mul ((hD x).trans (le_max_left _ _)) (hgR x) (norm_nonneg _) (le_max_right _ _)

variable [Fact (0 < n)] {Ω : Opens ℝ^n}
  [hΩ : Boundary.C1ExtensionAtlas n (Ω : Set ℝ^n)]

/-- Inverse-chart flattening and its auxiliary cutoff preserve essential bounds. -/
theorem exists_ae_bound_flattenLp (i : Fin hΩ.N)
    (u : Lp F p (domainMeasure n Ω)) {B : ℝ}
    (hB : ∀ᵐ x ∂domainMeasure n Ω, ‖u x‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂domainMeasure n ℝ^n₊, ‖flattenLp i u x‖ ≤ C := by
  obtain ⟨g, R, hR, hg, hgR⟩ := exists_bounded_representative u hB
  let ψ := targetSupportCutoff (Ω := (Ω : Set ℝ^n)) i
  obtain ⟨D, hD⟩ := ψ.contDiff.continuous.bounded_above_of_compact_support ψ.hasCompactSupport
  refine ⟨max D 0 * R, mul_nonneg (le_max_right _ _) hR, ?_⟩
  filter_upwards [flattenLp_ae_eq i u hg] with x hx
  rw [hx, norm_smul]
  exact mul_le_mul ((hD x).trans (le_max_left _ _)) (hgR _) (norm_nonneg _) (le_max_right _ _)

/-- Returning through a chart and multiplying by the partition cutoff
preserves essential bounds on whole-space physical fields. -/
theorem exists_ae_bound_localizeLp (i : Fin hΩ.N)
    (u : Lp F p (domainMeasure n univ)) {B : ℝ}
    (hB : ∀ᵐ x ∂domainMeasure n univ, ‖u x‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂domainMeasure n univ, ‖localizeLp i u x‖ ≤ C := by
  obtain ⟨g, R, hR, hg, hgR⟩ := exists_bounded_representative u hB
  let ψ := hΩ.boundaryCutoff i
  obtain ⟨D, hD⟩ := ψ.contDiff.continuous.bounded_above_of_compact_support ψ.hasCompactSupport
  have ht := hg.filter_mono
    (ae_mono (Measure.restrict_mono (subset_univ (hΩ.chart i).target) le_rfl))
  have hp := (quasiMeasurePreserving_partialHomeomorph
    (hΩ.chart_contDiff i) (hΩ.chart_symm_contDiff i)).ae_eq_comp ht
  have hi := (ae_restrict_iff' (hΩ.chart i).open_source.measurableSet).mp hp
  refine ⟨max D 0 * R, mul_nonneg (le_max_right _ _) hR, ?_⟩
  have hl := localizeLp_apply_ae i u
  simp only [domainMeasure, Measure.restrict_univ] at hl ⊢
  filter_upwards [hl, hi] with x hx hix
  rw [hx]
  by_cases hz : ψ x = 0
  · change ‖ψ x • _‖ ≤ _
    rw [hz, zero_smul, norm_zero]
    exact mul_nonneg (le_max_right _ _) hR
  · have hsource := hΩ.boundaryCutoff_support i (subset_tsupport ψ.toFun hz)
    simp only [Function.comp_apply] at hix
    rw [hix hsource, norm_smul]
    exact mul_le_mul ((hD x).trans (le_max_left _ _)) (hgR _) (norm_nonneg _) (le_max_right _ _)

/-- A reflected boundary patch preserves essential boundedness. -/
theorem exists_ae_bound_boundaryExtensionLp (k : ℕ) (i : Fin hΩ.N)
    (u : Lp F p (domainMeasure n Ω)) {B : ℝ}
    (hB : ∀ᵐ x ∂domainMeasure n Ω, ‖u x‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂domainMeasure n univ,
      ‖boundaryExtensionLp k i u x‖ ≤ C := by
  obtain ⟨_, _, hf⟩ := exists_ae_bound_flattenLp i u hB
  obtain ⟨_, _, hw⟩ := HigherOrderReflection.exists_ae_bound_weightedExtendLp n k p 0 _ hf
  exact exists_ae_bound_localizeLp i _ hw

/-- The assembled `Lp` extension preserves essential boundedness of the input. -/
theorem exists_ae_bound_extensionLp (k : ℕ)
    (u : Lp F p (domainMeasure n Ω)) {B : ℝ}
    (hB : ∀ᵐ x ∂domainMeasure n Ω, ‖u x‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂domainMeasure n univ, ‖extensionLp k u x‖ ≤ C := by
  classical
  let r := Lp.restrictionCLMOfLE (Measure.restrict_mono
    (show ((Ω ⊓ ⊤ : Opens ℝ^n) : Set ℝ^n) ⊆ Ω from inf_le_left) le_rfl) u
  let I := interMultiplierLp (Ω := ⊤) (V := Ω) hΩ.interiorCutoff hΩ.interiorCutoff_support r
  let P (i : Fin hΩ.N) := boundaryExtensionLp k i u
  have hr : ∀ᵐ x ∂domainMeasure n (Ω ⊓ ⊤), ‖r x‖ ≤ B := by
    have hb := hB.filter_mono (ae_mono (Measure.restrict_mono
      (show ((Ω ⊓ ⊤ : Opens ℝ^n) : Set ℝ^n) ⊆ Ω from inf_le_left) le_rfl))
    have he : (r : ℝ^n → F) =ᵐ[domainMeasure n (Ω ⊓ ⊤)] u :=
      Lp.restrictionCLMOfLE_apply_ae _ u
    filter_upwards [he, hb] with x hx hb
    simpa only [hx] using hb
  obtain ⟨C₀, hC₀, hI⟩ := exists_ae_bound_interMultiplierLp
    hΩ.interiorCutoff hΩ.interiorCutoff_support r hr
  have hb (i : Fin hΩ.N) := exists_ae_bound_boundaryExtensionLp k i u hB
  choose C hC hP using hb
  refine ⟨C₀ + ∑ i, C i, add_nonneg hC₀ (Finset.sum_nonneg fun i _ ↦ hC i), ?_⟩
  filter_upwards [hI, ae_all_iff.mpr hP, Lp.coeFn_add I (∑ i, P i),
    Lp.coeFn_finsetSum Finset.univ P] with x hix hpx hadd hsum
  simp only [extensionLp, add_apply, sum_apply, ContinuousLinearMap.comp_apply]
  change ‖(I + ∑ i, P i : Lp F p (domainMeasure n univ)) x‖ ≤ _
  rw [hadd, Pi.add_apply, hsum]
  simp only [Finset.sum_apply]
  exact (norm_add_le _ _).trans (add_le_add hix
    ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ hpx i)))

end SobolevSpace.VectorValued.GeometricExtension
