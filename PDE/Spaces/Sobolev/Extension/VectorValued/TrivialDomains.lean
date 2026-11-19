/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Restriction

/-!
# Sobolev extension on empty and full domains

On the empty domain there is only the zero Sobolev class; on the full space the
identity already extends every function. These cases also settle dimension zero,
where every open domain is empty or full. The extension and its `Lp` companion
agree on the base coordinate, at every derivative order and exponent.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Empty and full domains admit compatible Sobolev and `Lp` extension operators. -/
theorem exists_extension_with_lp_of_bot_or_top (hΩ : Ω = ⊥ ∨ Ω = ⊤) :
    ∃ E : W^{k,p}(Ω; F) →L[ℝ] W^{k,p}(ℝ^n; F),
      ∃ E₀ : Lp F p (domainMeasure n Ω) →L[ℝ] Lp F p (domainMeasure n Set.univ),
        (∀ U, coordinateCLM (baseIndex n k) (E U) =
          E₀ (coordinateCLM (baseIndex n k) U)) ∧
        (∀ u, Lp.restrictionCLMOfLE
          (Measure.restrict_mono (Set.subset_univ (Ω : Set ℝ^n)) le_rfl) (E₀ u) = u) ∧
        (∀ U, restrictCLM (show Ω ≤ ⊤ from le_top) (E U) = U) := by
  rcases hΩ with rfl | rfl
  · have hLp (u : Lp F p (domainMeasure n (⊥ : Opens ℝ^n))) : u = 0 := by
      apply Lp.ext
      simp only [domainMeasure, Opens.coe_bot, Measure.restrict_empty, ae_zero]
      exact Filter.eventually_bot
    have hSobolev (U : W^{k,p}((⊥ : Opens ℝ^n); F)) : U = 0 := by
      apply baseCoordinateCLM_injective
      simpa only [map_zero] using hLp (coordinateCLM (baseIndex n k) U)
    refine ⟨0, 0, ?_, ?_, ?_⟩
    · intro U
      simp
    · intro u
      simpa only [zero_apply, map_zero] using (hLp u).symm
    · intro U
      simpa only [zero_apply, map_zero] using (hSobolev U).symm
  · refine ⟨ContinuousLinearMap.id ℝ _, ContinuousLinearMap.id ℝ _, ?_, ?_, ?_⟩
    · intro U
      rfl
    · intro u
      apply Lp.ext
      exact Lp.restrictionCLMOfLE_apply_ae _ u
    · intro U
      simp

/-- In dimension zero every open domain is empty or full, so no boundary chart is needed. -/
theorem exists_extension_with_lp_dimension_zero {Ω : Opens ℝ^0} :
    ∃ E : W^{k,p}(Ω; F) →L[ℝ] W^{k,p}(ℝ^0; F),
      ∃ E₀ : Lp F p (domainMeasure 0 Ω) →L[ℝ] Lp F p (domainMeasure 0 Set.univ),
        (∀ U, coordinateCLM (baseIndex 0 k) (E U) =
          E₀ (coordinateCLM (baseIndex 0 k) U)) ∧
        (∀ u, Lp.restrictionCLMOfLE
          (Measure.restrict_mono (Set.subset_univ (Ω : Set ℝ^0)) le_rfl) (E₀ u) = u) ∧
        (∀ U, restrictCLM (show Ω ≤ ⊤ from le_top) (E U) = U) := by
  apply exists_extension_with_lp_of_bot_or_top
  by_cases hΩ : (Ω : Set ℝ^0).Nonempty
  · right
    obtain ⟨x, hx⟩ := hΩ
    apply top_unique
    intro y _
    change y ∈ (Ω : Set ℝ^0)
    exact (Subsingleton.elim x y) ▸ hx
  · left
    apply bot_unique
    intro x hx
    exact hΩ ⟨x, hx⟩

end SobolevSpace.VectorValued
