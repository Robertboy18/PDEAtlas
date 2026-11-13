/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Morrey.HigherOrder.GlobalRegularity
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.CompactSupportSupercritical
import PDE.Analysis.MeasureTheory.LocalRepresentative

/-!
# Interior classical representatives of square-integrable Sobolev fields

On any open domain, a `W^{m,2}` field has an interior `C^k` representative when
`m ≥ k + 1 + n / 2`. Cutoffs, global Sobolev and Morrey embeddings, and agreement on
open overlaps construct the representative. No boundary atlas or finite volume is needed.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal Sobolev

private theorem exists_contDiff_global_rep_of_dimension_lt
    {n k m : ℕ} {p : NNReal} [hpFact : Fact (1 ≤ (p : ℝ≥0∞))]
    (hn : 0 < n) (hnp : (n : ℝ) < p) (hkm : k + 1 ≤ m) :
    ∀ U : W^{m,(p : ℝ≥0∞)}(ℝ^n),
    ∃ f : ℝ^n → ℝ, ContDiff ℝ k f ∧ f =ᵐ[volume] baseRepresentative U := by
  have hpR : 1 < (p : ℝ) := lt_of_le_of_lt (by exact_mod_cast hn) hnp
  revert hpFact
  rw [← (ENNReal.ofReal_coe_nnreal (p := p))]
  intro inst V
  let f := finiteMorreyDerivativeEmbedding hn hnp
    (Real.HolderConjugate.conjExponent hpR) [] (by simp only [List.length_nil]; omega) V
  refine ⟨f, ?_, ?_⟩
  · exact finiteMorreyDerivativeEmbedding_contDiff hn hnp
      (Real.HolderConjugate.conjExponent hpR) k [] (by simpa using hkm) V
  · have hf := finiteMorreyDerivativeEmbedding_ae hn hnp
      (Real.HolderConjugate.conjExponent hpR) [] (by simp only [List.length_nil]; omega) V
    simpa only [f, baseRepresentative, derivativeWordIndex_baseIndex,
      derivIndexOfList_nil] using hf

/-- On an arbitrary open domain, a `W^{m,2}` field has a representative that is `C^k`
at every interior point when `m ≥ k + 1 + n / 2`. Smooth cutoffs and global Sobolev
and Morrey embeddings give local representatives; their almost-everywhere agreement
identifies them on overlaps. No boundary regularity or finite volume is assumed. -/
theorem exists_contDiffAt_representative_of_order
    {n k m : ℕ} (hn : 0 < n)
    {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω)
    (U : W^{m,2}(Ω)) (hm : k + 1 + n / 2 ≤ m) :
    ∃ f : ℝ^n → ℝ, (∀ x ∈ Ω, ContDiffAt ℝ k f x) ∧
      f =ᵐ[domainMeasure n Ω] baseRepresentative U := by
  apply MeasureTheory.exists_contDiffAt_ae_eq_of_locally (μ := volume)
  intro x hx
  obtain ⟨N, hN, hxN, hNΩ, q, hq, hqn, V, hV⟩ :=
    exists_global_supercritical_on_nhds hn hΩ U hm hx
  have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq⟩
  obtain ⟨f, hf, hrep⟩ := exists_contDiff_global_rep_of_dimension_lt
    hn hqn (le_refl (k + 1)) V
  have hfN : f =ᵐ[domainMeasure n N] baseRepresentative V :=
    ae_restrict_of_ae hrep
  exact ⟨N, hN, hxN, hNΩ, f, hf.contDiffOn, hfN.trans hV⟩

end SobolevSpace.GraphSpace
