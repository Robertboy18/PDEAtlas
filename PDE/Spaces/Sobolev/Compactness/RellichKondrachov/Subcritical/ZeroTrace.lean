/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.CompactEmbedding
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.FirstOrder.ZeroTrace
import PDE.Spaces.Sobolev.Compactness.Rellich.ZeroExtension

/-!
# Compact finite-exponent embeddings of H¹₀

On a bounded measurable set, `H¹₀` embeds compactly into every finite `Lᑫ`
with `q ≥ 2` strictly below the Sobolev critical exponent. In dimensions one and
two every finite exponent is allowed. The continuous embeddings already cover
these dimensions; the proof here combines them with compactness in `L²` and the
generic Vitali compactness transfer.

No boundary atlas or smoothness assumption is needed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The `H¹₀ → L^q` inclusion is compact for `2 ≤ q < 2*`, and for every finite `q ≥ 2`
when `n ≤ 2`. -/
theorem h10LpEmbedding_isCompactOperator
    (hn : 0 < n) (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω)
    {q : ℝ} (hq : 2 ≤ q)
    (hnq : 2 < n → q < 2 * (n : ℝ) / ((n : ℝ) - 2)) :
    have : IsFiniteMeasure (domainMeasure n Ω) :=
      isFiniteMeasure_domainMeasure_of_isBounded hbounded
    have : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
    IsCompactOperator (h10LpEmbedding hn hΩ hq (fun h ↦ (hnq h).le)) := by
  have : IsFiniteMeasure (domainMeasure n Ω) :=
    isFiniteMeasure_domainMeasure_of_isBounded hbounded
  have : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  obtain ⟨r, hqr, hr⟩ :
      ∃ r : ℝ, q < r ∧ (2 < n → r ≤ 2 * (n : ℝ) / ((n : ℝ) - 2)) := by
    by_cases hn2 : 2 < n
    · obtain ⟨r, hqr, hr⟩ := exists_between (hnq hn2)
      exact ⟨r, hqr, fun _ ↦ hr.le⟩
    · exact ⟨q + 1, by linarith, fun h ↦ (hn2 h).elim⟩
  have hr2 : 2 ≤ r := hq.trans hqr.le
  let qn : ℝ≥0 := ⟨q, by linarith⟩
  let rn : ℝ≥0 := ⟨r, by linarith⟩
  have hqn : (qn : ℝ≥0∞) = ENNReal.ofReal q := ENNReal.coe_nnreal_eq qn
  have hrn : (rn : ℝ≥0∞) = ENNReal.ofReal r := ENNReal.coe_nnreal_eq rn
  have : Fact (1 ≤ ENNReal.ofReal r) := ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  have hcompact := baseCoordCLM.isCompactOperator_of_bounded hΩ hbounded
  have transfer {s t : ℝ≥0∞} [Fact (1 ≤ s)] [Fact (1 ≤ t)]
      (hs : s = (qn : ℝ≥0∞)) (ht : t = (rn : ℝ≥0∞))
      (Jq : H¹₀(Ω) →L[ℝ] Lp ℝ s (domainMeasure n Ω))
      (Jr : H¹₀(Ω) →L[ℝ] Lp ℝ t (domainMeasure n Ω))
      (hqae : ∀ u, (Jq u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] baseCoordCLM u)
      (hrae : ∀ u, (Jr u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] baseCoordCLM u) :
      IsCompactOperator Jq := by
    subst s t
    exact hcompact.into_Lp_of_higher_exponent Jq Jr hqr
      (fun u ↦ (hqae u).symm) (fun u ↦ (hrae u).trans (hqae u).symm)
  exact transfer hqn.symm hrn.symm
    (h10LpEmbedding hn hΩ hq (fun h ↦ (hnq h).le))
    (h10LpEmbedding hn hΩ hr2 hr)
    (h10LpEmbedding_ae hn hΩ hq (fun h ↦ (hnq h).le))
    (h10LpEmbedding_ae hn hΩ hr2 hr)

end SobolevSpace.GraphSpace
