/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.Distribution

/-!
# Finite sums of regular distributions

Local integrability is preserved by a finite sum, and the distribution
represented by that sum is the sum of the represented distributions. This
holds on any open domain and for any finite or infinite test order.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped Distributions

namespace Distribution

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {μ : Measure E} {k : ℕ∞}

/-- Forming the ordinary distribution of a finite sum commutes with that sum
when the summands are locally integrable on the testing domain. -/
theorem ofFun_finsetSum (s : Finset ι) (f : ι → E → F)
    (hf : ∀ i ∈ s, LocallyIntegrableOn (f i) (Ω : Set E) μ) :
    ofFun Ω (∑ i ∈ s, f i) μ k = ∑ i ∈ s, ofFun Ω (f i) μ k := by
  classical
  suffices ∀ s : Finset ι, (∀ i ∈ s, LocallyIntegrableOn (f i) (Ω : Set E) μ) →
      LocallyIntegrableOn (∑ i ∈ s, f i) (Ω : Set E) μ ∧
        ofFun Ω (∑ i ∈ s, f i) μ k = ∑ i ∈ s, ofFun Ω (f i) μ k from
    (this s hf).2
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simp only [Finset.sum_empty]
      exact ⟨locallyIntegrableOn_zero, ofFun_zero⟩
  | @insert i s hi ih =>
      intro hf
      obtain ⟨hlocal, heq⟩ := ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))
      have hfi := hf i (Finset.mem_insert_self i s)
      simp only [Finset.sum_insert hi]
      exact ⟨hfi.add hlocal, (ofFun_add hfi hlocal).trans (congrArg (fun T ↦ _ + T) heq)⟩

end Distribution
