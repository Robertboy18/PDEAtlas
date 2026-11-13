/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions

/-!
# Integrability of continuous functions on bounded Euclidean sets

Local integrability facts used by the Sobolev pullback arguments. A continuous scalar
function belongs to every finite `L^p` space on a compact set and is essentially bounded on
every bounded set.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace

open MeasureTheory Set ENNReal

namespace WeakChangeOfVariables

variable {n : ℕ} {p : ℝ≥0∞}

/-- A continuous scalar function belongs to every `Lᵖ` space on a compact Euclidean set. -/
theorem memLp_on_compact_of_continuous {K : Set (ℝ^n)}
    (hK : IsCompact K) {f : ℝ^n → ℝ}
    (hf : Continuous f) : MeasureTheory.MemLp f p (domainMeasure n K) := by
  classical
  -- if `K = ∅`, this is immediate since the restricted measure is zero
  by_cases hK0 : K = ∅
  · subst hK0
    have : (domainMeasure n (∅ : Set (ℝ^n))) = (0 : Measure (ℝ^n)) := by
      simp [domainMeasure]
    -- `MemLp` is automatic for the zero measure
    rw [this]
    exact MeasureTheory.memLp_measure_zero
  -- otherwise, use boundedness of a continuous function on a compact set
  have hKmeas : MeasurableSet K := hK.measurableSet
  let : MeasureTheory.IsFiniteMeasure (domainMeasure n K) :=
    isFiniteMeasure_domainMeasure_of_isBounded hK.isBounded
  let A : ℝ^n → ℝ := fun x ↦ ‖f x‖
  have hAcont : Continuous A := continuous_norm.comp hf
  have hAbdd : BddAbove (A '' K) := (hK.image hAcont).bddAbove
  let C1 : ℝ := sSup (A '' K)
  let C : ℝ := max C1 0
  have hC1 : ∀ x ∈ K, A x ≤ C1 := by
    intro x hx
    have hx' : A x ∈ A '' K := ⟨x, hx, rfl⟩
    exact le_csSup hAbdd hx'
  have hAE : ∀ᵐ x ∂ (domainMeasure n K), ‖f x‖ ≤ C := by
    refine MeasureTheory.ae_restrict_of_forall_mem (μ := volume) (s := K) (hs := hKmeas) ?_
    intro x hx
    have : ‖f x‖ ≤ C1 := hC1 x hx
    exact this.trans (le_max_left _ _)
  exact MeasureTheory.MemLp.of_bound
    (μ := domainMeasure n K) (hf := (hf.aestronglyMeasurable : _)) C hAE

/-- A globally continuous scalar function is essentially bounded on every bounded Euclidean set. -/
theorem memLp_top_on_bounded_of_continuous {S : Set (ℝ^n)}
    (hS : Bornology.IsBounded S) {f : ℝ^n → ℝ} (hf : Continuous f) :
    MeasureTheory.MemLp f (⊤ : ℝ≥0∞) (domainMeasure n S) := by
  have hcompact : IsCompact (closure S) := hS.isCompact_closure
  have hclosure : MeasureTheory.MemLp f (⊤ : ℝ≥0∞) (domainMeasure n (closure S)) :=
    memLp_on_compact_of_continuous (n := n) (p := (⊤ : ℝ≥0∞)) hcompact hf
  have hrestricted := hclosure.restrict S
  simpa [domainMeasure, Measure.restrict_restrict_of_subset subset_closure] using hrestricted

end WeakChangeOfVariables

end SobolevSpace
