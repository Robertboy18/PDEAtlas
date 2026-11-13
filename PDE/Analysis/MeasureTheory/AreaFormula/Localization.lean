/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Localization of measure comparisons along an injective parametrization

A countable open subcover and its disjoint measurable refinement turn local image
estimates into global ones. Both measures may be infinite.
-/

@[expose] public section

open Set Function Filter
open scoped ENNReal Topology

namespace MeasureTheory

variable {E F : Type*}
variable [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
variable [TopologicalSpace F] [T2Space F] [MeasurableSpace F] [BorelSpace F]

/-- Uniform local two-sided image estimates hold globally for an injective continuous
parametrization of a measurable set. -/
theorem measure_image_comparison_of_locally
    {s : Set E} {f : E → F} (hs : MeasurableSet s)
    (hf : ContinuousOn f s) (hinj : InjOn f s)
    (μ : Measure E) (ν : Measure F) (c : ℝ≥0∞)
    (hloc : ∀ x ∈ s, ∃ u ∈ 𝓝 x, ∀ t ⊆ s ∩ u, MeasurableSet t →
      ν (f '' t) ≤ c * μ t ∧ μ t ≤ c * ν (f '' t)) :
    ν (f '' s) ≤ c * μ s ∧ μ s ≤ c * ν (f '' s) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · simp
  let : Nonempty s := hsne.to_subtype
  have hloc' : ∀ x : s, ∃ u : Set E, x.1 ∈ u ∧ IsOpen u ∧
      ∀ t ⊆ s ∩ u, MeasurableSet t →
        ν (f '' t) ≤ c * μ t ∧ μ t ≤ c * ν (f '' t) := by
    intro x
    obtain ⟨u, hu, hcomp⟩ := hloc x x.2
    obtain ⟨v, hvu, hvopen, hxv⟩ := mem_nhds_iff.mp hu
    exact ⟨v, hxv, hvopen, fun t ht ↦
      hcomp t (ht.trans (inter_subset_inter_right s hvu))⟩
  choose u hxu huopen hu using hloc'
  obtain ⟨a, ha⟩ := (HereditarilyLindelofSpace.isLindelof s).indexed_countable_subcover
    u huopen (fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, hxu ⟨x, hx⟩⟩)
  let t : ℕ → Set E := fun n ↦ s ∩ disjointed (u ∘ a) n
  have htmeas : ∀ n, MeasurableSet (t n) :=
    fun n ↦ hs.inter (MeasurableSet.disjointed (fun j ↦ (huopen (a j)).measurableSet) n)
  have htdisj : Pairwise (Disjoint on t) :=
    pairwise_disjoint_mono (disjoint_disjointed _) fun _ ↦ inter_subset_right
  have hts : ∀ n, t n ⊆ s := fun _ ↦ inter_subset_left
  have htcover : s = ⋃ n, t n := by
    dsimp [t]
    rw [← inter_iUnion, iUnion_disjointed]
    exact (inter_eq_left.mpr ha).symm
  have htcomp : ∀ n, ν (f '' t n) ≤ c * μ (t n) ∧ μ (t n) ≤ c * ν (f '' t n) :=
    fun n ↦ hu (a n) (t n)
      (inter_subset_inter_right s (disjointed_subset _ n)) (htmeas n)
  have himage : ν (f '' s) = ∑' n, ν (f '' t n) := by
    rw [htcover, image_iUnion, measure_iUnion]
    · intro i j hij
      exact Disjoint.image (htdisj hij) hinj (hts i) (hts j)
    · exact fun n ↦ (htmeas n).image_of_continuousOn_injOn
        (hf.mono (hts n)) (hinj.mono (hts n))
  have hmeasure : μ s = ∑' n, μ (t n) := by
    rw [htcover, measure_iUnion htdisj htmeas]
  rw [himage, hmeasure]
  constructor
  · rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun n ↦ (htcomp n).1
  · rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun n ↦ (htcomp n).2

end MeasureTheory
