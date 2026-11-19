/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.WeakSequentialCompactness

/-!
# A sequential direct method for extended energies

An extended nonnegative energy attains a finite minimum on a weakly sequentially closed admissible
set when one finite sublevel is bounded and the energy is lower semicontinuous along
bounded weakly convergent sequences. Separability and reflexivity supply the weakly
convergent subsequence of a minimizing sequence.

The energy may be infinite away from the chosen sublevel. A second theorem
requires only nonemptiness and boundedness of finite sublevels: if no finite
competitor exists, any admissible point minimizes. Infinite energy is retained
throughout, without using a totalized real integral.
-/

@[expose] public section

noncomputable section

open Filter Set TopologicalSpace
open scoped ENNReal Topology

namespace PDE.CalculusOfVariations

/-- A sequentially weakly lower semicontinuous extended energy has a finite minimizer
on a weakly sequentially closed admissible set in a separable reflexive real normed space, provided
one finite sublevel is bounded. Only bounded sequences in the admissible set enter the
lower-semicontinuity hypothesis. -/
theorem exists_isMinOn_of_weak_seq_lowerSemicontinuity_of_bounded_sublevel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SeparableSpace E]
    (hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    (J : E → ℝ≥0∞) {A : Set E} (hA : IsSeqClosed (toWeakSpace ℝ E '' A))
    (hseq : ∀ (u : ℕ → E) (uLimit : E), (∀ j, u j ∈ A) →
      Bornology.IsBounded (range u) →
      Tendsto (fun j ↦ toWeakSpace ℝ E (u j)) atTop
        (𝓝 (toWeakSpace ℝ E uLimit)) → J uLimit ≤ liminf (fun j ↦ J (u j)) atTop)
    {x₀ : E} (hx₀ : x₀ ∈ A) (hfinite : J x₀ ≠ ∞)
    (hbounded : Bornology.IsBounded {x | x ∈ A ∧ J x ≤ J x₀}) :
    ∃ u ∈ A, J u ≠ ∞ ∧ IsMinOn J A u := by
  let K : Set E := {x | x ∈ A ∧ J x ≤ J x₀}
  let S : Set ℝ≥0∞ := J '' K
  have hx₀K : x₀ ∈ K := ⟨hx₀, le_rfl⟩
  have hS : S.Nonempty := ⟨J x₀, ⟨x₀, hx₀K, rfl⟩⟩
  obtain ⟨e, _, he, heS⟩ := exists_seq_tendsto_sInf hS (OrderBot.bddBelow S)
  choose u huK huJ using heS
  have hubounded : Bornology.IsBounded (range u) := hbounded.subset (by
    rintro _ ⟨j, rfl⟩
    exact huK j)
  obtain ⟨uLimit, ns, hns, hweak⟩ :=
    PDE.Analysis.WeakCompactness.exists_subseq_tendsto_weak_of_isBounded
      hreflexive u hubounded
  have hlimitA : uLimit ∈ A := by
    have hmem : toWeakSpace ℝ E uLimit ∈ toWeakSpace ℝ E '' A :=
      hA (fun j ↦ ⟨u (ns j), (huK (ns j)).1, rfl⟩) hweak
    rcases hmem with ⟨v, hv, heq⟩
    exact (toWeakSpace ℝ E).injective heq ▸ hv
  have hsubbounded : Bornology.IsBounded (range (fun j ↦ u (ns j))) :=
    hubounded.subset (by
      rintro _ ⟨j, rfl⟩
      exact mem_range_self (ns j))
  have henergy : Tendsto (fun j ↦ J (u (ns j))) atTop (𝓝 (sInf S)) := by
    simpa only [huJ, Function.comp_def] using he.comp hns.tendsto_atTop
  have hminimal : J uLimit ≤ sInf S := by
    have h := hseq (fun j ↦ u (ns j)) uLimit (fun j ↦ (huK (ns j)).1)
      hsubbounded hweak
    rwa [henergy.liminf_eq] at h
  have hle₀ : J uLimit ≤ J x₀ := hminimal.trans (sInf_le ⟨x₀, hx₀K, rfl⟩)
  refine ⟨uLimit, hlimitA, ne_top_of_le_ne_top hfinite hle₀, ?_⟩
  intro v hv
  by_cases hle : J v ≤ J x₀
  · exact hminimal.trans (sInf_le ⟨v, ⟨hv, hle⟩, rfl⟩)
  · exact hle₀.trans (le_of_not_ge hle)

/-- The direct method for a nonempty admissible class, allowing every admissible
energy to be infinite. In the finite case a bounded finite sublevel supplies
a minimizer; in the all-infinite case every admissible point minimizes. -/
theorem exists_isMinOn_of_weak_seq_lowerSemicontinuity_of_bounded_finite_sublevels
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SeparableSpace E]
    (hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    (J : E → ℝ≥0∞) {A : Set E} (hA : IsSeqClosed (toWeakSpace ℝ E '' A))
    (hseq : ∀ (u : ℕ → E) (uLimit : E), (∀ j, u j ∈ A) →
      Bornology.IsBounded (range u) →
      Tendsto (fun j ↦ toWeakSpace ℝ E (u j)) atTop
        (𝓝 (toWeakSpace ℝ E uLimit)) → J uLimit ≤ liminf (fun j ↦ J (u j)) atTop)
    (hne : A.Nonempty)
    (hbounded : ∀ K : ℝ≥0∞, K ≠ ∞ → Bornology.IsBounded {x | x ∈ A ∧ J x ≤ K}) :
    ∃ u ∈ A, IsMinOn J A u := by
  by_cases hfinite : ∃ x ∈ A, J x ≠ ∞
  · obtain ⟨x, hx, hfin⟩ := hfinite
    obtain ⟨u, hu, _, hmin⟩ :=
      exists_isMinOn_of_weak_seq_lowerSemicontinuity_of_bounded_sublevel
        hreflexive J hA hseq hx hfin (hbounded (J x) hfin)
    exact ⟨u, hu, hmin⟩
  · obtain ⟨u, hu⟩ := hne
    refine ⟨u, hu, fun v hv ↦ ?_⟩
    have hvtop : J v = ∞ := by
      by_contra h
      exact hfinite ⟨v, hv, h⟩
    change J u ≤ J v
    rw [hvtop]
    exact le_top

end PDE.CalculusOfVariations
