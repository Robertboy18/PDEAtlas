/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# First contact on a compact convex region

A finite collection of initially negative functions cannot reach zero when,
at every possible first contact, one of the inward directions has a strictly
positive derivative. The clock is a continuous linear functional. In transport
applications the region is a backward cone and the inward direction is the
negative characteristic direction, including at its lateral boundary.
-/

@[expose] public noncomputable section

open Set
open scoped Convex

namespace PDE.Analysis.Transport

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite ι]

/-- Strict inequalities persist on a compact convex region if every contact
admits a past-pointing tangent direction with a positive directional derivative.
The derivative condition is needed only when all the inequalities still hold. -/
theorem strict_invariant_of_first_contact
    {K : Set E} {clock : E →L[ℝ] ℝ} {f : ι → E → ℝ}
    (hK : IsCompact K) (hconv : Convex ℝ K)
    (hclock : ∀ p ∈ K, 0 ≤ clock p)
    (hbase : ∃ q ∈ K, clock q = 0)
    (hcont : ∀ i, ContinuousOn (f i) K)
    (hinit : ∀ p ∈ K, clock p = 0 → ∀ i, f i p < 0)
    (hinward : ∀ p ∈ K, 0 < clock p → (∀ j, f j p ≤ 0) →
      ∀ i, f i p = 0 →
        ∃ L : E →L[ℝ] ℝ, HasFDerivWithinAt (f i) L K p ∧
          ∃ v ∈ posTangentConeAt (K ∩ {q | clock q ≤ clock p}) p, 0 < L v) :
    ∀ p ∈ K, ∀ i, f i p < 0 := by
  classical
  let bad : Set E := ⋃ i, {p ∈ K | 0 ≤ f i p}
  have hbad : IsCompact bad := by
    apply isCompact_iUnion
    intro i
    exact hK.of_isClosed_subset
      (hK.isClosed.isClosed_le continuousOn_const (hcont i)) (fun _ hp ↦ hp.1)
  have hbadK : bad ⊆ K := by
    intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact hi.1
  by_contra h
  push Not at h
  obtain ⟨p, hp, i, hi⟩ := h
  have hne : bad.Nonempty := ⟨p, mem_iUnion.mpr ⟨i, hp, hi⟩⟩
  obtain ⟨p, hpbad, hmin⟩ :=
    hbad.exists_isMinOn hne clock.continuous.continuousOn
  have hpK := hbadK hpbad
  obtain ⟨i, _, hi⟩ := mem_iUnion.mp hpbad
  have htp : 0 < clock p := by
    refine lt_of_le_of_ne (hclock p hpK) ?_
    intro heq
    exact (not_lt_of_ge hi) (hinit p hpK heq.symm i)
  have hearlier : ∀ q ∈ K, clock q < clock p → ∀ j, f j q < 0 := by
    intro q hq ht j
    by_contra hj
    have hqb : q ∈ bad := mem_iUnion.mpr ⟨j, hq, le_of_not_gt hj⟩
    exact (not_le_of_gt ht) (hmin hqb)
  obtain ⟨q₀, hq₀, ht₀⟩ := hbase
  have hpast : ∀ q ∈ K, clock q ≤ clock p → ∀ j, f j q ≤ 0 := by
    intro q hq hqt j
    have hseg : segment ℝ q₀ q ⊆ K := hconv.segment_subset hq₀ hq
    have hclosure : closure (openSegment ℝ q₀ q) ⊆ K := by
      rw [closure_openSegment]
      exact hseg
    apply le_on_closure (f := f j) (g := fun _ ↦ 0)
      (s := openSegment ℝ q₀ q) _ ((hcont j).mono hclosure) continuousOn_const
      (segment_subset_closure_openSegment (right_mem_segment ℝ q₀ q))
    rintro y ⟨a, b, ha, hb, hab, rfl⟩
    have hyK := hseg ⟨a, b, ha.le, hb.le, hab, rfl⟩
    apply (hearlier _ hyK _ j).le
    simp only [map_add, map_smul, ht₀, smul_eq_mul, mul_zero, zero_add]
    have hb1 : b < 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hqt hb.le]
  have hall := hpast p hpK le_rfl
  obtain ⟨L, hL, v, hv, hpos⟩ := hinward p hpK htp hall i (le_antisymm (hall i) hi)
  have hmax : IsMaxOn (f i) (K ∩ {q | clock q ≤ clock p}) p := by
    intro q hq
    exact (hpast q hq.1 hq.2 i).trans hi
  have hnonpos := hmax.isLocalMaxOn.hasFDerivWithinAt_nonpos
    (hL.mono inter_subset_left) hv
  exact (not_le_of_gt hpos) hnonpos

end PDE.Analysis.Transport
