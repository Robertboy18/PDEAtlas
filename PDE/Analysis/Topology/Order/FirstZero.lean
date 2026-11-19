/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The first zero of a continuous family on a compact set

A continuous family that is initially strictly positive and later nonpositive
somewhere has a first zero. At that time it is nonnegative at every spatial
point, and it is strictly positive throughout the preceding half-open cylinder.
-/

@[expose] public section

namespace PDE.Analysis

open Set

/-- Compactness chooses the earliest nonpositive point; the intermediate value
theorem makes it a zero and rules out negative values at the same time. -/
theorem exists_first_zero_with_pos_past
    {E : Type*} [TopologicalSpace E] [T2Space E]
    {S : Set E} {a b : ℝ} {f : E × ℝ → ℝ}
    (hS : IsCompact S) (hf : ContinuousOn f (S ×ˢ Icc a b))
    (hinitial : ∀ x ∈ S, 0 < f (x, a))
    (htest : ∃ q ∈ S ×ˢ Icc a b, f q ≤ 0) :
    ∃ p ∈ S ×ˢ Ioc a b, f p = 0 ∧
      (∀ q ∈ S ×ˢ Icc a p.2, 0 ≤ f q) ∧
      ∀ q ∈ S ×ˢ Ico a p.2, 0 < f q := by
  let A := (S ×ˢ Icc a b) ∩ {q | f q ≤ 0}
  have hK : IsCompact (S ×ˢ Icc a b) := hS.prod isCompact_Icc
  have hA : IsCompact A :=
    hK.of_isClosed_subset (hK.isClosed.isClosed_le hf continuousOn_const) inter_subset_left
  obtain ⟨p, hp, hmin⟩ := hA.exists_isMinOn htest continuous_snd.continuousOn
  have hroot (q : E × ℝ) (hq : q ∈ A) :
      ∃ r ∈ Icc a q.2, f (q.1, r) = 0 := by
    have hc : ContinuousOn (fun r ↦ f (q.1, r)) (Icc a q.2) :=
      hf.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun r hr ↦ ⟨hq.1.1, hr.1, hr.2.trans hq.1.2.2⟩)
    exact intermediate_value_Icc' hq.1.2.1 hc ⟨hq.2, (hinitial q.1 hq.1.1).le⟩
  have heqzero (q : E × ℝ) (hq : q ∈ A) (hqt : q.2 ≤ p.2) : f q = 0 := by
    obtain ⟨r, hr, hfr⟩ := hroot q hq
    have hrA : (q.1, r) ∈ A := ⟨⟨hq.1.1, hr.1, hr.2.trans hq.1.2.2⟩, hfr.le⟩
    have hpr : p.2 ≤ r := hmin hrA
    have heq : r = q.2 := hr.2.antisymm (hqt.trans hpr)
    simpa only [heq, Prod.eta] using hfr
  have hpzero : f p = 0 := heqzero p hp le_rfl
  have hpa : a < p.2 := by
    apply lt_of_le_of_ne hp.1.2.1
    intro h
    have hpos := hinitial p.1 hp.1.1
    rw [h] at hpos
    exact (ne_of_gt hpos) hpzero
  refine ⟨p, ⟨hp.1.1, hpa, hp.1.2.2⟩, hpzero, ?_, ?_⟩
  · intro q hq
    by_contra hneg
    have hqA : q ∈ A :=
      ⟨⟨hq.1, hq.2.1, hq.2.2.trans hp.1.2.2⟩, (lt_of_not_ge hneg).le⟩
    exact hneg (heqzero q hqA hq.2.2).ge
  · intro q hq
    by_contra hpos
    have hqA : q ∈ A :=
      ⟨⟨hq.1, hq.2.1, hq.2.2.le.trans hp.1.2.2⟩, not_lt.mp hpos⟩
    exact (not_le_of_gt hq.2.2) (hmin hqA)

/-- A first zero has a nonnegative closed past cylinder. -/
theorem exists_first_zero_with_nonneg_past
    {E : Type*} [TopologicalSpace E] [T2Space E]
    {S : Set E} {a b : ℝ} {f : E × ℝ → ℝ}
    (hS : IsCompact S) (hf : ContinuousOn f (S ×ˢ Icc a b))
    (hinitial : ∀ x ∈ S, 0 < f (x, a))
    (htest : ∃ q ∈ S ×ˢ Icc a b, f q ≤ 0) :
    ∃ p ∈ S ×ˢ Ioc a b, f p = 0 ∧
      ∀ q ∈ S ×ˢ Icc a p.2, 0 ≤ f q := by
  obtain ⟨p, hp, hzero, hnonneg, _⟩ :=
    exists_first_zero_with_pos_past hS hf hinitial htest
  exact ⟨p, hp, hzero, hnonneg⟩

end PDE.Analysis
