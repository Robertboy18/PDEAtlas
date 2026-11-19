/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Superlevel sets filled across an inner set

A continuous potential with value one on an inner frontier and zero on an outer
frontier gives open filled superlevel sets at intermediate levels. Their frontiers
lie in the original annulus. If the derivative does not vanish at the level,
the frontier is exactly that level. No smoothness of either original frontier is used.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace PDE.Analysis

/-- Fill the inner set and take the strict superlevel set in the surrounding annulus. -/
def filledSuperlevel {X : Type*} (K W : Set X) (u : X → ℝ) (c : ℝ) : Set X :=
  K ∪ {x | x ∈ W \ K ∧ c < u x}

private theorem closure_sdiff_eq_of_subset
    {X : Type*} [TopologicalSpace X] {K W : Set X}
    (hK : IsClosed K) (hW : IsOpen W) (hKW : K ⊆ W) :
    closure (W \ K) = closure W \ interior K := by
  apply Subset.antisymm
  · intro x hx
    refine ⟨closure_mono sdiff_subset hx, ?_⟩
    have hc : x ∈ closure Kᶜ := closure_mono (sdiff_subset_compl W K) hx
    simpa only [closure_compl, mem_compl_iff] using hc
  · intro x hx
    by_cases hxK : x ∈ K
    · have hc : x ∈ closure Kᶜ := by
        simpa only [closure_compl, mem_compl_iff] using hx.2
      simpa only [inter_comm, Set.sdiff_eq] using hW.closure_inter ⟨hc, hKW hxK⟩
    · apply closure_sdiff
      exact ⟨hx.1, by simpa only [hK.closure_eq] using hxK⟩

open Classical in
private theorem continuousOn_innerFill
    {X : Type*} [TopologicalSpace X] {K W : Set X} {u : X → ℝ}
    (hK : IsClosed K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hcont : ContinuousOn u (closure (W \ K)))
    (hinner : ∀ x ∈ frontier K, u x = 1) :
    ContinuousOn (fun x ↦ if x ∈ K then 1 else u x) (closure W) := by
  classical
  refine ContinuousOn.if (p := fun x ↦ x ∈ K) ?_ continuousOn_const ?_
  · exact fun x hx ↦ (hinner x hx.2).symm
  · apply hcont.mono
    intro x hx
    rw [closure_sdiff_eq_of_subset hK hW hKW]
    have hc : x ∈ closure Kᶜ := hx.2
    exact ⟨hx.1, by simpa only [closure_compl, mem_compl_iff] using hc⟩

/-- Filling the inner set gives an open strict superlevel set below its boundary value. -/
theorem isOpen_filledSuperlevel
    {X : Type*} [TopologicalSpace X] {K W : Set X} {u : X → ℝ} {c : ℝ}
    (hK : IsClosed K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hcont : ContinuousOn u (closure (W \ K)))
    (hinner : ∀ x ∈ frontier K, u x = 1) (hc : c < 1) :
    IsOpen (filledSuperlevel K W u c) := by
  classical
  have hfill := continuousOn_innerFill hK hW hKW hcont hinner
  have heq : filledSuperlevel K W u c =
      W ∩ (fun x ↦ if x ∈ K then 1 else u x) ⁻¹' Ioi c := by
    ext x
    by_cases hxK : x ∈ K
    · simp [filledSuperlevel, hxK, hKW hxK, hc]
    · simp [filledSuperlevel, hxK]
  rw [heq]
  exact (hfill.mono subset_closure).isOpen_inter_preimage hW isOpen_Ioi

/-- The frontier of an intermediate filled superlevel set lies in the original
annulus and has exactly the prescribed potential value. -/
theorem frontier_filledSuperlevel_subset
    {X : Type*} [TopologicalSpace X] {K W : Set X} {u : X → ℝ} {c : ℝ}
    (hK : IsClosed K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hcont : ContinuousOn u (closure (W \ K)))
    (hinner : ∀ x ∈ frontier K, u x = 1) (houter : ∀ x ∈ frontier W, u x = 0)
    (hc0 : 0 < c) (hc1 : c < 1) :
    frontier (filledSuperlevel K W u c) ⊆ {x | x ∈ W \ K ∧ u x = c} := by
  classical
  let S := filledSuperlevel K W u c
  have hSopen : IsOpen S := isOpen_filledSuperlevel hK hW hKW hcont hinner hc1
  have hSW : S ⊆ W := by
    rintro x (hx | hx)
    · exact hKW hx
    · exact hx.1.1
  let v : X → ℝ := fun x ↦ if x ∈ K then 1 else u x
  have hv : ContinuousOn v (closure S) :=
    (continuousOn_innerFill hK hW hKW hcont hinner).mono (closure_mono hSW)
  have hbound : ∀ x ∈ closure S, c ≤ v x := by
    apply le_on_closure _ continuousOn_const hv
    rintro x (hx | hx)
    · simpa only [v, ite_eq_left hx] using hc1.le
    · simpa only [v, ite_eq_right hx.1.2] using hx.2.le
  intro x hx
  have hxcl : x ∈ closure S := frontier_subset_closure hx
  have hxnot : x ∉ S := (hSopen.frontier_eq ▸ hx).2
  have hxK : x ∉ K := fun h ↦ hxnot (Or.inl h)
  have hcx : c ≤ u x := by simpa only [v, ite_eq_right hxK] using hbound x hxcl
  have hxW : x ∈ W := by
    by_contra h
    have hxfr : x ∈ frontier W := by
      rw [hW.frontier_eq]
      exact ⟨closure_mono hSW hxcl, h⟩
    rw [houter x hxfr] at hcx
    exact hc0.not_ge hcx
  exact ⟨⟨hxW, hxK⟩, le_antisymm
    (le_of_not_gt (fun h ↦ hxnot (Or.inr ⟨⟨hxW, hxK⟩, h⟩))) hcx⟩

/-- A regular intermediate level is exactly the frontier of its filled superlevel set. -/
theorem frontier_filledSuperlevel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K W : Set E} {u : E → ℝ} {c : ℝ}
    (hK : IsClosed K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hcont : ContinuousOn u (closure (W \ K)))
    (hinner : ∀ x ∈ frontier K, u x = 1) (houter : ∀ x ∈ frontier W, u x = 0)
    (hc0 : 0 < c) (hc1 : c < 1)
    (hregular : ∀ x ∈ W \ K, u x = c → fderiv ℝ u x ≠ 0) :
    frontier (filledSuperlevel K W u c) = {x | x ∈ W \ K ∧ u x = c} := by
  apply Subset.antisymm
  · exact frontier_filledSuperlevel_subset hK hW hKW hcont hinner houter hc0 hc1
  · rintro x ⟨hx, hlevel⟩
    have hxnot : x ∉ filledSuperlevel K W u c := by
      simp only [filledSuperlevel, mem_union, mem_ofPred_eq, hlevel, lt_self_iff_false,
        and_false, or_false]
      exact hx.2
    have hxcl : x ∈ closure (filledSuperlevel K W u c) := by
      by_contra hcl
      have hmax : IsLocalMax u x := by
        filter_upwards [(hW.sdiff hK).mem_nhds hx,
          isClosed_closure.isOpen_compl.mem_nhds hcl] with y hy hycl
        rw [hlevel]
        exact le_of_not_gt fun h ↦ hycl (subset_closure (Or.inr ⟨hy, h⟩))
      exact hregular x hx hlevel hmax.fderiv_eq_zero
    rw [(isOpen_filledSuperlevel hK hW hKW hcont hinner hc1).frontier_eq]
    exact ⟨hxcl, hxnot⟩

end PDE.Analysis
