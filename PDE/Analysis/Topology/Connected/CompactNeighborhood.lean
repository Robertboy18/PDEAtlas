/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Connected relatively compact neighborhoods

A compact connected set inside an open set has an open connected
neighborhood whose closure is compact and remains inside the original set.
Taking a component of a sufficiently small thickening also handles an
ambient open set with several components.
-/

@[expose] public section

namespace PDE.Analysis

open Set Metric

/-- A compact preconnected subset has a relatively compact open preconnected
neighborhood inside any prescribed open neighborhood. The empty set is allowed. -/
theorem exists_preconnected_open_compact_closure
    {E : Type*} [MetricSpace E] [ProperSpace E] [LocallyConnectedSpace E]
    {K U : Set E} (hK : IsCompact K) (hconn : IsPreconnected K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ W : Set E, IsOpen W ∧ IsPreconnected W ∧ K ⊆ W ∧
      IsCompact (closure W) ∧ closure W ⊆ U := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨z, hz⟩
  · exact ⟨∅, isOpen_empty, isPreconnected_empty, subset_rfl, by simp, by simp⟩
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  let W := connectedComponentIn (thickening δ K) z
  have hWO : W ⊆ thickening δ K := connectedComponentIn_subset _ _
  have hclosed : closure W ⊆ cthickening δ K :=
    (closure_mono hWO).trans (closure_thickening_subset_cthickening δ K)
  exact ⟨W, isOpen_thickening.connectedComponentIn, isPreconnected_connectedComponentIn,
    hconn.subset_connectedComponentIn hz (self_subset_thickening hδ K),
    hK.cthickening.of_isClosed_subset isClosed_closure hclosed, hclosed.trans hδU⟩

end PDE.Analysis
