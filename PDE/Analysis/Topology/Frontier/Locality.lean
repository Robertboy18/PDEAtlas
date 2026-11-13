/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.NhdsWithin

/-!
# Locality of the frontier

Membership in the frontier depends only on the germ of a set. Thus an open
patch on which two sets agree also identifies their frontiers there.
-/

@[expose] public section

open Set
open scoped Topology

/-- Sets agreeing near a point have the same frontier membership there. -/
theorem Filter.EventuallyEqSet.mem_frontier_iff
    {X : Type*} [TopologicalSpace X] {s t : Set X} {x : X} (h : s =ᶠ[𝓝 x] t) :
    x ∈ frontier s ↔ x ∈ frontier t := by
  change (x ∈ closure s ∧ x ∉ interior s) ↔ (x ∈ closure t ∧ x ∉ interior t)
  rw [closure_eq_compl_interior_compl, closure_eq_compl_interior_compl]
  exact and_congr (not_congr h.compl.mem_interior_iff) (not_congr h.mem_interior_iff)

/-- Equality of sets on an open patch identifies their frontiers on that patch. -/
theorem IsOpen.mem_frontier_iff_of_local_eq
    {X : Type*} [TopologicalSpace X] {s t U : Set X} (hU : IsOpen U)
    (h : ∀ y ∈ U, y ∈ s ↔ y ∈ t) {x : X} (hx : x ∈ U) :
    x ∈ frontier s ↔ x ∈ frontier t := by
  apply Filter.EventuallyEqSet.mem_frontier_iff
  filter_upwards [hU.mem_nhds hx] with y hy
  exact propext (h y hy)
