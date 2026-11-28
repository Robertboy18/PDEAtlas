/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Convex.Join
public import Mathlib.Analysis.Convex.Star
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The join of two sets: compactness, and star-shaped sets that contain it

The join `convexJoin ℝ s t` is the union of the segments from a point of `s` to a point of `t`.
It is compact when `s` and `t` are, and it lies in every set that contains `s` and is
star-shaped about each point of `t`. Together the two facts locate the support of the output of
an integral operator whose kernel lives on segments, such as Bogovskii's operator on a domain
that is star-shaped with respect to a ball.

## Main results

* `IsCompact.convexJoin`: in a real topological vector space, the join of two compact sets is
  compact.
* `convexJoin_subset_of_starConvex`: a set that is star-shaped about every point of `t` and
  contains `s` contains `convexJoin ℝ s t`. It is the star-shaped form of Mathlib's
  `convexJoin_subset`, which asks the containing set to be convex.

## How it works

The join is the image of `s × t × [0, 1]` under the continuous map
`(x, y, θ) ↦ (1 - θ) x + θ y`, so it is compact when `s` and `t` are. A segment from `a ∈ s` to
`b ∈ t` lies in a set that is star-shaped about `b` and contains `a`.
-/

@[expose] public section

open Set

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {s t D : Set E}

/-- A set that is star-shaped about every point of `t` and contains `s` contains every segment
from `s` to `t`. -/
theorem convexJoin_subset_of_starConvex (hD : ∀ w ∈ t, StarConvex ℝ w D) (hs : s ⊆ D) :
    convexJoin ℝ s t ⊆ D := by
  intro x hx
  obtain ⟨a, ha, b, hb, hx⟩ := mem_convexJoin.1 hx
  rw [segment_symm] at hx
  exact (hD b hb).segment_subset (hs ha) hx

end Module

section Topology

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] {s t : Set E}

/-- The join of two compact sets is compact: it is a continuous image of `s × t × [0, 1]`. -/
theorem IsCompact.convexJoin (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (_root_.convexJoin ℝ s t) := by
  have himage : _root_.convexJoin ℝ s t =
      (fun p : (E × E) × ℝ ↦ (1 - p.2) • p.1.1 + p.2 • p.1.2) '' ((s ×ˢ t) ×ˢ Icc (0 : ℝ) 1) := by
    ext x
    simp only [mem_convexJoin, segment_eq_image, mem_image, mem_prod, mem_Icc, Prod.exists]
    constructor
    · rintro ⟨a, ha, b, hb, θ, hθ, rfl⟩
      exact ⟨a, b, θ, ⟨⟨ha, hb⟩, hθ⟩, rfl⟩
    · rintro ⟨a, b, θ, ⟨⟨ha, hb⟩, hθ⟩, rfl⟩
      exact ⟨a, ha, b, hb, θ, hθ, rfl⟩
  rw [himage]
  exact ((hs.prod ht).prod isCompact_Icc).image (by fun_prop)

end Topology
