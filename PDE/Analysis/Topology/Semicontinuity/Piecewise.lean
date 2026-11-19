/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Semicontinuity of piecewise functions

An upper semicontinuous function on the interior of a set extends upper
semicontinuously to the set by assigning the values of a dominating upper
semicontinuous barrier on the remaining points. Reversing the order gives
the lower semicontinuous version. A local maximum can also be pasted into
an open patch when the original function dominates it near the patch boundary.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace PDE

/-- Extend an upper semicontinuous function from the interior using a
dominating upper semicontinuous barrier. -/
theorem upperSemicontinuousOn_piecewise_interior
    {X R : Type*} [TopologicalSpace X] [Preorder R]
    {K : Set X} {u b : X → R} [DecidablePred (· ∈ interior K)]
    (hu : UpperSemicontinuousOn u (interior K))
    (hb : UpperSemicontinuousOn b K)
    (hub : ∀ x ∈ interior K, u x ≤ b x) :
    UpperSemicontinuousOn ((interior K).piecewise u b) K := by
  intro x hx c hc
  by_cases hxU : x ∈ interior K
  · rw [piecewise_eq_of_mem _ _ _ hxU] at hc
    have hU : interior K ∈ 𝓝 x := isOpen_interior.mem_nhds hxU
    have hK : K ∈ 𝓝 x := mem_of_superset hU interior_subset
    have hevent : ∀ᶠ y in 𝓝[K] x, u y < c := by
      rw [nhdsWithin_eq_nhds.mpr hK, ← nhdsWithin_eq_nhds.mpr hU]
      exact hu x hxU c hc
    filter_upwards [hevent, mem_nhdsWithin_of_mem_nhds hU] with y hy hyU
    rwa [piecewise_eq_of_mem _ _ _ hyU]
  · rw [piecewise_eq_of_notMem _ _ _ hxU] at hc
    filter_upwards [hb x hx c hc] with y hy
    by_cases hyU : y ∈ interior K
    · rw [piecewise_eq_of_mem _ _ _ hyU]
      exact (hub y hyU).trans_lt hy
    · rwa [piecewise_eq_of_notMem _ _ _ hyU]

/-- Extend a lower semicontinuous function from the interior using a
lower semicontinuous lower barrier. -/
theorem lowerSemicontinuousOn_piecewise_interior
    {X R : Type*} [TopologicalSpace X] [Preorder R]
    {K : Set X} {u l : X → R} [DecidablePred (· ∈ interior K)]
    (hu : LowerSemicontinuousOn u (interior K))
    (hl : LowerSemicontinuousOn l K)
    (hlu : ∀ x ∈ interior K, l x ≤ u x) :
    LowerSemicontinuousOn ((interior K).piecewise u l) K :=
  upperSemicontinuousOn_piecewise_interior (R := Rᵒᵈ) hu hl hlu

/-- Local dominance near the boundary preserves upper semicontinuity
when pasting a maximum on an open patch. -/
theorem upperSemicontinuousOn_piecewise_max
    {X : Type*} [TopologicalSpace X]
    {U V : Set X} {u ψ : X → ℝ} [DecidablePred (· ∈ V)]
    (hu : UpperSemicontinuousOn u U) (hV : IsOpen V)
    (hψ : UpperSemicontinuousOn ψ (U ∩ V))
    (hglue : ∀ x ∈ U, x ∉ V →
      ∀ᶠ y in 𝓝[U] x, y ∈ V → ψ y ≤ u y) :
    UpperSemicontinuousOn (V.piecewise (fun y ↦ max (u y) (ψ y)) u) U := by
  intro x hx
  by_cases hxV : x ∈ V
  · have hψx : UpperSemicontinuousWithinAt ψ U x := by
      have h := hψ x ⟨hx, hxV⟩
      change ∀ b, ψ x < b → ∀ᶠ y in 𝓝[U ∩ V] x, ψ y < b at h
      rw [nhdsWithin_inter_of_mem'
        (mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hxV))] at h
      exact h
    apply UpperSemicontinuousWithinAt.congr_of_eventuallyEq
      (UpperSemicontinuousWithinAt.sup (hu x hx) hψx) hx
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hxV)] with y hy
    exact (piecewise_eq_of_mem V (fun y ↦ max (u y) (ψ y)) u hy).symm
  · apply UpperSemicontinuousWithinAt.congr_of_eventuallyEq (hu x hx) hx
    filter_upwards [hglue x hx hxV] with y hy
    by_cases hyV : y ∈ V
    · rw [piecewise_eq_of_mem V _ _ hyV, max_eq_left (hy hyV)]
    · rw [piecewise_eq_of_notMem V _ _ hyV]

end PDE
