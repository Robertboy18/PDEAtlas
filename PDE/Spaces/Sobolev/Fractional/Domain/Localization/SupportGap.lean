/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Separation from an artificial patch edge

A compact subset of an open patch has a positive distance from its complement.
Intersecting the patch with a physical domain only removes pairs from this
estimate. No separation from the physical boundary is required.
-/

@[expose] public section

open Set

namespace SobolevSpace.Fractional.Localization

variable {X : Type*} [PseudoMetricSpace X] {K U B : Set X}

/-- A compact subset of an open patch is uniformly separated from its complement.
The statement also covers the empty compact set. -/
theorem exists_pos_le_dist_of_isCompact_subset_open
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∉ U, δ ≤ dist x y := by
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open hU hKU
  refine ⟨δ, hδ, fun x hx y hy ↦ ?_⟩
  by_contra h
  apply hy
  exact hthick (Metric.mem_thickening_iff.mpr
    ⟨x, hx, by simpa only [dist_comm] using lt_of_not_ge h⟩)

/-- The new portion of a relative extension lies outside the patch, even when
the physical domain meets the support. -/
theorem exists_pos_le_dist_sdiff_inter_of_isCompact
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∈ B \ (U ∩ B), δ ≤ dist x y := by
  obtain ⟨δ, hδ, hgap⟩ := exists_pos_le_dist_of_isCompact_subset_open hK hU hKU
  exact ⟨δ, hδ, fun x hx y hy ↦ hgap x hx y (fun hyU ↦ hy.2 ⟨hyU, hy.1⟩)⟩

/-- A compactly supported cutoff supplies the support-gap hypothesis for every
function it multiplies. The radius is independent of that function. -/
theorem exists_pos_le_dist_mul_sdiff_inter
    {φ : X → ℝ} (hc : HasCompactSupport φ) (hU : IsOpen U)
    (hφU : tsupport φ ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : X → ℝ, ∀ x ∈ U ∩ B,
      φ x * u x ≠ 0 → ∀ y ∈ B \ (U ∩ B), δ ≤ dist x y := by
  obtain ⟨δ, hδ, hgap⟩ :=
    exists_pos_le_dist_sdiff_inter_of_isCompact (B := B) hc hU hφU
  refine ⟨δ, hδ, fun u x _ hx y hy ↦ hgap x ?_ y hy⟩
  exact subset_closure (show x ∈ Function.support φ from (mul_ne_zero_iff.mp hx).1)

end SobolevSpace.Fractional.Localization
