/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Distance from an interior set to the boundary

The infimum of the distances from a set to the boundary controls an interior collar.
We use extended nonnegative distances, so an empty set or an empty boundary imposes
no artificial upper bound on the collar radius.
-/

@[expose] public noncomputable section

namespace Metric

open Set
open scoped ENNReal

variable {E : Type*}

/-- The distance between a set and the frontier of another set, with value infinity
when either set of points in the infimum is empty. -/
def boundaryEDist [PseudoMetricSpace E] (V Ω : Set E) : ℝ≥0∞ :=
  ⨅ x ∈ V, infEDist x (frontier Ω)

/-- Boundary distance is no larger than the distance between any selected pair. -/
theorem boundaryEDist_le_edist [PseudoMetricSpace E] {V Ω : Set E} {x y : E}
    (hx : x ∈ V) (hy : y ∈ frontier Ω) :
    boundaryEDist V Ω ≤ edist x y :=
  (iInf₂_le x hx).trans (infEDist_le_edist_of_mem hy)

/-- A collar narrower than the distance to the boundary stays inside the domain. -/
theorem thickening_subset_of_le_boundaryEDist
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {V Ω : Set E} (hVΩ : V ⊆ Ω)
    {ρ : ℝ} (hρ : ENNReal.ofReal ρ ≤ boundaryEDist V Ω) :
    thickening ρ V ⊆ Ω := by
  intro z hz
  obtain ⟨x, hx, hzx⟩ := mem_thickening_iff.mp hz
  by_contra hzΩ
  have hΩ : Ω ≠ univ := by
    intro heq
    exact hzΩ (heq ▸ mem_univ z)
  obtain ⟨y, hy, hxy⟩ := exists_mem_frontier_infDist_compl_eq_dist (hVΩ hx) hΩ
  have hρxy : ρ ≤ dist x y := by
    apply (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp
    simpa only [← edist_dist] using hρ.trans (boundaryEDist_le_edist hx hy)
  have hnear := infDist_le_dist_of_mem (show z ∈ Ωᶜ from hzΩ) (x := x)
  rw [hxy] at hnear
  exact (hρxy.trans hnear).not_gt (by simpa only [dist_comm] using hzx)

/-- An interior collar gives a lower bound for distance to the boundary of an open set. -/
theorem le_boundaryEDist_of_thickening_subset [PseudoMetricSpace E]
    {V Ω : Set E} (hΩ : IsOpen Ω)
    {ρ : ℝ} (hρΩ : thickening ρ V ⊆ Ω) :
    ENNReal.ofReal ρ ≤ boundaryEDist V Ω := by
  apply le_iInf₂
  intro x hx
  apply le_infEDist.mpr
  intro y hy
  rw [edist_dist]
  apply ENNReal.ofReal_le_ofReal
  by_contra! hnear
  have hyΩ := hρΩ (mem_thickening_iff.mpr
    ⟨x, hx, by simpa only [dist_comm] using hnear⟩)
  exact (disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hΩ)) hy hyΩ

/-- Compact containment in an open set gives a positive lower bound for its boundary
distance, including domains with empty boundary. -/
theorem exists_pos_le_boundaryEDist [PseudoMetricSpace E]
    {V Ω : Set E} (hΩ : IsOpen Ω)
    (hV : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω) :
    ∃ ρ : ℝ, 0 < ρ ∧ ENNReal.ofReal ρ ≤ boundaryEDist V Ω := by
  obtain ⟨ρ, hρ, hρΩ⟩ := hV.exists_thickening_subset_open hΩ hVΩ
  refine ⟨ρ, hρ, le_boundaryEDist_of_thickening_subset hΩ ?_⟩
  simpa only [thickening_closure] using hρΩ

end Metric
