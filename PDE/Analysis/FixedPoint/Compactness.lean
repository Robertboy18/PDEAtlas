/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Sequences

/-!
# Compactness of approximate fixed points

Suppose a sequence in a closed set has vanishing fixed-point error and its images have compact
closure. A subsequence of the images converges; the vanishing error forces the same subsequence
of the original points to converge to the same limit. Continuity then makes that limit a fixed
point.

The argument is metric and requires neither a vector space nor completeness. For a map whose
image has compact closure, arbitrarily accurate approximate fixed points therefore give an
exact fixed point.
-/

@[expose] public section

open Filter Function Set
open scoped Topology

namespace PDE.FixedPoint

variable {X : Type*} [MetricSpace X] {s : Set X} {f : X → X}

/-- A sequence of approximate fixed points has an exact fixed point as a subsequential limit
when its images have compact closure. Closedness keeps the limit in the domain, where
continuity identifies it with its image. -/
theorem exists_isFixedPt_of_tendsto_dist (hs : IsClosed s) (hf : ContinuousOn f s)
    {u : ℕ → X} (hu : ∀ n, u n ∈ s)
    (hcompact : IsCompact (closure (range (f ∘ u))))
    (herror : Tendsto (fun n ↦ dist (f (u n)) (u n)) atTop (𝓝 0)) :
    ∃ x ∈ s, IsFixedPt f x := by
  obtain ⟨x, _, φ, hφ, hfx⟩ := hcompact.tendsto_subseq
    (fun n ↦ subset_closure (mem_range_self n))
  have hux : Tendsto (u ∘ φ) atTop (𝓝 x) :=
    hfx.congr_dist (herror.comp hφ.tendsto_atTop)
  have hx : x ∈ s := hs.mem_of_tendsto hux (Eventually.of_forall fun n ↦ hu (φ n))
  have hwithin : Tendsto (u ∘ φ) atTop (𝓝[s] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨hux, Eventually.of_forall fun n ↦ hu (φ n)⟩
  exact ⟨x, hx, tendsto_nhds_unique ((hf x hx).tendsto.comp hwithin) hfx⟩

/-- For a continuous map on a closed set with relatively compact image, approximate fixed points
at every positive error tolerance yield an exact fixed point in that set. This is the compactness
step of a fixed-point argument; the approximate fixed points are hypotheses.
-/
theorem exists_isFixedPt_of_forall_dist_lt (hs : IsClosed s) (hf : ContinuousOn f s)
    (hcompact : IsCompact (closure (f '' s)))
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ x ∈ s, dist (f x) x < ε) :
    ∃ x ∈ s, IsFixedPt f x := by
  choose u hu herror using fun n : ℕ ↦
    happrox (1 / ((n : ℝ) + 1)) (one_div_pos.mpr (Nat.cast_add_one_pos n))
  apply exists_isFixedPt_of_tendsto_dist hs hf hu
  · apply hcompact.of_isClosed_subset isClosed_closure
    apply closure_mono
    rintro _ ⟨n, rfl⟩
    exact mem_image_of_mem f (hu n)
  · exact squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ (herror n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat

end PDE.FixedPoint
