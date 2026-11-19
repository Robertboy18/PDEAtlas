/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Relatively compact images of bounded sets

For arbitrary maps between metric spaces, compact closure of every bounded image is
equivalent to the bounded-sequence subsequence criterion. No linearity or continuity is
needed. The reverse implication approximates a sequence in the image closure by
image points, so its conclusion is compactness in the target space itself.
-/

@[expose] public section

open Set Filter Metric Bornology
open scoped Topology

namespace PDE.Analysis

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y}

/-- The all-bounded-sets compactness condition for a nonlinear map is equivalent to
convergence of a subsequence of the image of every bounded sequence. -/
theorem isCompact_closure_image_bounded_iff_subsequence :
    (∀ s : Set X, IsBounded s → IsCompact (closure (f '' s))) ↔
      ∀ u : ℕ → X, IsBounded (range u) →
        ∃ (y : Y) (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (f ∘ u ∘ φ) atTop (𝓝 y) := by
  constructor
  · intro h u hu
    obtain ⟨y, _, φ, hφ, hy⟩ := (h (range u) hu).tendsto_subseq
      (fun n ↦ subset_closure (mem_image_of_mem f (mem_range_self n)))
    exact ⟨y, φ, hφ, hy⟩
  · intro h s hs
    apply IsSeqCompact.isCompact
    intro v hv
    have happrox (n : ℕ) :
        ∃ x ∈ s, dist (v n) (f x) < 1 / ((n : ℝ) + 1) := by
      obtain ⟨y, hy, hnear⟩ := mem_closure_iff.mp (hv n)
        (1 / ((n : ℝ) + 1)) (one_div_pos.mpr (Nat.cast_add_one_pos n))
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨x, hx, hnear⟩
    choose u hu hnear using happrox
    obtain ⟨y, φ, hφ, hy⟩ := h u (hs.subset (range_subset_iff.mpr hu))
    have herr : Tendsto (fun n ↦ dist (f (u n)) (v n)) atTop (𝓝 0) := by
      apply squeeze_zero (fun _ ↦ dist_nonneg)
        (fun n ↦ (by simpa only [dist_comm] using (hnear n).le))
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have hlimit : Tendsto (v ∘ φ) atTop (𝓝 y) := hy.congr_dist (herr.comp hφ.tendsto_atTop)
    have hmem : y ∈ closure (f '' s) :=
      isClosed_closure.mem_of_tendsto hy
        (Eventually.of_forall fun n ↦ subset_closure (mem_image_of_mem f (hu (φ n))))
    exact ⟨y, hmem, φ, hφ, hlimit⟩

end PDE.Analysis
