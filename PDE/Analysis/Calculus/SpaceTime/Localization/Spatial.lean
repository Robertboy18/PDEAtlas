/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Spatial localization of fields on a time set

A spatial cutoff whose closed support lies in an open spatial domain extends
a local field by zero without imposing any regularity on the field outside
that domain. The time set may be closed, so the continuity statement applies
at an initial or terminal time as well.
-/

@[expose] public section

namespace PDE.Analysis

open Filter Set
open scoped ContDiff Topology

variable {E F S : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [TopologicalSpace S]

/-- A local field supported in a closed spatial subset of its open domain
is continuous after extension by zero. The statement is relative to an
arbitrary time set. -/
theorem continuousOn_of_spatial_support_subset
    {Ω K : Set E} {I : Set S} {u : E × S → F}
    (hΩ : IsOpen Ω) (hK : IsClosed K) (hKΩ : K ⊆ Ω)
    (hu : ContinuousOn u (Ω ×ˢ I))
    (hzero : ∀ p : E × S, p.2 ∈ I → p.1 ∉ K → u p = 0) :
    ContinuousOn u (univ ×ˢ I) := by
  intro p hp
  by_cases hx : p.1 ∈ K
  · have hnear : Ω ×ˢ I ∈ 𝓝[univ ×ˢ I] p := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds
        ((hΩ.preimage continuous_fst).mem_nhds (hKΩ hx)),
        self_mem_nhdsWithin] with q hq hqI
      exact ⟨hq, hqI.2⟩
    exact (hu p ⟨hKΩ hx, hp.2⟩).mono_of_mem_nhdsWithin hnear
  · apply (continuousWithinAt_const (b := (0 : F))).congr_of_eventuallyEq_of_mem _ hp
    filter_upwards [mem_nhdsWithin_of_mem_nhds
      ((hK.isOpen_compl.preimage continuous_fst).mem_nhds hx),
      self_mem_nhdsWithin] with q hq hqI
    exact hzero q hqI.2 hq

variable [NormedSpace ℝ F]

/-- Multiplication by a spatial cutoff preserves joint continuity and extends
it to every spatial point, including at the boundary of an arbitrary time set. -/
theorem continuousOn_spatial_cutoff_smul
    {Ω : Set E} {I : Set S} {u : E × S → F} {χ : E → ℝ}
    (hΩ : IsOpen Ω) (hχ : Continuous χ) (hχΩ : tsupport χ ⊆ Ω)
    (hu : ContinuousOn u (Ω ×ˢ I)) :
    ContinuousOn (fun p : E × S ↦ χ p.1 • u p) (univ ×ˢ I) := by
  apply continuousOn_of_spatial_support_subset hΩ (isClosed_tsupport χ) hχΩ
    ((hχ.comp continuous_fst).continuousOn.smul hu)
  intro p _ hp
  change χ p.1 • u p = 0
  simp only [image_eq_zero_of_notMem_tsupport hp, zero_smul]

variable [NormedSpace ℝ E]

/-- A smooth spatial cutoff localizes any finite or infinite differentiability
order. Outside its closed support the product is identically zero near the point;
no differentiability of the unlocalized function is needed there. -/
theorem contDiff_spatial_cutoff_smul
    {m : ℕ∞ω} {Ω : Set E} {u : E → F} {χ : E → ℝ}
    (hΩ : IsOpen Ω) (hχ : ContDiff ℝ m χ) (hχΩ : tsupport χ ⊆ Ω)
    (hu : ContDiffOn ℝ m u Ω) :
    ContDiff ℝ m (fun x ↦ χ x • u x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.smul (hu.contDiffAt (hΩ.mem_nhds (hχΩ hx)))
  · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
    simp only [image_eq_zero_of_notMem_tsupport hy, zero_smul]

end PDE.Analysis
