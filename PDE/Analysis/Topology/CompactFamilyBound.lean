/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Local bounds for compactly indexed families

A continuous family is uniformly bounded on a compact index set near any fixed
parameter. Only the index set needs compactness. In particular, the parameter
may belong to an infinite-dimensional Banach space.

This is the local domination used when differentiating parameter integrals.
-/

@[expose] public section

open Filter Set
open scoped Topology

/-- Joint continuity gives a uniform bound on a compact index set near a parameter.
There is no local compactness assumption on the parameter space. -/
theorem ContinuousOn.exists_bound_nhds_of_isCompact
    {X T F : Type*} [TopologicalSpace X] [TopologicalSpace T]
    [SeminormedAddCommGroup F] {f : X × T → F} {U : Set X} {K : Set T}
    (hf : ContinuousOn f (U ×ˢ K)) (hU : IsOpen U) (hK : IsCompact K)
    {x : X} (hx : x ∈ U) :
    ∃ V ∈ 𝓝 x, ∃ C : ℝ, V ⊆ U ∧
      ∀ y ∈ V, ∀ t ∈ K, ‖f (y, t)‖ ≤ C := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let g : X × K → F := fun p ↦ f (p.1, p.2)
  have hg : ContinuousOn g (U ×ˢ univ) :=
    hf.comp (continuous_fst.prodMk continuous_snd.subtype_val).continuousOn
      (fun p hp ↦ ⟨hp.1, p.2.property⟩)
  have hslice : Continuous (fun t : K ↦ g (x, t)) :=
    hg.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ ↦ ⟨hx, mem_univ _⟩)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hslice.continuousOn
  let W : Set (X × K) := (U ×ˢ univ) ∩ {p | ‖g p‖ < C + 1}
  have hW : IsOpen W :=
    hg.norm.isOpen_inter_preimage (hU.prod isOpen_univ) isOpen_Iio
  have hsub : ({x} : Set X) ×ˢ (univ : Set K) ⊆ W := by
    rintro ⟨y, t⟩ ⟨hy, _⟩
    have hy' : y = x := hy
    subst y
    exact ⟨⟨hx, mem_univ _⟩, (hC t (mem_univ _)).trans_lt (lt_add_one C)⟩
  obtain ⟨V, Z, hV, _, hxV, hKZ, hVZ⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ hW hsub
  refine ⟨V ∩ U, inter_mem (hV.mem_nhds (hxV (mem_singleton x))) (hU.mem_nhds hx),
    C + 1, inter_subset_right, ?_⟩
  intro y hy t ht
  exact (hVZ (a := (y, (⟨t, ht⟩ : K))) ⟨hy.1, hKZ (mem_univ _)⟩).2.le
