/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.TietzeExtension

/-!
# Continuous extensions of uniformly continuous scalar data

Uniform continuity on a subset gives a continuous extension to its closure by completion.
Tietze's theorem then gives a continuous ambient representative. On a bounded subset of a
proper metric space, this also proves boundedness without assuming values on the boundary.
-/

@[expose] public section

open Set

/-- Uniformly continuous real data on a subset admit an ambient continuous representative.
The extension to the closure is obtained by completeness before applying Tietze's theorem. -/
theorem UniformContinuousOn.exists_continuous_eqOn
    {E : Type*} [MetricSpace E] {s : Set E} {f : E → ℝ}
    (hf : UniformContinuousOn f s) :
    ∃ g : E → ℝ, Continuous g ∧ EqOn g f s := by
  let e : s → closure s := inclusion subset_closure
  have he : IsUniformInducing e :=
    (isUniformInducing_val (closure s)).of_comp_iff.mp (isUniformInducing_val s)
  have hd : DenseRange e := (denseRange_inclusion_iff subset_closure).mpr Subset.rfl
  let g : closure s → ℝ := (he.isDenseInducing hd).extend (s.domRestrict f)
  have hg : Continuous g :=
    (uniformContinuous_uniformly_extend he hd hf.restrict).continuous
  obtain ⟨G, hG⟩ := ContinuousMap.exists_extension'
    isClosed_closure.isClosedEmbedding_subtypeVal ⟨g, hg⟩
  refine ⟨G, G.continuous, fun x hx ↦ ?_⟩
  calc
    G x = g (e ⟨x, hx⟩) := congrFun hG (e ⟨x, hx⟩)
    _ = f x := (he.isDenseInducing hd).extend_eq hf.restrict.continuous ⟨x, hx⟩

/-- Uniformly continuous scalar data on a bounded subset of a proper metric space
are bounded, even when no boundary values have been specified. -/
theorem UniformContinuousOn.exists_pos_bound
    {E : Type*} [MetricSpace E] [ProperSpace E] {s : Set E} {f : E → ℝ}
    (hf : UniformContinuousOn f s) (hs : Bornology.IsBounded s) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ s, ‖f x‖ ≤ C := by
  obtain ⟨g, hg, heq⟩ := hf.exists_continuous_eqOn
  obtain ⟨C, hC, hbound⟩ :=
    (hs.isCompact_closure.image hg).isBounded.exists_pos_norm_le
  exact ⟨C, hC, fun x hx ↦ by
    rw [← heq hx]
    exact hbound _ (mem_image_of_mem g (subset_closure hx))⟩
