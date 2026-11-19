/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.WeakCompactness
import Mathlib.Topology.MetricSpace.PiNat

/-!
# Sequential compactness in separable reflexive spaces

Norming functionals at a countable dense set separate the points of a separable real
normed space. Their evaluations are weakly continuous, so they metrize every weakly compact
subset, which is therefore weakly sequentially compact. Combined with weak compactness of
bounded sets in reflexive spaces, every bounded sequence in a separable reflexive space has
a weakly convergent subsequence. Separability refers to the norm topology.
-/

@[expose] public section

noncomputable section

open Filter Set TopologicalSpace
open scoped Topology

namespace PDE.Analysis.WeakCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SeparableSpace E]

/-- Norming functionals on a countable dense set distinguish every pair of vectors. -/
private theorem exists_countable_separating_evaluations :
    ∃ ell : ℕ → StrongDual ℝ E, ∀ ⦃x y : E⦄, x ≠ y → ∃ j, ell j x ≠ ell j y := by
  choose ell hell_norm hell_value using fun j ↦ exists_dual_vector'' ℝ (denseSeq E j)
  refine ⟨ell, ?_⟩
  intro x y hxy
  by_contra h
  push Not at h
  let z := x - y
  have hz : 0 < ‖z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  obtain ⟨j, hj⟩ := (denseRange_denseSeq E).exists_dist_lt z (half_pos hz)
  have hz_eval : ell j z = 0 := by
    rw [show z = x - y from rfl, map_sub, h j, sub_self]
  have hdense : ‖denseSeq E j‖ ≤ ‖z - denseSeq E j‖ := by
    calc
      ‖denseSeq E j‖ = ell j (denseSeq E j - z) := by
        rw [map_sub, hz_eval, sub_zero, hell_value j, RCLike.ofReal_real_eq_id]
        rfl
      _ ≤ ‖ell j (denseSeq E j - z)‖ := le_abs_self _
      _ ≤ ‖denseSeq E j - z‖ := by
        simpa only [one_mul] using
          (ell j).le_of_opNorm_le (hell_norm j) (denseSeq E j - z)
      _ = ‖z - denseSeq E j‖ := norm_sub_rev _ _
  have htriangle : ‖z‖ ≤ ‖z - denseSeq E j‖ + ‖denseSeq E j‖ := by
    calc
      ‖z‖ = ‖(z - denseSeq E j) + denseSeq E j‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - denseSeq E j‖ + ‖denseSeq E j‖ := norm_add_le _ _
  rw [dist_eq_norm] at hj
  linarith

/-- Weakly compact subsets of a norm-separable real normed space are sequentially
compact. Countably many norming evaluations supply metrizability on the compact set. -/
theorem isSeqCompact_of_isCompact {K : Set (WeakSpace ℝ E)} (hK : IsCompact K) :
    IsSeqCompact K := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨ell, hsep⟩ := exists_countable_separating_evaluations (E := E)
  let f (j : ℕ) (w : K) : ℝ := ell j ((toWeakSpace ℝ E).symm w.1)
  have hf (j : ℕ) : Continuous (f j) :=
    (WeakBilin.eval_continuous (topDualPairing ℝ E).flip (ell j)).comp
      continuous_subtype_val
  have hseparates {x y : K} (hxy : x ≠ y) : ∃ j, f j x ≠ f j y :=
    hsep ((toWeakSpace ℝ E).symm.injective.ne (Subtype.val_injective.ne hxy))
  have : MetrizableSpace K :=
    Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace.of_countable_separating f hf
      (fun _ _ hxy ↦ hseparates hxy)
  have hval : SeqContinuous (Subtype.val : K → WeakSpace ℝ E) :=
    continuous_iff_seqContinuous.mp continuous_subtype_val
  simpa using IsSeqCompact.range hval

/-- Every bounded sequence in a separable reflexive real normed space has a weakly
convergent subsequence. Reflexivity is the surjectivity of the canonical bidual map. -/
theorem exists_subseq_tendsto_weak_of_isBounded
    (hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    (u : ℕ → E) (hu : Bornology.IsBounded (range u)) :
    ∃ (uLimit : E) (ns : ℕ → ℕ), StrictMono ns ∧
      Tendsto (fun j ↦ toWeakSpace ℝ E (u (ns j))) atTop
        (𝓝 (toWeakSpace ℝ E uLimit)) := by
  let S : Set (WeakSpace ℝ E) := range (fun j ↦ toWeakSpace ℝ E (u j))
  have hpre : (toWeakSpace ℝ E) ⁻¹' S = range u := by
    ext x
    simp [S]
  have hbounded : Bornology.IsBounded ((toWeakSpace ℝ E) ⁻¹' S) := by
    rwa [hpre]
  have hcompact := isCompact_closure_of_isBounded_of_reflexive hreflexive S hbounded
  obtain ⟨w, _, ns, hns, hw⟩ := isSeqCompact_of_isCompact hcompact
    (x := fun j ↦ toWeakSpace ℝ E (u j))
    (fun j ↦ subset_closure (mem_range_self j))
  refine ⟨(toWeakSpace ℝ E).symm w, ns, hns, ?_⟩
  simpa only [Function.comp_def, LinearEquiv.apply_symm_apply] using hw

end PDE.Analysis.WeakCompactness
