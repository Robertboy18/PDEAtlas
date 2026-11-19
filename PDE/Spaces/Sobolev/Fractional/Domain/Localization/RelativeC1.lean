/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.RelativeOperator

/-!
# Relative extension under compact C1 localization

A compact C1 cutoff supported in an open patch supplies both multiplier bounds
and a positive artificial-edge gap. These geometric facts construct the bounded
relative extension without imposing any regularity on the physical boundary.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace SobolevSpace.Fractional.Localization

variable {n : ℕ} {s : ℝ} {U B : Set (ℝ^n)} {φ : ℝ^n → ℝ}

/-- A compact C1 cutoff gives a bounded extension from a patch to the physical
domain. The resulting representative is exactly the cutoff product on the
patch and zero on the added part. -/
theorem exists_relativeCutoffCLM_of_contDiff_hasCompactSupport
    (hs0 : 0 < s) (hs1 : s < 1) (hU : IsOpen U) (hB : MeasurableSet B)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    ∃ T : GagliardoSpace n s (U ∩ B) →L[ℝ] GagliardoSpace n s B,
      ∀ u, (GagliardoSpace.toLp n s B (T u) : ℝ^n → ℝ) =ᵐ[volume.restrict B]
        (U ∩ B).indicator (fun x ↦ φ x * GagliardoSpace.toLp n s (U ∩ B) u x) := by
  obtain ⟨L, M, hL, hM⟩ := exists_cutoff_bounds_of_contDiff hφ hc
  obtain ⟨δ, hδ, hsep⟩ :=
    exists_pos_le_dist_sdiff_inter_of_isCompact (B := B) hc hU hφU
  have hgap : ∀ x ∈ U ∩ B, φ x ≠ 0 → ∀ y ∈ B \ (U ∩ B), δ ≤ dist x y :=
    fun x _ hx ↦ hsep x (subset_closure (show x ∈ Function.support φ from hx))
  exact ⟨GagliardoSpace.relativeCutoffCLM hs0 hs1 hδ (hU.measurableSet.inter hB)
    hB inter_subset_right hL hM hgap,
    GagliardoSpace.toLp_relativeCutoffCLM_apply_ae hs0 hs1 hδ
      (hU.measurableSet.inter hB) hB inter_subset_right hL hM hgap⟩

end SobolevSpace.Fractional.Localization
