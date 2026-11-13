/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Continuity of suprema under uniform convergence

If a family of real functions `F s` converges to `F t` uniformly on a set `D` as `s → t`, then the
supremum `⨆ p ∈ D, ENNReal.ofReal (F s p)` converges in `ℝ≥0∞`, also when the limit is `∞`. This
is the form in which a weighted sup norm or a Hölder seminorm of a time-dependent function is
continuous in time: no compactness of `D` and no finiteness of the supremum is needed.

## Main results

* `iSup_ofReal_le_add_of_le`: a uniform bound `F s p ≤ F t p + δ` on `D` bounds the suprema.
* `TendstoUniformlyOn.continuousWithinAt_iSup_ofReal`: continuity at one point.
* `continuousOn_iSup_ofReal_of_tendstoUniformlyOn`: continuity on a set.
-/

@[expose] public section

open Filter Set
open scoped ENNReal Topology

variable {ι α : Type*}

namespace PDE

/-- A uniform bound `F p ≤ G p + δ` on `D` gives
`⨆ p ∈ D, ofReal (F p) ≤ ⨆ p ∈ D, ofReal (G p) + ofReal δ`. -/
theorem iSup_ofReal_le_add_of_le {F G : α → ℝ} {D : Set α} {δ : ℝ}
    (h : ∀ p ∈ D, F p ≤ G p + δ) :
    ⨆ p ∈ D, ENNReal.ofReal (F p) ≤ (⨆ p ∈ D, ENNReal.ofReal (G p)) + ENNReal.ofReal δ := by
  refine iSup₂_le fun p hp ↦ ?_
  calc ENNReal.ofReal (F p) ≤ ENNReal.ofReal (G p + δ) := ENNReal.ofReal_le_ofReal (h p hp)
    _ ≤ ENNReal.ofReal (G p) + ENNReal.ofReal δ := ENNReal.ofReal_add_le
    _ ≤ (⨆ p ∈ D, ENNReal.ofReal (G p)) + ENNReal.ofReal δ := by
      gcongr
      exact le_iSup₂ (f := fun p (_ : p ∈ D) ↦ ENNReal.ofReal (G p)) p hp

/-- **Continuity of a supremum under uniform convergence.** If `F s → F t` uniformly on `D` as
`s → t` within `S`, then `s ↦ ⨆ p ∈ D, ofReal (F s p)` is continuous at `t` within `S` in
`ℝ≥0∞`. The supremum may be infinite. -/
theorem _root_.TendstoUniformlyOn.continuousWithinAt_iSup_ofReal [TopologicalSpace ι]
    {F : ι → α → ℝ} {D : Set α} {S : Set ι} {t : ι} (h : TendstoUniformlyOn F (F t) (𝓝[S] t) D) :
    ContinuousWithinAt (fun s ↦ ⨆ p ∈ D, ENNReal.ofReal (F s p)) S t := by
  set G : ι → ℝ≥0∞ := fun s ↦ ⨆ p ∈ D, ENNReal.ofReal (F s p)
  have hb : ∀ δ : ℝ, 0 < δ → ∀ᶠ s in 𝓝[S] t, G s ≤ G t + ENNReal.ofReal δ ∧
      G t ≤ G s + ENNReal.ofReal δ := by
    intro δ hδ
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 h δ hδ] with s hs
    have hs' : ∀ p ∈ D, |F s p - F t p| ≤ δ := fun p hp ↦ by
      have := hs p hp
      rw [Real.dist_eq] at this
      rw [abs_sub_comm]
      exact this.le
    refine ⟨iSup_ofReal_le_add_of_le fun p hp ↦ ?_, iSup_ofReal_le_add_of_le fun p hp ↦ ?_⟩
    · have := (abs_le.1 (hs' p hp)).2
      linarith
    · have := (abs_le.1 (hs' p hp)).1
      linarith
  change Tendsto G (𝓝[S] t) (𝓝 (G t))
  by_cases ht : G t = ⊤
  · have hev : ∀ᶠ s in 𝓝[S] t, G s = G t := by
      filter_upwards [hb 1 one_pos] with s hs
      rw [ht]
      have h2 := hs.2
      rw [ht, top_le_iff, ENNReal.add_eq_top] at h2
      rcases h2 with h2 | h2
      · exact h2
      · exact absurd h2 ENNReal.ofReal_ne_top
    exact tendsto_const_nhds.congr' (hev.mono fun s hs ↦ hs.symm)
  · rw [ENNReal.tendsto_nhds ht]
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ ε := by
      by_cases hε' : ε = ⊤
      · exact ⟨1, one_pos, by simp [hε']⟩
      · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' hε', by rw [ENNReal.ofReal_toReal hε']⟩
    filter_upwards [hb δ hδ] with s hs
    refine ⟨?_, hs.1.trans (by gcongr)⟩
    rw [tsub_le_iff_right]
    exact hs.2.trans (by gcongr)

/-- **Continuity of a supremum under uniform convergence**, on a set: if `F s → F t` uniformly on
`D` as `s → t` within `S` for every `t ∈ S`, then `s ↦ ⨆ p ∈ D, ofReal (F s p)` is continuous on
`S` in `ℝ≥0∞`. -/
theorem continuousOn_iSup_ofReal_of_tendstoUniformlyOn [TopologicalSpace ι] {F : ι → α → ℝ}
    {D : Set α} {S : Set ι} (h : ∀ t ∈ S, TendstoUniformlyOn F (F t) (𝓝[S] t) D) :
    ContinuousOn (fun s ↦ ⨆ p ∈ D, ENNReal.ofReal (F s p)) S :=
  fun t ht ↦ (h t ht).continuousWithinAt_iSup_ofReal

end PDE
