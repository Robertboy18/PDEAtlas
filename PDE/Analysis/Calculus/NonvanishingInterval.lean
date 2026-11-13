/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# The interval of nonvanishing of a continuous function

Intervals of times `(a, T) = {t | a < t ∧ t < T}` with `a < 0` real and `T ∈ (0, ∞]` extended
real are open and order connected. For a function `w` continuous on such an interval with
`w 0 ≠ 0` there is a smaller interval `(-δ, t_end)` around `0` on which `w` does not vanish,
maximal to the right.

## Main definitions

* `timeInterval`: the interval of times `(a, T)` with a real left end and an extended real right
  end.

## Main results

* `isOpen_timeInterval`: `(a, T)` is open.
* `ordConnected_timeInterval`: `(a, T)` is order connected.
* `exists_nonvanishing_timeInterval`: `w` does not vanish on some `(-δ, t_end)`, and
  `w(t_end) = 0` when `t_end < T`.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology ENNReal

namespace PDE.Analysis

/-- The interval of times `(a, T)` with a real left end and an extended real right end. -/
def timeInterval (a : ℝ) (T : ℝ≥0∞) : Set ℝ :=
  {t | a < t ∧ ENNReal.ofReal t < T}

/-- The interval `(a, T)` is open. -/
theorem isOpen_timeInterval (a : ℝ) (T : ℝ≥0∞) : IsOpen (timeInterval a T) :=
  (isOpen_lt continuous_const continuous_id).inter
    (isOpen_lt ENNReal.continuous_ofReal continuous_const)

/-- The interval `(a, T)` is order connected. -/
theorem ordConnected_timeInterval (a : ℝ) (T : ℝ≥0∞) : (timeInterval a T).OrdConnected :=
  ⟨fun _ hx _ hy _ ht ↦ ⟨hx.1.trans_le ht.1, (ENNReal.ofReal_le_ofReal ht.2).trans_lt hy.2⟩⟩

/-- The time `0` lies in `(a, T)` when `a < 0 < T`. -/
theorem zero_mem_timeInterval {a : ℝ} {T : ℝ≥0∞} (ha : a < 0) (hT : 0 < T) :
    (0 : ℝ) ∈ timeInterval a T :=
  ⟨ha, by simpa using hT⟩

/-- `(a, T) ⊆ (a', T')` when `a' ≤ a` and `T ≤ T'`. -/
theorem timeInterval_mono {a a' : ℝ} {T T' : ℝ≥0∞} (ha : a' ≤ a) (hT : T ≤ T') :
    timeInterval a T ⊆ timeInterval a' T' :=
  fun _ ht ↦ ⟨ha.trans_lt ht.1, ht.2.trans_le hT⟩

/-- At nonnegative times membership in `(a, T)`, `a < 0`, is `t < T`. -/
theorem mem_timeInterval_iff {a : ℝ} {T : ℝ≥0∞} (ha : a < 0) {t : ℝ} (ht : 0 ≤ t) :
    t ∈ timeInterval a T ↔ ENNReal.ofReal t < T :=
  ⟨fun h ↦ h.2, fun h ↦ ⟨ha.trans_le ht, h⟩⟩

/-- **The interval of nonvanishing.** Let `w` be continuous on `(-τ, T)`, `τ > 0`, `T > 0`, with
`w 0 ≠ 0`. There are `0 < δ ≤ τ` and `0 < t_end ≤ T` such that `w` does not vanish on
`(-δ, t_end)` and `w(t_end) = 0` if `t_end < T`. -/
theorem exists_nonvanishing_timeInterval {w : ℝ → ℝ} {τ : ℝ} {T : ℝ≥0∞} (hτ : 0 < τ)
    (hT : 0 < T) (hw : ContinuousOn w (timeInterval (-τ) T)) (hw0 : w 0 ≠ 0) :
    ∃ (δ : ℝ) (tEnd : ℝ≥0∞), 0 < δ ∧ δ ≤ τ ∧ 0 < tEnd ∧ tEnd ≤ T ∧
      (∀ t ∈ timeInterval (-δ) tEnd, w t ≠ 0) ∧ (tEnd < T → w tEnd.toReal = 0) := by
  set J₀ := timeInterval (-τ) T
  have hJ₀ : IsOpen J₀ := isOpen_timeInterval _ _
  have h0 : (0 : ℝ) ∈ J₀ := zero_mem_timeInterval (by linarith) hT
  -- a neighbourhood of `0` on which `w` does not vanish
  have hnhds : ∀ᶠ s in 𝓝 (0 : ℝ), s ∈ J₀ ∧ w s ≠ 0 :=
    Filter.Eventually.and (show ∀ᶠ s in 𝓝 (0 : ℝ), s ∈ J₀ from hJ₀.mem_nhds h0)
      ((hw.continuousAt (hJ₀.mem_nhds h0)).eventually_ne hw0)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hnhds
  set δ := min (ε / 2) τ
  have hδ : 0 < δ := lt_min (by linarith) hτ
  have hδε : δ < ε := (min_le_left _ _).trans_lt (by linarith)
  -- the nonnegative times up to which `w` does not vanish
  set P : ℝ → Prop := fun t ↦ 0 ≤ t ∧ t ∈ J₀ ∧ ∀ s ∈ Icc 0 t, w s ≠ 0
  set tEnd : ℝ≥0∞ := ⨆ (t : ℝ) (_ : P t), ENNReal.ofReal t
  have hball' {s : ℝ} (hs : |s| < ε) : s ∈ J₀ ∧ w s ≠ 0 :=
    hball (by rwa [Real.dist_eq, sub_zero])
  have hPδ : P (δ / 2) := ⟨by linarith, (hball' (by rw [abs_of_pos (by linarith)]; linarith)).1,
    fun s hs ↦ (hball' (by rw [abs_of_nonneg hs.1]; linarith [hs.2])).2⟩
  have htEnd0 : 0 < tEnd :=
    lt_of_lt_of_le (by simpa using hδ) (le_iSup₂_of_le (δ / 2) hPδ le_rfl)
  have hP_of_lt {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t < tEnd) :
      ∃ t', P t' ∧ t < t' := by
    obtain ⟨t', hPt', hlt⟩ := lt_biSup_iff.mp ht
    exact ⟨t', hPt', (ENNReal.ofReal_lt_ofReal_iff'.mp hlt).1⟩
  refine ⟨δ, tEnd, hδ, min_le_right _ _, htEnd0, iSup₂_le fun t hPt ↦ hPt.2.1.2.le, ?_, ?_⟩
  · rintro t ⟨htδ, ht⟩
    rcases lt_or_ge t 0 with ht0 | ht0
    · exact (hball' (by rw [abs_of_neg ht0]; linarith)).2
    · obtain ⟨t', hPt', htt'⟩ := hP_of_lt ht0 ht
      exact hPt'.2.2 t ⟨ht0, htt'.le⟩
  · intro hlt
    by_contra hne
    have htop : tEnd ≠ ⊤ := ne_top_of_lt hlt
    set te := tEnd.toReal
    have hte0 : 0 ≤ te := ENNReal.toReal_nonneg
    have hteJ₀ : te ∈ J₀ := ⟨by linarith, by rwa [ENNReal.ofReal_toReal htop]⟩
    -- `w` does not vanish on `[0, te]`
    have hbefore : ∀ s ∈ Icc 0 te, w s ≠ 0 := by
      intro s hs
      rcases hs.2.lt_or_eq with hst | rfl
      · obtain ⟨t', hPt', hst'⟩ := hP_of_lt hs.1
          ((ENNReal.ofReal_lt_iff_lt_toReal hs.1 htop).2 hst)
        exact hPt'.2.2 s ⟨hs.1, hst'.le⟩
      · exact hne
    -- and on a neighbourhood of `te`
    have hnear : ∀ᶠ s in 𝓝 te, s ∈ J₀ ∧ w s ≠ 0 :=
      Filter.Eventually.and (show ∀ᶠ s in 𝓝 te, s ∈ J₀ from hJ₀.mem_nhds hteJ₀)
        ((hw.continuousAt (hJ₀.mem_nhds hteJ₀)).eventually_ne hne)
    obtain ⟨η, hη, hηball⟩ := Metric.eventually_nhds_iff.1 hnear
    have hP' : P (te + η / 2) := by
      refine ⟨by linarith, (hηball (by
          rw [Real.dist_eq, show te + η / 2 - te = η / 2 by ring, abs_of_pos (by linarith)]
          linarith)).1, fun s hs ↦ ?_⟩
      rcases le_or_gt s te with hste | hste
      · exact hbefore s ⟨hs.1, hste⟩
      · exact (hηball (by
          rw [Real.dist_eq, abs_of_pos (by linarith)]
          linarith [hs.2])).2
    have hle : ENNReal.ofReal (te + η / 2) ≤ tEnd := le_iSup₂_of_le _ hP' le_rfl
    rw [← ENNReal.ofReal_toReal htop, ENNReal.ofReal_le_ofReal_iff hte0] at hle
    linarith

end PDE.Analysis
