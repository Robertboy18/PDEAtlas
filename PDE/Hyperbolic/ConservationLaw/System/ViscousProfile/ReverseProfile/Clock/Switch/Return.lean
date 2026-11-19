/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Clock.Middle
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.FastLogCosh
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Feedback

/-!
# Switching the fast-coordinate feedback and returning the scalar clock

Starting at height `415/2`, the equation `Y' = g(Y) + clockFeedback a b (Z)`
remains between `411/2` and `2087/10` during the next half-unit of time. A moving upper barrier
proves this bound.

Choosing `a = Z(T)` and `b = Z(T + 1/2)` on the increasing fast solution makes
the feedback equal one at `T` and exactly `-4` from `T + 1/2` onward. Any global
solution of this scalar equation has transverse first descending hits of 205 and zero.
The squared-state transition is used throughout; it is not replaced by a
transition evaluated at elapsed time.
-/

@[expose] public noncomputable section

open Set
open PDE.Analysis PDE.Analysis.NormalizedPulse

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile

namespace ClockSwitch

open MiddleClock

/-- The feedback equation stays in the stated band throughout a half-unit switch. -/
theorem switch_interval_bounds {Y Z : ℝ → ℝ} {a b T : ℝ}
    (hY : ∀ t, HasDerivAt Y (g (Y t) + clockFeedback a b (Z t)) t) (hstart : Y T = 415 / 2) :
    ∀ t ∈ Icc T (T + 1 / 2), 411 / 2 ≤ Y t ∧ Y t ≤ 2087 / 10 := by
  have hYd : Differentiable ℝ Y := fun t ↦ (hY t).differentiableAt
  have hderiv_lower (t : ℝ) : -4 ≤ deriv Y t := by
    rw [(hY t).deriv]
    linarith [(clockFeedback_mem_Icc a b (Z t)).1, g_nonneg (Y t)]
  have hupper : ∀ t ∈ Icc T (T + 1 / 2), Y t ≤ 415 / 2 + (12 / 5) * (t - T) := by
    intro t ht
    apply image_le_of_deriv_right_lt_deriv_boundary
      (f := Y) (f' := fun t ↦ g (Y t) + clockFeedback a b (Z t))
      (B := fun t : ℝ ↦ 415 / 2 + (12 / 5) * (t - T)) (B' := fun _ ↦ 12 / 5)
      (a := T) (b := T + 1 / 2) hYd.continuous.continuousOn
      (fun t _ ↦ (hY t).hasDerivWithinAt) ?_ ?_ ?_ ht
    · simp only [hstart, sub_self, mul_zero, add_zero, le_refl]
    · intro t
      simpa only [mul_one, id_eq] using
        (((hasDerivAt_id t).sub_const T).const_mul (12 / 5)).const_add (415 / 2)
    · intro t ht heq
      have hy0 : 0 ≤ Y t := by linarith [ht.1]
      have hy210 : Y t ≤ 210 := by linarith [ht.2]
      have hg := monotoneOn_g_nonneg hy0 (by norm_num : (0 : ℝ) ≤ 210) hy210
      linarith [g_210_lt, (clockFeedback_mem_Icc a b (Z t)).2]
  intro t ht
  have hlower := mul_sub_le_image_sub_of_le_deriv hYd hderiv_lower ht.1
  have hu := hupper t ht
  rw [hstart] at hlower
  constructor <;> linarith [ht.2]

private theorem strictMonoOn_fast_clock {δ : ℝ} {Z : ℝ → ℝ}
    (hδ : |δ| < 1 / 4) (hZ : ∀ t, HasDerivAt Z (fastLogCosh δ (Z t)) t)
    (hZlower : ∀ t, 0 ≤ t → 1 + t ≤ Z t) : StrictMonoOn Z (Ici 0) := by
  have hk : StrictMono (fastLogCosh δ) :=
    strictMono_of_deriv_pos fun s ↦ by
      linarith [seven_fourths_lt_deriv_fastLogCosh hδ s]
  have hkzero : fastLogCosh δ 0 = 0 := by simp [fastLogCosh]
  have hZd : Differentiable ℝ Z := fun t ↦ (hZ t).differentiableAt
  refine strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ)) hZd.continuous.continuousOn fun t ht ↦ ?_
  have ht0 : 0 ≤ t := interior_subset ht
  have hz0 : 0 < Z t := by linarith [hZlower t ht0]
  rw [(hZ t).deriv, ← hkzero]
  exact hk hz0

/-- Thresholds chosen from the fast trajectory give the switch endpoints. -/
theorem feedback_switch_properties {δ T : ℝ} {Z : ℝ → ℝ}
    (hδ : |δ| < 1 / 4) (hZ : ∀ t, HasDerivAt Z (fastLogCosh δ (Z t)) t)
    (hZlower : ∀ t, 0 ≤ t → 1 + t ≤ Z t) (hT : 1 ≤ T) :
    Z T ^ 2 < Z (T + 1 / 2) ^ 2 ∧ clockFeedback (Z T) (Z (T + 1 / 2)) (Z T) = 1 ∧ ∀ t ≥ T + 1 / 2,
      clockFeedback (Z T) (Z (T + 1 / 2)) (Z t) = -4 := by
  have hT0 : 0 ≤ T := by linarith
  have hS0 : 0 ≤ T + 1 / 2 := by linarith
  have hmono := strictMonoOn_fast_clock hδ hZ hZlower
  have hab : Z T < Z (T + 1 / 2) := hmono hT0 hS0 (by linarith)
  have ha0 : 0 < Z T := by linarith [hZlower T hT0]
  have hsum : 0 < Z (T + 1 / 2) + Z T := by linarith
  have habsq : Z T ^ 2 < Z (T + 1 / 2) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hab) hsum]
  refine ⟨habsq, ?_, ?_⟩
  · rw [clockFeedback_of_sq_le habsq le_rfl]
    apply transition_of_one_le
    nlinarith [hZlower T hT0, sq_nonneg (Z T - 2)]
  · intro t ht
    have ht0 : 0 ≤ t := hS0.trans ht
    have horder : Z (T + 1 / 2) ≤ Z t := hmono.monotoneOn hS0 ht0 ht
    apply clockFeedback_of_le_sq habsq
    have hsum' : 0 ≤ Z t + Z (T + 1 / 2) := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr horder) hsum']

/-- Once the feedback is `-4`, every lower nonnegative level has a transverse first hit.
The clock starts below 210. Only times from `S` on enter, where `Y` is differentiable. -/
theorem exists_first_descending_hit {Y : ℝ → ℝ} {S H : ℝ}
    (hY : ∀ t ≥ S, HasDerivAt Y (g (Y t) - 4) t) (hH : 0 ≤ H) (hstart : H < Y S)
    (hceiling : Y S < 210) :
    ∃ τ ∈ Ioc S (S + (Y S - H) / 2), Y τ = H ∧ (∀ t ∈ Ico S τ, H < Y t) ∧ HasDerivAt Y (g H - 4) τ ∧
      g H - 4 < -(13 / 5) := by
  have hYc : ContinuousOn Y (Ici S) := fun s hs ↦ (hY s hs).continuousAt.continuousWithinAt
  have hupper (t : ℝ) (ht : S ≤ t) : Y t ≤ 210 := by
    apply image_le_of_deriv_right_lt_deriv_boundary (f := Y) (f' := fun t ↦ g (Y t) - 4)
      (B := fun _ : ℝ ↦ 210) (B' := fun _ ↦ 0) (a := S) (b := t) (hYc.mono Icc_subset_Ici_self)
      (fun s hs ↦ (hY s hs.1).hasDerivWithinAt) hceiling.le
      (fun s ↦ hasDerivAt_const s (210 : ℝ)) ?_ ⟨ht, le_rfl⟩
    intro s _ heq
    rw [heq]
    linarith [g_210_lt]
  let L : ℝ := S + (Y S - H) / 2
  have hSL : S < L := by dsimp only [L]; linarith
  have hex : ∃ t ∈ Icc S L, Y t ≤ H := by
    by_contra hnone
    have habove (t : ℝ) (ht : t ∈ Icc S L) : H < Y t := by
      by_contra h
      exact hnone ⟨t, ht, le_of_not_gt h⟩
    have hderiv (t : ℝ) (ht : t ∈ interior (Icc S L)) : deriv Y t < -2 := by
      have htI : t ∈ Icc S L := interior_subset ht
      rw [(hY t htI.1).deriv]
      have hy0 : 0 ≤ Y t := hH.trans (habove t htI).le
      have hg := monotoneOn_g_nonneg hy0 (by norm_num : (0 : ℝ) ≤ 210) (hupper t htI.1)
      linarith [g_210_lt]
    have hmean := (convex_Icc S L).image_sub_lt_mul_sub_of_deriv_lt
      (hYc.mono Icc_subset_Ici_self)
      (fun s hs ↦ (hY s (interior_subset hs).1).differentiableAt.differentiableWithinAt) hderiv
      S ⟨le_rfl, hSL.le⟩ L ⟨hSL.le, le_rfl⟩ hSL
    have hlast := habove L ⟨hSL.le, le_rfl⟩
    dsimp only [L] at hmean
    linarith
  let A : Set ℝ := Icc S L ∩ {t | Y t ≤ H}
  have hcompact : IsCompact A :=
    isCompact_Icc.of_isClosed_subset ((hYc.mono Icc_subset_Ici_self).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_Iic) inter_subset_left
  have hnonempty : A.Nonempty := by
    obtain ⟨t, ht, hyt⟩ := hex
    exact ⟨t, ht, hyt⟩
  obtain ⟨τ, hτ, hmin⟩ := hcompact.exists_isMinOn hnonempty
    (f := fun t : ℝ ↦ t) continuous_id.continuousOn
  have hτS : S < τ := by
    by_contra h
    have heq : τ = S := le_antisymm (le_of_not_gt h) hτ.1.1
    have hbelow : Y τ ≤ H := hτ.2
    rw [heq] at hbelow
    linarith
  have hhit : Y τ = H := by
    obtain ⟨s, hs, hys⟩ := intermediate_value_Icc' hτS.le (hYc.mono Icc_subset_Ici_self)
      (show H ∈ Icc (Y τ) (Y S) from ⟨hτ.2, hstart.le⟩)
    have hsA : s ∈ A := ⟨⟨hs.1, hs.2.trans hτ.1.2⟩, hys.le⟩
    have hτs : τ ≤ s := (isMinOn_iff.mp hmin) s hsA
    have heq : s = τ := le_antisymm hs.2 hτs
    simpa only [heq] using hys
  refine ⟨τ, ⟨hτS, hτ.1.2⟩, hhit, ?_, ?_, ?_⟩
  · intro t ht
    by_contra h
    have htA : t ∈ A := ⟨⟨ht.1, ht.2.le.trans hτ.1.2⟩, le_of_not_gt h⟩
    have hτt : τ ≤ t := (isMinOn_iff.mp hmin) t htA
    exact (not_lt_of_ge hτt) ht.2
  · simpa only [hhit] using hY τ hτS.le
  · have hg := monotoneOn_g_nonneg hH (by norm_num : (0 : ℝ) ≤ 210) (hstart.le.trans hceiling.le)
    linarith [g_210_lt]

/-- The switched clock has transverse first descending hits of 205 and zero. -/
theorem exists_switch_return {δ T : ℝ} {Y Z : ℝ → ℝ} (hδ : |δ| < 1 / 4)
    (hZ : ∀ t, HasDerivAt Z (fastLogCosh δ (Z t)) t) (hZlower : ∀ t, 0 ≤ t → 1 + t ≤ Z t)
    (hT : 1 ≤ T) (hY : ∀ t, HasDerivAt Y (g (Y t) + clockFeedback (Z T) (Z (T + 1 / 2)) (Z t)) t)
    (hstart : Y T = 415 / 2) :
    ∃ τ205 τ0 : ℝ,
      Z T ^ 2 < Z (T + 1 / 2) ^ 2 ∧
      clockFeedback (Z T) (Z (T + 1 / 2)) (Z T) = 1 ∧
      (∀ t ≥ T + 1 / 2, clockFeedback (Z T) (Z (T + 1 / 2)) (Z t) = -4) ∧
      (∀ t ∈ Icc T (T + 1 / 2), 411 / 2 ≤ Y t ∧ Y t ≤ 2087 / 10) ∧
      T + 1 / 2 < τ205 ∧ τ205 < τ0 ∧ Y τ205 = 205 ∧ Y τ0 = 0 ∧
      (∀ t ∈ Ico T τ205, 205 < Y t) ∧
      (∀ t ∈ Ico T τ0, 0 < Y t) ∧
      HasDerivAt Y (g 205 - 4) τ205 ∧ g 205 - 4 < -(13 / 5) ∧
      HasDerivAt Y (-4) τ0 := by
  obtain ⟨horder, hon, hoff⟩ := feedback_switch_properties hδ hZ hZlower hT
  have hband := switch_interval_bounds hY hstart
  have hSband := hband (T + 1 / 2) ⟨by linarith, le_rfl⟩
  have hpost (t : ℝ) (ht : T + 1 / 2 ≤ t) : HasDerivAt Y (g (Y t) - 4) t := by
    simpa only [hoff t ht, sub_eq_add_neg] using hY t
  obtain ⟨τ205, hτ205, hhit205, hbefore205, hd205, hv205⟩ :=
    exists_first_descending_hit (S := T + 1 / 2) hpost (H := 205) (by norm_num)
      (by linarith [hSband.1]) (by linarith [hSband.2])
  obtain ⟨τ0, hτ0, hhit0, hbefore0, hd0, _⟩ :=
    exists_first_descending_hit (S := T + 1 / 2) hpost (H := 0) (by norm_num)
      (by linarith [hSband.1]) (by linarith [hSband.2])
  have hordered : τ205 < τ0 := by
    by_contra h
    rcases lt_or_eq_of_le (le_of_not_gt h) with ht | heq
    · have hbefore := hbefore205 τ0 ⟨hτ0.1.le, ht⟩
      rw [hhit0] at hbefore
      linarith
    · rw [heq, hhit205] at hhit0
      norm_num at hhit0
  refine ⟨τ205, τ0, horder, hon, hoff, hband, hτ205.1, hordered, hhit205,
    hhit0, ?_, ?_, hd205, hv205, ?_⟩
  · intro t ht
    by_cases hs : t ≤ T + 1 / 2
    · have hb := hband t ⟨ht.1, hs⟩
      linarith [hb.1]
    · exact hbefore205 t ⟨(lt_of_not_ge hs).le, ht.2⟩
  · intro t ht
    by_cases hs : t ≤ T + 1 / 2
    · have hb := hband t ⟨ht.1, hs⟩
      linarith [hb.1]
    · exact hbefore0 t ⟨(lt_of_not_ge hs).le, ht.2⟩
  · simpa only [g_zero, zero_sub] using hd0

end ClockSwitch

end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
