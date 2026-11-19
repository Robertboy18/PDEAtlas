/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Clock.Passage.Integrals

import CAS.ExactTactic

/-!
# Closed chronological margins for the retained reference clock

The two cuts are the supplied passage times of `41001/200`. The midpoint brackets
are exactly those of `prescribed_clock_reference_brackets`. The four original
closed-interval margins are retained. Two further conclusions exclude the entire
open gate before the upper bracket and between the branches. The lower
extension `X` is used through its own zero.

The common branch properties are supplied by `clock_gate_branch_properties`.
-/

@[expose] public noncomputable section

open Set
open PDE.Analysis PDE.Analysis.NormalizedPulse

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

open ClockSwitch MiddleClock Gate.Weights

/-- The retained reference has strict margins on the chronological complements of
its two gate branches. The hypotheses are the clock and passage-data hypotheses of
`prescribed_clock_reference_brackets`; family and event-map hypotheses are unnecessary.
After the descending 205 hit, only the supplied extension and its zero are used.
The final two bounds exclude the full gate on the complementary fixed intervals. -/
theorem prescribed_clock_reference_itinerary {Y Z X : ℝ → ℝ} {T τ205 τ0 upBaseTime A B : ℝ}
    {D : PassageData} (hZ : ∀ t, HasDerivAt Z (2 * Z t) t) (hZlower : ∀ t, 0 ≤ t → 1 + t ≤ Z t)
    (hT : 1 ≤ T) (hY : ∀ t, HasDerivAt Y (g (Y t) + clockFeedback (Z T) (Z (T + 1 / 2)) (Z t)) t)
    (hYzero : Y 0 = 0) (hYT : Y T = 415 / 2) (hτ205 : T + 1 / 2 < τ205) (hhit205 : Y τ205 = 205)
    (hbefore205 : ∀ t ∈ Ico T τ205, 205 < Y t) (heqXY : EqOn X Y (Icc 0 τ205)) (hτ0 : τ205 ≤ τ0)
    (hzero : X τ0 = 0) (hantiX : StrictAntiOn X (Icc τ205 τ0)) (hupBase : D.tPlus 205 = upBaseTime)
    (hgate : ∀ y ∈ Icc (205 : ℝ) (2051 / 10), D.tPlus y ∈ Ioo 1 T ∧ D.tMinus y ∈
      Ioc (T + 1 / 2) τ205 ∧ Y (D.tPlus y) = y ∧ Y (D.tMinus y) = y)
    (hA : A = Z T) (hB : B = Z (T + 1 / 2)) :
    let sUp := (1 + upBaseTime) / 2
    let eUp := (D.tPlus (2051 / 10) + T) / 2
    let sDown := (T + 1 / 2 + D.tMinus (2051 / 10)) / 2
    let rUp := D.tPlus (41001 / 200)
    let rDown := D.tMinus (41001 / 200)
    (0 < sUp ∧ sUp < rUp ∧ rUp < eUp ∧ eUp < sDown ∧
      sDown < rDown ∧ rDown < τ0) ∧
      (∀ t ∈ Icc 0 rUp, X t ∈ Ioo (-1 : ℝ) (20501 / 100) ∧ Z t ^ 2 < A ^ 2) ∧
      (∀ t ∈ Icc rUp rDown, 205 < X t) ∧
      (∀ t ∈ Icc eUp sDown, (20509 / 100 : ℝ) < X t) ∧
      (∀ t ∈ Icc rDown τ0, X t ∈ Ioo (-1 : ℝ) (20501 / 100) ∧ B ^ 2 < Z t ^ 2) ∧
      (∀ t ∈ Icc 0 sUp, X t < 205) ∧
      (∀ t ∈ Icc eUp sDown, (2051 / 10 : ℝ) < X t) := by
  intro sUp eUp sDown rUp rDown
  have hδ : |(0 : ℝ)| < 1 / 4 := by cas
  have hZfast (t : ℝ) : HasDerivAt Z (fastLogCosh 0 (Z t)) t := by
    simpa only [fastLogCosh, zero_mul, add_zero] using hZ t
  obtain ⟨hup, hdown, hband⟩ := ClockSwitch.clock_gate_branch_properties hδ hZfast hZlower hT
      hY hYzero hYT hhit205 hbefore205
  have hmono := strictMonoOn_clock_upward hup
  have hanti := strictAntiOn_clock_downward hdown hband
  have hZsq := strictMonoOn_fast_clock_sq hδ hZfast hZlower
  have hinner := feedback_eq_inner_before_switch hδ hZfast hZlower hT
  have hmono0 : MonotoneOn Y (Icc 0 T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 T)
      (fun t _ ↦ (hY t).continuousAt.continuousWithinAt)
      (fun t _ ↦ (hY t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hY t).deriv, hinner t (interior_subset ht)]
    exact add_nonneg (g_nonneg (Y t)) (transition_nonneg _)
  let S := T + 1 / 2
  let u := D.tPlus (2051 / 10)
  let m := D.tMinus (2051 / 10)
  have hκlo : (205 : ℝ) < 41001 / 200 := by norm_num
  have hκhi : (41001 / 200 : ℝ) < 2051 / 10 := by norm_num
  have hκouter : (41001 / 200 : ℝ) < 20501 / 100 := by norm_num
  have hTS : T < S := lt_add_of_pos_right T (by norm_num)
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hS0 : 0 ≤ S := hT0.trans hTS.le
  have hT205 : T ≤ τ205 := hTS.le.trans hτ205.le
  obtain ⟨hbTime, _, hbY, _⟩ := hgate 205 ⟨le_rfl, (hκlo.trans hκhi).le⟩
  rw [hupBase] at hbTime hbY
  obtain ⟨huTime, hmTime, huY, hmY⟩ := hgate (2051 / 10) ⟨(hκlo.trans hκhi).le, le_rfl⟩
  obtain ⟨hrTime, hdTime, hrY, hdY⟩ := hgate (41001 / 200) ⟨hκlo.le, hκhi.le⟩
  have hbI : upBaseTime ∈ Icc 1 T := ⟨hbTime.1.le, hbTime.2.le⟩
  have huI : u ∈ Icc 1 T := ⟨huTime.1.le, huTime.2.le⟩
  have hrI : rUp ∈ Icc 1 T := ⟨hrTime.1.le, hrTime.2.le⟩
  have hmI : m ∈ Icc S τ205 := ⟨hmTime.1.le, hmTime.2⟩
  have hdI : rDown ∈ Icc S τ205 := ⟨hdTime.1.le, hdTime.2⟩
  have hbr : upBaseTime < rUp := (hmono.lt_iff_lt hbI hrI).mp (by rw [hbY, hrY]; exact hκlo)
  have hru : rUp < u := (hmono.lt_iff_lt hrI huI).mp (by rw [hrY, huY]; exact hκhi)
  have hmd : m < rDown := (hanti.lt_iff_gt hdI hmI).mp (by rw [hdY, hmY]; exact hκhi)
  have hd205 : rDown < τ205 :=
    (hanti.lt_iff_gt ⟨hτ205.le, le_rfl⟩ hdI).mp (by rw [hhit205, hdY]; exact hκlo)
  have h1s : 1 < sUp := left_lt_add_div_two.mpr hbTime.1
  have hsb : sUp < upBaseTime := add_div_two_lt_right.mpr hbTime.1
  have hue : u < eUp := left_lt_add_div_two.mpr huTime.2
  have heT : eUp < T := add_div_two_lt_right.mpr huTime.2
  have hSd : S < sDown := left_lt_add_div_two.mpr hmTime.1
  have hdm : sDown < m := add_div_two_lt_right.mpr hmTime.1
  have hre : rUp < eUp := hru.trans hue
  have hsdr : sDown < rDown := hdm.trans hmd
  have hr0 : 0 ≤ rUp := zero_le_one.trans hrI.1
  have hbetweenAll : ∀ t ∈ Icc eUp sDown, (2051 / 10 : ℝ) < X t := by
    intro t ht
    have ht205 : t ≤ τ205 := ht.2.trans (hsdr.le.trans hd205.le)
    rw [heqXY ⟨hr0.trans (hre.le.trans ht.1), ht205⟩]
    rcases le_or_gt t T with htT | htT
    · exact huY.symm.trans_lt (hmono huI ⟨huI.1.trans (hue.le.trans ht.1), htT⟩ (hue.trans_le ht.1))
    rcases le_or_gt t S with htS | htS
    · exact (by norm_num : (2051 / 10 : ℝ) < 411 / 2).trans_le
        (switch_interval_bounds hY hYT t ⟨htT.le, htS⟩).1
    · exact hmY.symm.trans_lt (hanti ⟨htS.le, ht205⟩ hmI (ht.2.trans_lt hdm))
  refine ⟨⟨zero_lt_one.trans h1s, hsb.trans hbr, hre, heT.trans (hTS.trans hSd), hsdr,
    hd205.trans_le hτ0⟩, fun t ht ↦ ?_, fun t ht ↦ ?_,
    fun t ht ↦ (by norm_num : (20509 / 100 : ℝ) < 2051 / 10).trans (hbetweenAll t ht),
    fun t ht ↦ ?_, fun t ht ↦ ?_, hbetweenAll⟩
  · have htT : t < T := ht.2.trans_lt hrTime.2
    have htI : t ∈ Icc 0 T := ⟨ht.1, htT.le⟩
    rw [heqXY ⟨ht.1, htT.le.trans hT205⟩, hA]
    exact ⟨⟨(by norm_num : (-1 : ℝ) < 0).trans_le
      (by simpa only [hYzero] using hmono0 ⟨le_rfl, hT0⟩ htI ht.1),
      ((hmono0 htI ⟨hr0, hrTime.2.le⟩ ht.2).trans_eq hrY).trans_lt hκouter⟩, hZsq ht.1 hT0 htT⟩
  · have ht205 : t < τ205 := ht.2.trans_lt hd205
    rw [heqXY ⟨hr0.trans ht.1, ht205.le⟩]
    rcases le_or_gt t T with htT | htT
    · exact hκlo.trans_le (hrY.symm.trans_le (hmono.monotoneOn hrI ⟨hrI.1.trans ht.1, htT⟩ ht.1))
    · exact hbefore205 t ⟨htT.le, ht205⟩
  · have hSt : S < t := hdTime.1.trans_le ht.1
    have ht0 : 0 ≤ t := hS0.trans hSt.le
    refine ⟨?_, by rw [hB]; exact hZsq hS0 ht0 hSt⟩
    rcases le_or_gt t τ205 with ht205 | ht205
    · rw [heqXY ⟨ht0, ht205⟩]
      have htI : t ∈ Icc S τ205 := ⟨hSt.le, ht205⟩
      exact ⟨(by norm_num : (-1 : ℝ) < 205).trans_le (hband t htI).1,
        ((hanti.antitoneOn hdI htI ht.1).trans_eq hdY).trans_lt hκouter⟩
    · have htI : t ∈ Icc τ205 τ0 := ⟨ht205.le, ht.2⟩
      have hx0 := hantiX.antitoneOn htI ⟨hτ0, le_rfl⟩ ht.2
      have hx205 := hantiX.antitoneOn ⟨le_rfl, hτ0⟩ htI htI.1
      rw [hzero] at hx0
      rw [heqXY ⟨hT0.trans hT205, le_rfl⟩, hhit205] at hx205
      exact ⟨(by norm_num : (-1 : ℝ) < 0).trans_le hx0, hx205.trans_lt (by norm_num)⟩
  · have hsT : sUp < T := hsb.trans hbTime.2
    have htT : t ≤ T := ht.2.trans hsT.le
    rw [heqXY ⟨ht.1, htT.trans hT205⟩]
    exact (hmono0 ⟨ht.1, htT⟩ ⟨zero_le_one.trans h1s.le, hsT.le⟩ ht.2).trans_lt
      ((hmono ⟨h1s.le, hsT.le⟩ hbI hsb).trans_eq hbY)

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
