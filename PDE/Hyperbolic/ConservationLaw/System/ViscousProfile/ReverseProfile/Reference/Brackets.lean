/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Clock.Passage.Integrals

import CAS.ExactTactic

/-!
# Reference brackets for the retained prescribed clock

The endpoints are midpoints of times belonging to the supplied passage data.
The supplied family agrees with this same prescribed clock at parameter zero.
The common clock is used only through its descending 205 hit; below that hit,
the prescribed clock's strict decrease and its zero supply the range.
-/

@[expose] public noncomputable section

open Set
open PDE.Analysis

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

open ClockSwitch MiddleClock Gate.Weights

/-- Deterministic reference brackets for the supplied common clock, its prescribed
extension, the retained passage data, and the same family's upward event.
Only reference identities are assumed for the family. The slow ranges, strict
endpoint slack, and squared fast-state margins are derived on closed brackets. -/
theorem prescribed_clock_reference_brackets {Y Z X : ℝ → ℝ} {T τ205 τ0 upBaseTime A B : ℝ}
    {D : PassageData} {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {Bhit : ℝ × ℝ → ℝ}
    (hZ : ∀ t, HasDerivAt Z (2 * Z t) t) (hZlower : ∀ t, 0 ≤ t → 1 + t ≤ Z t) (hT : 1 ≤ T)
    (hY : ∀ t, HasDerivAt Y (g (Y t) + clockFeedback (Z T) (Z (T + 1 / 2)) (Z t)) t)
    (hYzero : Y 0 = 0) (hYT : Y T = 415 / 2) (hτ205 : T + 1 / 2 < τ205) (hhit205 : Y τ205 = 205)
    (hbefore205 : ∀ t ∈ Ico T τ205, 205 < Y t) (heqXY : EqOn X Y (Icc 0 τ205)) (hτ0 : τ205 ≤ τ0)
    (hzero : X τ0 = 0) (hantiX : StrictAntiOn X (Icc τ205 τ0)) (hupBase : D.tPlus 205 = upBaseTime)
    (hgate : ∀ y ∈ Icc (205 : ℝ) (2051 / 10), D.tPlus y ∈ Ioo 1 T ∧ D.tMinus y ∈
      Ioc (T + 1 / 2) τ205 ∧ Y (D.tPlus y) = y ∧ Y (D.tMinus y) = y)
    (hA : A = Z T) (hB : B = Z (T + 1 / 2))
    (href : EqOn (fun t ↦ F (t, (0, 0))) (fun t ↦ (X t, Z t)) (Icc (-1 : ℝ) (τ0 + 1)))
    (hBtime : Bhit (0, 0) ∈ Ioo (1 : ℝ) T) (hBhit : (F (Bhit (0, 0), (0, 0))).1 = 205) :
    let sUp := (1 + upBaseTime) / 2
    let eUp := (D.tPlus (2051 / 10) + T) / 2
    let sDown := (T + 1 / 2 + D.tMinus (2051 / 10)) / 2
    A ^ 2 < B ^ 2 ∧
      Bhit (0, 0) ∈ Ioo sUp eUp ∧
      (-1 ≤ sDown ∧ sDown < τ0) ∧
      (∀ t ∈ Icc sUp eUp,
        (F (t, (0, 0))).1 ∈ Ioo (0 : ℝ) 210 ∧
          2 < (F (t, (0, 0))).2 ∧ (F (t, (0, 0))).2 ^ 2 < A ^ 2) ∧
      (∀ t ∈ Icc sDown τ0,
        (F (t, (0, 0))).1 ∈ Ico (0 : ℝ) 210 ∧
          B ^ 2 < (F (t, (0, 0))).2 ^ 2) ∧
      (F (sUp, (0, 0))).1 < 205 ∧
      (2051 / 10 : ℝ) < (F (eUp, (0, 0))).1 ∧
      (2051 / 10 : ℝ) < (F (sDown, (0, 0))).1 ∧
      Icc sUp eUp ⊆ Icc (-1 : ℝ) (τ0 + 1) := by
  intro sUp eUp sDown
  have hδ : |(0 : ℝ)| < 1 / 4 := by cas
  have hZfast (t : ℝ) : HasDerivAt Z (fastLogCosh 0 (Z t)) t := by
    simpa only [fastLogCosh, zero_mul, add_zero] using hZ t
  have hpre := (clock_bounds_before_switch hδ hZfast hZlower hT hY hYzero hYT).1
  obtain ⟨hup, hdown, hband⟩ := ClockSwitch.clock_gate_branch_properties hδ hZfast hZlower hT
      hY hYzero hYT hhit205 hbefore205
  have hmono := strictMonoOn_clock_upward hup
  have hantiY := strictAntiOn_clock_downward hdown hband
  have hZsq := strictMonoOn_fast_clock_sq hδ hZfast hZlower
  let S := T + 1 / 2
  let u := D.tPlus (2051 / 10)
  let m := D.tMinus (2051 / 10)
  have hTS : T < S := lt_add_of_pos_right T (by norm_num)
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hS0 : 0 ≤ S := hT0.trans hTS.le
  have hT205 : T ≤ τ205 := hTS.le.trans hτ205.le
  have hTτ0 : T ≤ τ0 := hT205.trans hτ0
  have hneg : (-1 : ℝ) ≤ 0 := by norm_num
  have hhigh : (205 : ℝ) < 2051 / 10 := by norm_num
  obtain ⟨hbTime, _, hbY, _⟩ := hgate 205 ⟨le_rfl, hhigh.le⟩
  rw [hupBase] at hbTime hbY
  obtain ⟨huTime, hmTime, huY, hmY⟩ := hgate (2051 / 10) ⟨hhigh.le, le_rfl⟩
  have hbI : upBaseTime ∈ Icc 1 T := ⟨hbTime.1.le, hbTime.2.le⟩
  have huI : u ∈ Icc 1 T := ⟨huTime.1.le, huTime.2.le⟩
  have hmI : m ∈ Icc S τ205 := ⟨hmTime.1.le, hmTime.2⟩
  have hbu : upBaseTime < u := (hmono.lt_iff_lt hbI huI).mp (by rw [hbY, huY]; exact hhigh)
  have hm205 : m < τ205 :=
    (hantiY.lt_iff_gt ⟨hτ205.le, le_rfl⟩ hmI).mp (by rw [hhit205, hmY]; exact hhigh)
  have h1s : 1 < sUp := left_lt_add_div_two.mpr hbTime.1
  have hsb : sUp < upBaseTime := add_div_two_lt_right.mpr hbTime.1
  have hue : u < eUp := left_lt_add_div_two.mpr huTime.2
  have heT : eUp < T := add_div_two_lt_right.mpr huTime.2
  have hSd : S < sDown := left_lt_add_div_two.mpr hmTime.1
  have hdm : sDown < m := add_div_two_lt_right.mpr hmTime.1
  have hsI : sUp ∈ Icc 1 T := ⟨h1s.le, (hsb.trans (hbu.trans (hue.trans heT))).le⟩
  have heI : eUp ∈ Icc 1 T := ⟨(h1s.trans (hsb.trans (hbu.trans hue))).le, heT.le⟩
  have hdI : sDown ∈ Icc S τ205 := ⟨hSd.le, (hdm.trans hm205).le⟩
  have htime (t : ℝ) (ht : t ∈ Icc 1 T) : t ∈ Icc 0 τ205 :=
    ⟨zero_le_one.trans ht.1, ht.2.trans hT205⟩
  have hFref (t : ℝ) (ht0 : 0 ≤ t) (htτ0 : t ≤ τ0) : F (t, (0, 0)) = (X t, Z t) :=
    href ⟨hneg.trans ht0, htτ0.trans (le_add_of_nonneg_right zero_le_one)⟩
  have hFup (t : ℝ) (ht : t ∈ Icc 1 T) : F (t, (0, 0)) = (Y t, Z t) := by
    rw [hFref t (htime t ht).1 (ht.2.trans hTτ0), heqXY (htime t ht)]
  have hFdown (t : ℝ) (ht : t ∈ Icc S τ205) : F (t, (0, 0)) = (Y t, Z t) := by
    rw [hFref t (hS0.trans ht.1) (ht.2.trans hτ0), heqXY ⟨hS0.trans ht.1, ht.2⟩]
  have hBI : Bhit (0, 0) ∈ Icc 1 T := ⟨hBtime.1.le, hBtime.2.le⟩
  have hBeq : Bhit (0, 0) = upBaseTime := hmono.injOn hBI hbI
    ((show Y (Bhit (0, 0)) = 205 by simpa only [hFup _ hBI] using hBhit).trans hbY.symm)
  refine ⟨by rw [hA, hB]; exact hZsq hT0 hS0 hTS, hBeq ▸ ⟨hsb, hbu.trans hue⟩,
    ⟨hneg.trans (hS0.trans hSd.le), (hdm.trans hm205).trans_le hτ0⟩, fun t ht ↦ ?_,
    fun t ht ↦ ?_, (congrArg Prod.fst (hFup sUp hsI)).trans_lt ((hmono hsI hbI hsb).trans_eq hbY),
    huY.symm.trans_lt ((hmono huI heI hue).trans_eq (congrArg Prod.fst (hFup eUp heI)).symm),
    hmY.symm.trans_lt ((hantiY hdI hmI hdm).trans_eq (congrArg Prod.fst (hFdown sDown hdI)).symm),
    Icc_subset_Icc (hneg.trans (htime sUp hsI).1)
      (heI.2.trans (hTτ0.trans (le_add_of_nonneg_right zero_le_one)))⟩
  · have ht1 : 1 < t := h1s.trans_le ht.1
    have htI : t ∈ Icc 1 T := ⟨ht1.le, (ht.2.trans_lt heT).le⟩
    have ht0 : 0 ≤ t := (htime t htI).1
    rw [hFup t htI]
    exact ⟨⟨(hpre 1 ⟨zero_le_one, hT⟩).1.1.trans_lt (hmono ⟨le_rfl, hT⟩ htI ht1),
      (hpre t ⟨ht0, htI.2⟩).1.2.trans_lt (by norm_num)⟩, by linarith [hZlower t ht0],
      by rw [hA]; exact hZsq ht0 hT0 (ht.2.trans_lt heT)⟩
  · have hSt : S < t := hSd.trans_le ht.1
    have ht0 : 0 ≤ t := hS0.trans hSt.le
    rw [hFref t ht0 ht.2]
    refine ⟨?_, by rw [hB]; exact hZsq hS0 ht0 hSt⟩
    rcases le_or_gt t τ205 with ht205 | ht205
    · have htI : t ∈ Icc S τ205 := ⟨hSt.le, ht205⟩
      rw [heqXY ⟨ht0, ht205⟩]
      exact ⟨(by norm_num : (0 : ℝ) ≤ 205).trans (hband t htI).1,
        ((hantiY.antitoneOn ⟨le_rfl, hτ205.le⟩ htI htI.1).trans
          (switch_interval_bounds hY hYT S ⟨hTS.le, le_rfl⟩).2).trans_lt (by norm_num)⟩
    · have htI : t ∈ Icc τ205 τ0 := ⟨ht205.le, ht.2⟩
      have hx0 := hantiX.antitoneOn htI ⟨hτ0, le_rfl⟩ ht.2
      have hx205 := hantiX.antitoneOn ⟨le_rfl, hτ0⟩ htI htI.1
      rw [hzero] at hx0
      rw [(heqXY ⟨hS0.trans hτ205.le, le_rfl⟩).trans hhit205] at hx205
      exact ⟨hx0, hx205.trans_lt (by norm_num)⟩

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
