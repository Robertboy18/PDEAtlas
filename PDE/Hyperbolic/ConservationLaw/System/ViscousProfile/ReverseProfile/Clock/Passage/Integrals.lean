/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Clock.Passage.Times
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Weights.Concrete

import CAS.ExactTactic

/-!
# Integral identification of the gate passages

The upward integral is anchored at the passage through 205. The downward
integral retains the full denominator `4 - g + 4 * cutoff`, and its additive
anchor is the descending passage through 205 plus `downTime 205`.

On the upper descending segment the equation is `Y' = g(Y) - 4` and
`cutoff(Y) = 0`. Consequently the integral time evaluated along that segment
has derivative one. The analogous identity holds during the ascent, where
`Y' = g(Y) + 1`. Constancy after subtracting elapsed time identifies the chosen
passage witnesses on the closed gate, including both endpoints. Strict
monotonicity gives uniqueness on the two passage intervals.

The clock supplies the separation. The same bound therefore holds for the integral times and makes
their value-weight ratio smaller than `1/100`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open PDE.Analysis

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.ClockSwitch

open Gate.Weights MiddleClock

/-- The lower endpoint of the closed gate, used to fix both additive anchors. -/
def clockGateBase : Icc (205 : ℝ) (2051 / 10) :=
  ⟨205, by norm_num⟩

/-- Passage data anchored at the supplied base passage times. `terminalTime` is an additive integral
anchor. -/
def clockGatePassageData (upBaseTime downBaseTime speedConstant : ℝ) : PassageData :=
  clockPassageData 205 upBaseTime
    (downBaseTime + (clockPassageData 205 upBaseTime 0 speedConstant).downTime 205)
    speedConstant

/-- The downward additive anchor retains the complete lower cutoff integral. -/
theorem clockGatePassageData_terminalTime (upBaseTime downBaseTime speedConstant : ℝ) :
    (clockGatePassageData upBaseTime downBaseTime speedConstant).terminalTime =
      downBaseTime + (clockGatePassageData upBaseTime downBaseTime speedConstant).downTime 205 :=
  rfl

/-- The upward integral vanishes at its base. -/
theorem clockGatePassageData_tPlus_base (upBaseTime downBaseTime speedConstant : ℝ) :
    (clockGatePassageData upBaseTime downBaseTime speedConstant).tPlus 205 = upBaseTime := by
  simp [clockGatePassageData, clockPassageData, PassageData.tPlus]

/-- Subtracting the full lower integral recovers the supplied downward base time. -/
theorem clockGatePassageData_tMinus_base (upBaseTime downBaseTime speedConstant : ℝ) :
    (clockGatePassageData upBaseTime downBaseTime speedConstant).tMinus 205 = downBaseTime := by
  change (downBaseTime + (clockPassageData 205 upBaseTime 0 speedConstant).downTime 205) -
    (clockPassageData 205 upBaseTime 0 speedConstant).downTime 205 = downBaseTime
  exact add_sub_cancel_right _ _

/-- The descending solution cannot cross the constant upper barrier 210.
This recovers a fact local to the first-return provider without rebuilding it. -/
theorem clock_le_210_after_switch {Y : ℝ → ℝ} {S : ℝ} (hYd : Differentiable ℝ Y)
    (hY : ∀ t ≥ S, HasDerivAt Y (g (Y t) - 4) t) (hstart : Y S ≤ 210) :
    ∀ t ≥ S, Y t ≤ 210 := by
  intro t ht
  apply image_le_of_deriv_right_lt_deriv_boundary (f := Y) (f' := fun t ↦ g (Y t) - 4)
    (B := fun _ : ℝ ↦ 210) (B' := fun _ ↦ 0) (a := S) (b := t) hYd.continuous.continuousOn
    (fun s hs ↦ (hY s hs.1).hasDerivWithinAt) hstart
    (fun s ↦ hasDerivAt_const s (210 : ℝ)) ?_ ⟨ht, le_rfl⟩
  intro s _ heq
  rw [heq]
  linarith only [g_210_lt]

/-- The upward equation is strictly increasing from time one onward,
up to the attained switch height. -/
theorem strictMonoOn_clock_upward {Y : ℝ → ℝ} {T : ℝ}
    (hY : ∀ t ∈ Icc 1 T, HasDerivAt Y (g (Y t) + 1) t) :
    StrictMonoOn Y (Icc 1 T) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 1 T)
    (fun t ht ↦ (hY t ht).continuousAt.continuousWithinAt)
  intro t ht
  rw [(hY t (interior_subset ht)).deriv]
  linarith only [g_nonneg (Y t)]

/-- The descending equation is strictly decreasing while its values
remain between 205 and 210. The existence theorem derives this range. -/
theorem strictAntiOn_clock_downward {Y : ℝ → ℝ} {S U : ℝ}
    (hY : ∀ t ∈ Icc S U, HasDerivAt Y (g (Y t) - 4) t)
    (hband : ∀ t ∈ Icc S U, Y t ∈ Icc (205 : ℝ) 210) :
    StrictAntiOn Y (Icc S U) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc S U)
    (fun t ht ↦ (hY t ht).continuousAt.continuousWithinAt)
  intro t ht
  have htI := interior_subset ht
  have hy := hband t htI
  have hg := (monotoneOn_g_nonneg (show 0 ≤ Y t by linarith only [hy.1])
    (show (0 : ℝ) ≤ 210 by norm_num) hy.2).trans_lt g_210_lt
  rw [(hY t htI).deriv]
  linarith only [hg]

/-- Anchoring at the base witnesses identifies any passage witnesses on the two
autonomous segments. -/
theorem clock_gate_integral_times_eq {Y : ℝ → ℝ} {T S U : ℝ}
    {tPlus tMinus : Icc (205 : ℝ) (2051 / 10) → ℝ}
    (hup : ∀ t ∈ Icc 1 T, HasDerivAt Y (g (Y t) + 1) t)
    (hdown : ∀ t ∈ Icc S U, HasDerivAt Y (g (Y t) - 4) t)
    (hband : ∀ t ∈ Icc S U, Y t ∈ Icc (205 : ℝ) 210)
    (hpass : ∀ y, tPlus y ∈ Icc 1 T ∧ tMinus y ∈ Icc S U ∧
      Y (tPlus y) = y ∧ Y (tMinus y) = y) (speedConstant : ℝ) :
    let D := clockGatePassageData (tPlus clockGateBase) (tMinus clockGateBase) speedConstant
    ∀ y : Icc (205 : ℝ) (2051 / 10), D.tPlus y = tPlus y ∧ D.tMinus y = tMinus y := by
  let D := clockGatePassageData (tPlus clockGateBase) (tMinus clockGateBase) speedConstant
  change ∀ y : Icc (205 : ℝ) (2051 / 10), D.tPlus y = tPlus y ∧ D.tMinus y = tMinus y
  have hplusConst := PDE.Analysis.integral_reciprocal_comp_sub_eq
    (d := fun v ↦ g v + 1) (base := 205) (c := 1) (contDiff_g.continuous.add continuous_const)
    (fun t ht ↦ by simpa only [mul_one] using hup t ht)
    (fun _ _ v _ ↦ ne_of_gt (add_pos_of_nonneg_of_pos (g_nonneg v) zero_lt_one))
  have hd : Continuous D.downSpeed := (continuous_const.sub contDiff_g.continuous).add
      (continuous_const.mul contDiff_cutoff.continuous)
  have hdownFlow (t : ℝ) (ht : t ∈ Icc S U) :
      HasDerivAt Y (D.downSpeed (Y t) * (-1)) t := by
    apply (hdown t ht).congr_deriv
    change g (Y t) - 4 = (4 - g (Y t) + 4 * cutoff (Y t)) * (-1)
    rw [cutoff_of_ge (hband t ht).1]
    ring
  have hne : ∀ t ∈ Icc S U, ∀ v ∈ uIcc (0 : ℝ) (Y t), D.downSpeed v ≠ 0 := by
    intro t ht v hv
    have hy0 : 0 ≤ Y t := (by norm_num : (0 : ℝ) ≤ 205).trans (hband t ht).1
    rw [uIcc_of_le hy0] at hv
    exact ne_of_gt (MiddleClock.lower_denominator_pos hv.1 (hv.2.trans (hband t ht).2))
  have hminusConst := PDE.Analysis.integral_reciprocal_comp_sub_eq hd hdownFlow hne
  obtain ⟨hbPlus, hbMinus, hhitBasePlus, hhitBaseMinus⟩ := hpass clockGateBase
  intro y
  obtain ⟨hyPlus, hyMinus, hhitPlus, hhitMinus⟩ := hpass y
  constructor
  · have heq := (hplusConst (tPlus y) hyPlus).trans (hplusConst (tPlus clockGateBase) hbPlus).symm
    rw [hhitPlus, hhitBasePlus] at heq
    change (∫ v in (205 : ℝ)..(y : ℝ), 1 / (g v + 1)) - 1 * tPlus y =
      (∫ v in (205 : ℝ)..(205 : ℝ), 1 / (g v + 1)) - 1 * tPlus clockGateBase at heq
    simp only [one_mul, intervalIntegral.integral_same, zero_sub] at heq
    change tPlus clockGateBase + (∫ v in (205 : ℝ)..(y : ℝ), 1 / (g v + 1)) = tPlus y
    linarith
  · have heq := (hminusConst (tMinus y) hyMinus).trans
      (hminusConst (tMinus clockGateBase) hbMinus).symm
    rw [hhitMinus, hhitBaseMinus] at heq
    change D.downTime y - (-1) * tMinus y = D.downTime 205 - (-1) * tMinus clockGateBase at heq
    simp only [neg_one_mul, sub_neg_eq_add] at heq
    change (tMinus clockGateBase + D.downTime 205) - D.downTime y = tMinus y
    linarith

/-- The two autonomous equations and the full descending range of a supplied
common clock. The range includes the descending endpoint at 205. -/
theorem clock_gate_branch_properties {δ : ℝ} {Y Z : ℝ → ℝ} {T τ205 : ℝ} (hδ : |δ| < 1 / 4)
    (hZ : ∀ t, HasDerivAt Z (fastLogCosh δ (Z t)) t) (hZlower : ∀ t, 0 ≤ t → 1 + t ≤ Z t)
    (hT : 1 ≤ T) (hY : ∀ t, HasDerivAt Y (g (Y t) + clockFeedback (Z T) (Z (T + 1 / 2)) (Z t)) t)
    (hYzero : Y 0 = 0) (hYhit : Y T = 415 / 2) (hhit205 : Y τ205 = 205)
    (hbefore205 : ∀ t ∈ Ico T τ205, 205 < Y t) :
    (∀ t ∈ Icc 1 T, HasDerivAt Y (g (Y t) + 1) t) ∧
      (∀ t ∈ Icc (T + 1 / 2) τ205, HasDerivAt Y (g (Y t) - 4) t) ∧
      (∀ t ∈ Icc (T + 1 / 2) τ205, Y t ∈ Icc (205 : ℝ) 210) := by
  have hYd : Differentiable ℝ Y := fun t ↦ (hY t).differentiableAt
  have hup := (clock_bounds_before_switch hδ hZ hZlower hT hY hYzero hYhit).2
  obtain ⟨_, _, hoff⟩ := feedback_switch_properties hδ hZ hZlower hT
  have hpost (t : ℝ) (ht : T + 1 / 2 ≤ t) : HasDerivAt Y (g (Y t) - 4) t := by
    simpa only [hoff t ht, sub_eq_add_neg] using hY t
  have hTS : T ≤ T + 1 / 2 := le_add_of_nonneg_right (by norm_num)
  have hswitch := switch_interval_bounds hY hYhit (T + 1 / 2) ⟨hTS, le_rfl⟩
  have hupper := clock_le_210_after_switch hYd hpost
    (hswitch.2.trans (by norm_num : (2087 / 10 : ℝ) ≤ 210))
  have hband (t : ℝ) (ht : t ∈ Icc (T + 1 / 2) τ205) :
      Y t ∈ Icc (205 : ℝ) 210 := by
    refine ⟨?_, hupper t ht.1⟩
    rcases lt_or_eq_of_le ht.2 with hlt | rfl
    · exact (hbefore205 t ⟨hTS.trans ht.1, hlt⟩).le
    · exact hhit205.ge
  exact ⟨hup, fun t ht ↦ hpost t ht.1, hband⟩

/-- The supplied common clock determines an upward anchor whose integral times
are its gate passages. The first-hit hypothesis supplies the descending
range, and the passage provider supplies the gap, including both gate endpoints. -/
theorem exists_clock_gate_integral_identification_of_clock {δ : ℝ} {Y Z : ℝ → ℝ} {T τ205 : ℝ}
    (hδ : |δ| < 1 / 4) (hZ : ∀ t, HasDerivAt Z (fastLogCosh δ (Z t)) t)
    (hZlower : ∀ t, 0 ≤ t → 1 + t ≤ Z t) (hT : 1 ≤ T)
    (hY : ∀ t, HasDerivAt Y (g (Y t) + clockFeedback (Z T) (Z (T + 1 / 2)) (Z t)) t)
    (hYzero : Y 0 = 0) (hYhit : Y T = 415 / 2) (hτ205 : T + 1 / 2 < τ205) (hhit205 : Y τ205 = 205)
    (hbefore205 : ∀ t ∈ Ico T τ205, 205 < Y t) (speedConstant : ℝ) :
    ∃ upBaseTime : ℝ,
      let D := clockGatePassageData upBaseTime τ205 speedConstant
      ∀ y ∈ Icc (205 : ℝ) (2051 / 10),
        D.tPlus y ∈ Ioo 1 T ∧ D.tMinus y ∈ Ioc (T + 1 / 2) τ205 ∧
        Y (D.tPlus y) = y ∧ Y (D.tMinus y) = y ∧
        8 / 5 ≤ D.tMinus y - D.tPlus y := by
  obtain ⟨_, tPlus, tMinus, hpass⟩ :=
    gate_passage_times_of_clock hδ hZ hZlower hT hY hYzero hYhit hτ205 hhit205
  obtain ⟨hup, hdown, hband⟩ :=
    clock_gate_branch_properties hδ hZ hZlower hT hY hYzero hYhit hhit205 hbefore205
  have hanti := strictAntiOn_clock_downward hdown hband
  have hpassClosed (y : Icc (205 : ℝ) (2051 / 10)) :
      tPlus y ∈ Icc 1 T ∧ tMinus y ∈ Icc (T + 1 / 2) τ205 ∧
        Y (tPlus y) = y ∧ Y (tMinus y) = y := by
    obtain ⟨hp, hm, hhp, hhm, _⟩ := hpass y
    exact ⟨⟨hp.1.le, hp.2.le⟩, ⟨hm.1.le, hm.2⟩, hhp, hhm⟩
  have hbaseMinus : tMinus clockGateBase = τ205 :=
    hanti.injOn (hpassClosed clockGateBase).2.1 ⟨hτ205.le, le_rfl⟩
      ((hpassClosed clockGateBase).2.2.2.trans hhit205.symm)
  have heq := clock_gate_integral_times_eq hup hdown hband hpassClosed speedConstant
  rw [hbaseMinus] at heq
  refine ⟨tPlus clockGateBase, fun y hy ↦ ?_⟩
  obtain ⟨hp, hm, hhp, hhm, _, _, _, _, _, _, hgap⟩ := hpass ⟨y, hy⟩
  obtain ⟨hip, him⟩ := heq ⟨y, hy⟩
  exact ⟨hip ▸ hp, him ▸ hm, hip ▸ hhp, him ▸ hhm, hip ▸ him ▸ hgap⟩

/-- The common constructed clock has unique gate passages equal to the anchored
integral times. Its proved separation transfers to those times and their value
weights. The zero hit is retained separately from the additive integral anchor. -/
theorem exists_clock_gate_integral_identification {δ : ℝ} (hδ : |δ| < 1 / 4) (speedConstant : ℝ) :
    ∃ (Y Z : ℝ → ℝ) (T τ205 τ0 : ℝ)
      (tPlus tMinus : Icc (205 : ℝ) (2051 / 10) → ℝ),
      let D := clockGatePassageData (tPlus clockGateBase) (tMinus clockGateBase) speedConstant
      Y 0 = 0 ∧ Z 0 = 1 ∧
        (∀ t, HasDerivAt Z (fastLogCosh δ (Z t)) t) ∧
        (∀ t, HasDerivAt Y
          (g (Y t) + clockFeedback (Z T) (Z (T + 1 / 2)) (Z t)) t) ∧
        (∀ t, 0 ≤ t → 1 + t ≤ Z t) ∧
        T ∈ Ioc 1 (417 / 2) ∧ Y T = 415 / 2 ∧
        Z T ^ 2 < Z (T + 1 / 2) ^ 2 ∧
        T + 1 / 2 < τ205 ∧ τ205 < τ0 ∧ Y τ205 = 205 ∧ Y τ0 = 0 ∧
        D.terminalTime = τ205 + D.downTime 205 ∧
        (∀ y, tPlus y ∈ Ioo 1 T ∧ tMinus y ∈ Ioc (T + 1 / 2) τ205 ∧
          D.tPlus y = tPlus y ∧ D.tMinus y = tMinus y ∧
          Y (D.tPlus y) = y ∧ Y (D.tMinus y) = y ∧
          HasDerivAt Y (g y + 1) (D.tPlus y) ∧
          HasDerivAt Y (g y - 4) (D.tMinus y) ∧
          (∀ t ∈ Icc 1 T, Y t = y ↔ t = D.tPlus y) ∧
          (∀ t ∈ Icc (T + 1 / 2) τ205, Y t = y ↔ t = D.tMinus y) ∧
          8 / 5 ≤ D.tMinus y - D.tPlus y ∧ D.R y < 1 / 100) ∧
        (∀ y ∈ Ioo (205 : ℝ) (2051 / 10), D.wPlus y / D.wMinus y < 1 / 100) := by
  obtain ⟨Y, Z, T, τ205, τ0, hclock⟩ := exists_clock_upward_and_return hδ
  rcases hclock with ⟨hYzero, hZzero, hZ, hY, hZlower, hT, hYhit, _, _, _,
    horder, _, _, hτ205, hτ0, hhit205, hhit0, hbefore205, _⟩
  obtain ⟨upBaseTime, hgate⟩ :=
    exists_clock_gate_integral_identification_of_clock hδ hZ hZlower hT.1.le hY
      hYzero hYhit hτ205 hhit205 hbefore205 speedConstant
  obtain ⟨hup, hdown, hband⟩ :=
    clock_gate_branch_properties hδ hZ hZlower hT.1.le hY hYzero hYhit hhit205 hbefore205
  have hmono := strictMonoOn_clock_upward hup
  have hanti := strictAntiOn_clock_downward hdown hband
  let D := clockGatePassageData upBaseTime τ205 speedConstant
  let tPlus : Icc (205 : ℝ) (2051 / 10) → ℝ := fun y ↦ D.tPlus y
  let tMinus : Icc (205 : ℝ) (2051 / 10) → ℝ := fun y ↦ D.tMinus y
  have hbasePlus : tPlus clockGateBase = upBaseTime :=
    clockGatePassageData_tPlus_base upBaseTime τ205 speedConstant
  have hbaseMinus : tMinus clockGateBase = τ205 :=
    clockGatePassageData_tMinus_base upBaseTime τ205 speedConstant
  have hratio (y : Icc (205 : ℝ) (2051 / 10)) : D.R y < 1 / 100 :=
    linear_fast_weight_ratio_lt (g_mem_Icc_gate y.property) ((hgate y y.property).2.2.2.2)
  refine ⟨Y, Z, T, τ205, τ0, tPlus, tMinus, ?_⟩
  rw [hbasePlus, hbaseMinus]
  refine ⟨hYzero, hZzero, hZ, hY, hZlower, hT, hYhit, horder, hτ205, hτ0,
    hhit205, hhit0, clockGatePassageData_terminalTime upBaseTime τ205 speedConstant, ?_, ?_⟩
  · intro y
    obtain ⟨hp, hm, hhp, hhm, hgap⟩ := hgate y y.property
    have hpClosed : D.tPlus y ∈ Icc 1 T := ⟨hp.1.le, hp.2.le⟩
    have hmClosed : D.tMinus y ∈ Icc (T + 1 / 2) τ205 := ⟨hm.1.le, hm.2⟩
    exact ⟨hp, hm, rfl, rfl, hhp, hhm,
      (hup (D.tPlus y) hpClosed).congr_deriv (congrArg (fun u ↦ g u + 1) hhp),
      (hdown (D.tMinus y) hmClosed).congr_deriv (congrArg (fun u ↦ g u - 4) hhm),
      fun t ht ↦ ⟨fun hhit ↦ hmono.injOn ht hpClosed (hhit.trans hhp.symm), fun h ↦ h ▸ hhp⟩,
      fun t ht ↦ ⟨fun hhit ↦ hanti.injOn ht hmClosed (hhit.trans hhm.symm), fun h ↦ h ▸ hhm⟩,
      hgap, hratio y⟩
  · intro y hy
    have hreg : GateRegularity D (Ioo (205 : ℝ) (2051 / 10)) :=
      gateRegularity_clockPassageData 205 upBaseTime D.terminalTime speedConstant
    rw [← hreg.R_eq_weight_ratio hy]
    exact hratio ⟨y, hy.1.le, hy.2.le⟩

end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.ClockSwitch
