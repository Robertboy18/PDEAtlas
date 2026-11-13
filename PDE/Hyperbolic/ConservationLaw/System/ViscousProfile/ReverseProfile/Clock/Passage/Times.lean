/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Clock.Return
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Clock.Switch.Monotonicity

/-!
# Separated gate passages of the constructed scalar clock

The common middle and fast trajectories come from `exists_clock_upward_and_return`.
The feedback still uses the attained states `Z T` and `Z (T + 1/2)` as thresholds.
Before the switch its outer transition vanishes, so the middle coordinate is
nonnegative and at most `415/2`. Its cutoff is consequently one there.

For every level in the closed gate `[205, 2051/10]`, the same middle trajectory
has an upward passage before `T` and a downward passage after `T + 1/2`.
The ascent to `415/2` takes at least one further time unit, and the descent from
`Y (T + 1/2) ≥ 411/2` takes at least `1/10`. Including the half-unit switch gives
separation at least `8/5`. Both passages have their transverse derivatives.

The level-indexed times are chosen witnesses.
-/

@[expose] public noncomputable section

open Set
open PDE.Analysis PDE.Analysis.NormalizedPulse

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.ClockSwitch

open MiddleClock

/-- The outer transition vanishes throughout the closed interval before `T`. -/
theorem feedback_eq_inner_before_switch {δ T : ℝ} {Z : ℝ → ℝ}
    (hδ : |δ| < 1 / 4) (hZ : ∀ t, HasDerivAt Z (fastLogCosh δ (Z t)) t)
    (hZlower : ∀ t, 0 ≤ t → 1 + t ≤ Z t) (hT : 1 ≤ T) :
    ∀ t ∈ Icc 0 T,
      clockFeedback (Z T) (Z (T + 1 / 2)) (Z t) = transition (Z t ^ 2 - 1) := fun _ ht ↦
  clockFeedback_of_sq_le (feedback_switch_properties hδ hZ hZlower hT).1
    ((strictMonoOn_fast_clock_sq hδ hZ hZlower).monotoneOn ht.1 (zero_le_one.trans hT) ht.2)

/-- The clock is confined before the switch, with cutoff one and speed at most
`12/5`. From time one through `T`, its derivative is exactly `g(Y) + 1`.
The lower bound is derived from the feedback. -/
theorem clock_bounds_before_switch {δ T : ℝ} {Y Z : ℝ → ℝ}
    (hδ : |δ| < 1 / 4) (hZ : ∀ t, HasDerivAt Z (fastLogCosh δ (Z t)) t)
    (hZlower : ∀ t, 0 ≤ t → 1 + t ≤ Z t) (hT : 1 ≤ T)
    (hY : ∀ t, HasDerivAt Y
      (g (Y t) + clockFeedback (Z T) (Z (T + 1 / 2)) (Z t)) t)
    (hYzero : Y 0 = 0) (hYhit : Y T = 415 / 2) :
    (∀ t ∈ Icc 0 T, Y t ∈ Icc 0 (415 / 2) ∧
      cutoff (-Y t) = 1 ∧ deriv Y t ≤ 12 / 5) ∧
    (∀ t ∈ Icc 1 T, HasDerivAt Y (g (Y t) + 1) t) := by
  have hT0 : 0 ≤ T := by linarith only [hT]
  have hYd : Differentiable ℝ Y := fun t ↦ (hY t).differentiableAt
  have hinner := feedback_eq_inner_before_switch hδ hZ hZlower hT
  have hmono : MonotoneOn Y (Icc 0 T) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 T) hYd.continuous.continuousOn
      hYd.differentiableOn fun t ht ↦ by
        rw [(hY t).deriv, hinner t (interior_subset ht)]
        exact add_nonneg (g_nonneg (Y t)) (transition_nonneg _)
  refine ⟨fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · have hy0 : 0 ≤ Y t := by
      simpa only [hYzero] using hmono ⟨le_rfl, hT0⟩ ht ht.1
    have hyH : Y t ≤ 415 / 2 := by
      simpa only [hYhit] using hmono ht ⟨hT0, le_rfl⟩ ht.2
    refine ⟨⟨hy0, hyH⟩, cutoff_of_le (by linarith only [hy0]), ?_⟩
    rw [(hY t).deriv]
    linarith only [monotoneOn_g_nonneg hy0 (by norm_num : (0 : ℝ) ≤ 210)
      (show Y t ≤ 210 by linarith only [hyH]), g_210_lt,
      (clockFeedback_mem_Icc (Z T) (Z (T + 1 / 2)) (Z t)).2]
  · have ht0 : 0 ≤ t := by linarith only [ht.1]
    have hone : transition (Z t ^ 2 - 1) = 1 :=
      transition_of_one_le (by nlinarith only [hZlower t ht0, ht.1, sq_nonneg (Z t - 2)])
    simpa only [hinner t ⟨ht0, ht.2⟩, hone] using hY t

/-- Any common clock with the constructed initial state, attained switch height,
and return to 205 has separated transverse passages through the entire closed gate.
The switch band and both travel-time lower bounds are consequences of its equations. -/
theorem gate_passage_times_of_clock {δ T τ205 : ℝ} {Y Z : ℝ → ℝ} (hδ : |δ| < 1 / 4)
    (hZ : ∀ t, HasDerivAt Z (fastLogCosh δ (Z t)) t) (hZlower : ∀ t, 0 ≤ t → 1 + t ≤ Z t)
    (hT : 1 ≤ T) (hY : ∀ t, HasDerivAt Y (g (Y t) + clockFeedback (Z T) (Z (T + 1 / 2)) (Z t)) t)
    (hYzero : Y 0 = 0) (hYhit : Y T = 415 / 2) (hτ205 : T + 1 / 2 < τ205) (hhit205 : Y τ205 = 205) :
    (∀ t ∈ Icc 0 T, Y t ∈ Icc 0 (415 / 2) ∧
      cutoff (-Y t) = 1 ∧ deriv Y t ≤ 12 / 5) ∧
    ∃ tPlus tMinus : Icc (205 : ℝ) (2051 / 10) → ℝ,
      ∀ y, tPlus y ∈ Ioo 1 T ∧ tMinus y ∈ Ioc (T + 1 / 2) τ205 ∧
        Y (tPlus y) = y ∧ Y (tMinus y) = y ∧
        HasDerivAt Y (g y + 1) (tPlus y) ∧ 1 ≤ g y + 1 ∧
        HasDerivAt Y (g y - 4) (tMinus y) ∧ g y - 4 < -(13 / 5) ∧
        1 ≤ T - tPlus y ∧ 1 / 10 ≤ tMinus y - (T + 1 / 2) ∧
        8 / 5 ≤ tMinus y - tPlus y := by
  have hT0 : 0 ≤ T := by linarith only [hT]
  have hYd : Differentiable ℝ Y := fun t ↦ (hY t).differentiableAt
  obtain ⟨hpre, hon⟩ := clock_bounds_before_switch hδ hZ hZlower hT hY hYzero hYhit
  have hmean (s t : ℝ) (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t) :
      Y t - Y s ≤ (12 / 5) * (t - s) := (convex_Icc 0 T).image_sub_le_mul_sub_of_deriv_le
      hYd.continuous.continuousOn hYd.differentiableOn
      (fun r hr ↦ (hpre r (interior_subset hr)).2.2) s hs t ht hst
  have hglobal_lower (t : ℝ) : -4 ≤ deriv Y t := by
    rw [(hY t).deriv]
    linarith only [g_nonneg (Y t), (clockFeedback_mem_Icc (Z T) (Z (T + 1 / 2)) (Z t)).1]
  have hSband := switch_interval_bounds hY hYhit (T + 1 / 2)
    ⟨by linarith, le_rfl⟩
  obtain ⟨_, _, hoff⟩ := feedback_switch_properties hδ hZ hZlower hT
  have hpoint (y : Icc (205 : ℝ) (2051 / 10)) : ∃ tPlus tMinus : ℝ,
        tPlus ∈ Ioo 1 T ∧ tMinus ∈ Ioc (T + 1 / 2) τ205 ∧ Y tPlus = y ∧ Y tMinus = y ∧
        HasDerivAt Y (g y + 1) tPlus ∧ 1 ≤ g y + 1 ∧
        HasDerivAt Y (g y - 4) tMinus ∧ g y - 4 < -(13 / 5) ∧
        1 ≤ T - tPlus ∧ 1 / 10 ≤ tMinus - (T + 1 / 2) ∧
        8 / 5 ≤ tMinus - tPlus := by
    obtain ⟨tPlus, htPlus, hhitPlus⟩ := intermediate_value_Icc hT0 hYd.continuous.continuousOn
      (show (y : ℝ) ∈ Icc (Y 0) (Y T) by
        rw [hYzero, hYhit]
        constructor <;> linarith only [y.property.1, y.property.2])
    have hfromzero := hmean 0 tPlus ⟨le_rfl, hT0⟩ htPlus htPlus.1
    rw [hYzero, hhitPlus] at hfromzero
    have htPlusOne : 1 < tPlus := by
      linarith only [hfromzero, y.property.1]
    -- The slow ascent still has at least 12/5 units of height left to gain.
    have htoT := hmean tPlus T htPlus ⟨hT0, le_rfl⟩ htPlus.2
    rw [hYhit, hhitPlus] at htoT
    have hascent : 1 ≤ T - tPlus := by
      linarith only [htoT, y.property.2]
    have hdPlus : HasDerivAt Y (g y + 1) tPlus := by
      simpa only [hhitPlus] using hon tPlus ⟨htPlusOne.le, htPlus.2⟩
    obtain ⟨tMinus, htMinus, hhitMinus⟩ := intermediate_value_Icc' hτ205.le
      hYd.continuous.continuousOn
      (show (y : ℝ) ∈ Icc (Y τ205) (Y (T + 1 / 2)) by
        rw [hhit205]
        exact ⟨y.property.1, by linarith only [hSband.1, y.property.2]⟩)
    -- The global lower speed bound controls the descent after the exact switch endpoint.
    have hfall := mul_sub_le_image_sub_of_le_deriv hYd hglobal_lower htMinus.1
    rw [hhitMinus] at hfall
    have hdescent : 1 / 10 ≤ tMinus - (T + 1 / 2) := by
      linarith only [hfall, hSband.1, y.property.2]
    have hdMinus : HasDerivAt Y (g y - 4) tMinus := by
      simpa only [hhitMinus, hoff tMinus htMinus.1, sub_eq_add_neg] using hY tMinus
    have hg := monotoneOn_g_nonneg (show 0 ≤ (y : ℝ) by linarith only [y.property.1])
      (by norm_num : (0 : ℝ) ≤ 210) (show (y : ℝ) ≤ 210 by linarith only [y.property.2])
    exact ⟨tPlus, tMinus, ⟨htPlusOne, by linarith only [hascent]⟩,
      ⟨by linarith only [hdescent], htMinus.2⟩, hhitPlus, hhitMinus, hdPlus,
      by linarith only [g_nonneg (y : ℝ)], hdMinus, by linarith only [hg, g_210_lt], hascent,
      hdescent, by linarith only [hascent, hdescent]⟩
  choose tPlus tMinus hpass using hpoint
  exact ⟨hpre, tPlus, tMinus, hpass⟩

/-- The clock construction, with all its conclusions retained, admits
level-indexed upward and downward gate passages separated by at least `8/5`.
The only hypothesis is admissibility of the fast parameter. -/
theorem exists_clock_gate_passage_times {δ : ℝ} (hδ : |δ| < 1 / 4) :
    ∃ (Y Z : ℝ → ℝ) (T τ205 τ0 : ℝ),
      (Y 0 = 0 ∧ Z 0 = 1 ∧
        (∀ t, HasDerivAt Z (fastLogCosh δ (Z t)) t) ∧
        (∀ t, HasDerivAt Y
          (g (Y t) + clockFeedback (Z T) (Z (T + 1 / 2)) (Z t)) t) ∧
        (∀ t, 0 ≤ t → 1 + t ≤ Z t) ∧
        T ∈ Ioc 1 (417 / 2) ∧ Y T = 415 / 2 ∧
        (∀ t ∈ Ico 0 T, Y t < 415 / 2) ∧
        HasDerivAt Y (g (415 / 2) + 1) T ∧ 1 ≤ g (415 / 2) + 1 ∧
        Z T ^ 2 < Z (T + 1 / 2) ^ 2 ∧
        (∀ t ≥ T + 1 / 2, clockFeedback (Z T) (Z (T + 1 / 2)) (Z t) = -4) ∧
        (∀ t ∈ Icc T (T + 1 / 2), 411 / 2 ≤ Y t ∧ Y t ≤ 2087 / 10) ∧
        T + 1 / 2 < τ205 ∧ τ205 < τ0 ∧ Y τ205 = 205 ∧ Y τ0 = 0 ∧
        (∀ t ∈ Ico T τ205, 205 < Y t) ∧
        (∀ t ∈ Ico T τ0, 0 < Y t) ∧
        HasDerivAt Y (g 205 - 4) τ205 ∧ g 205 - 4 < -(13 / 5) ∧
        HasDerivAt Y (-4) τ0) ∧
      (∀ t ∈ Icc 0 T, Y t ∈ Icc 0 (415 / 2) ∧
        cutoff (-Y t) = 1 ∧ deriv Y t ≤ 12 / 5) ∧
      ∃ tPlus tMinus : Icc (205 : ℝ) (2051 / 10) → ℝ,
        ∀ y, tPlus y ∈ Ioo 1 T ∧ tMinus y ∈ Ioc (T + 1 / 2) τ205 ∧
          Y (tPlus y) = y ∧ Y (tMinus y) = y ∧
          HasDerivAt Y (g y + 1) (tPlus y) ∧ 1 ≤ g y + 1 ∧
          HasDerivAt Y (g y - 4) (tMinus y) ∧ g y - 4 < -(13 / 5) ∧
          1 ≤ T - tPlus y ∧ 1 / 10 ≤ tMinus y - (T + 1 / 2) ∧
          8 / 5 ≤ tMinus y - tPlus y := by
  obtain ⟨Y, Z, T, τ205, τ0, hclock⟩ := exists_clock_upward_and_return hδ
  refine ⟨Y, Z, T, τ205, τ0, hclock, ?_⟩
  rcases hclock with ⟨hYzero, _, hZ, hY, hZlower, hT, hYhit, _, _, _, _, _, _, hτ205, _, hhit205, _⟩
  exact gate_passage_times_of_clock hδ hZ hZlower hT.1.le hY hYzero hYhit hτ205 hhit205

end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.ClockSwitch
