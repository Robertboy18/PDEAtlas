/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Clock.LowerReturn
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Clock.Passage.Integrals

import CAS.ExactTactic

/-!
# The integral time of the prescribed lower return

For the prescribed lower equation `X' = g(X) - 4 - 4 * cutoff(X)`, the full
remaining-time primitive has derivative minus one along the trajectory.
Consequently `t + downTime (X t)` is constant from the descending 205 hit to
the newly constructed zero. The additive anchor in `clockGatePassageData`
is therefore the terminal time of this prescribed trajectory.

The same trajectory is strictly decreasing and maps its closed descent interval
onto `[0, 205]`. Its unique passage through each lower level is the
integral-defined `tMinus`.
-/

@[expose] public noncomputable section

open MeasureTheory PDE.Analysis Set

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

open ClockSwitch Gate.Weights MiddleClock

/-- Along any supplied solution of the lower equation in `[0,205]`,
elapsed time plus the full remaining-time primitive is constant. -/
theorem clock_downTime_comp_add_eq {X : ℝ → ℝ} {A B : ℝ}
    (hX : ∀ t ∈ Icc A B, HasDerivAt X (lowerClockField (X t)) t)
    (hband : ∀ t ∈ Icc A B, X t ∈ Icc (0 : ℝ) 205) (upBaseTime downBaseTime speedConstant : ℝ) :
    let D := clockGatePassageData upBaseTime downBaseTime speedConstant
    ∀ t ∈ Icc A B, D.downTime (X t) + t = D.downTime (X A) + A := by
  let D := clockGatePassageData upBaseTime downBaseTime speedConstant
  change ∀ t ∈ Icc A B, D.downTime (X t) + t = D.downTime (X A) + A
  have hd : Continuous D.downSpeed := (continuous_const.sub contDiff_g.continuous).add
      (continuous_const.mul contDiff_cutoff.continuous)
  have hflow (t : ℝ) (ht : t ∈ Icc A B) : HasDerivAt X (D.downSpeed (X t) * (-1)) t := by
    apply (hX t ht).congr_deriv
    change g (X t) - 4 - 4 * cutoff (X t) = (4 - g (X t) + 4 * cutoff (X t)) * (-1)
    generalize g (X t) = r
    generalize cutoff (X t) = c
    cas
  have hne : ∀ t ∈ Icc A B, ∀ v ∈ uIcc (0 : ℝ) (X t), D.downSpeed v ≠ 0 := by
    intro t ht v hv
    rw [uIcc_of_le (hband t ht).1] at hv
    exact ne_of_gt (MiddleClock.lower_denominator_pos hv.1
      (hv.2.trans ((hband t ht).2.trans (by cas : (205 : ℝ) ≤ 210))))
  simpa only [PassageData.downTime, neg_one_mul, sub_neg_eq_add] using
    PDE.Analysis.integral_reciprocal_comp_sub_eq hd hflow hne

/-- Identify the return and every lower passage of the same supplied trajectory.
The range follows from its endpoint values and strict decrease; the integral
identity follows from its equation. These inputs are outputs of the prescribed
return constructor in the corollaries below. -/
theorem prescribed_lower_return_integral_identification {X : ℝ → ℝ} {A B : ℝ} (hab : A ≤ B)
    (hX : ∀ t ∈ Icc A B, HasDerivAt X (lowerClockField (X t)) t) (hstart : X A = 205)
    (hzero : X B = 0) (hanti : StrictAntiOn X (Icc A B)) (upBaseTime speedConstant : ℝ) :
    let D := clockGatePassageData upBaseTime A speedConstant
    D.terminalTime = B ∧ B = A + D.downTime 205 ∧
      X '' Icc A B = Icc (0 : ℝ) 205 ∧
      (∀ t ∈ Icc A B, D.downTime (X t) = B - t ∧ D.tMinus (X t) = t) ∧
      (∀ y ∈ Icc (0 : ℝ) 205, D.tMinus y ∈ Icc A B ∧ X (D.tMinus y) = y ∧
        ∀ t ∈ Icc A B, X t = y ↔ t = D.tMinus y) := by
  let D := clockGatePassageData upBaseTime A speedConstant
  have hcont : ContinuousOn X (Icc A B) := fun t ht ↦ (hX t ht).continuousAt.continuousWithinAt
  have hrange : X '' Icc A B = Icc (0 : ℝ) 205 := by
    simpa only [hstart, hzero] using hcont.image_Icc_of_antitoneOn hab hanti.antitoneOn
  have hband (t : ℝ) (ht : t ∈ Icc A B) : X t ∈ Icc (0 : ℝ) 205 := by
    rw [← hrange]
    exact ⟨t, ht, rfl⟩
  have hclock := clock_downTime_comp_add_eq hX hband upBaseTime A speedConstant
  have hlast := hclock B ⟨hab, le_rfl⟩
  have hDzero : D.downTime 0 = 0 := by
    simp only [PassageData.downTime, intervalIntegral.integral_same]
  rw [hstart, hzero, hDzero, zero_add] at hlast
  have htime : B = A + D.downTime 205 := hlast.trans (add_comm _ _)
  have hterminal : D.terminalTime = B :=
    (clockGatePassageData_terminalTime upBaseTime A speedConstant).trans htime.symm
  have halong (t : ℝ) (ht : t ∈ Icc A B) : D.downTime (X t) = B - t ∧ D.tMinus (X t) = t := by
    have hc := hclock t ht
    rw [hstart] at hc
    have hremaining : D.downTime (X t) = B - t := by linarith only [hc, hlast]
    refine ⟨hremaining, ?_⟩
    change D.terminalTime - D.downTime (X t) = t
    rw [hterminal, hremaining]
    linarith
  refine ⟨hterminal, htime, hrange, halong, fun y hy ↦ ?_⟩
  have hyimage : y ∈ X '' Icc A B := by rw [hrange]; exact hy
  obtain ⟨t, ht, hhit⟩ := hyimage
  have hty : D.tMinus y = t := by
    rw [← hhit]
    exact (halong t ht).2
  refine ⟨?_, ?_, ?_⟩
  · rw [hty]
    exact ht
  · rw [hty]
    exact hhit
  · intro s hs
    constructor
    · exact fun hhit' ↦ ((halong s hs).2).symm.trans (congrArg D.tMinus hhit')
    · intro htime'
      rw [htime', hty]
      exact hhit

/-- Extend the supplied common clock by its prescribed return and identify
that new return with the full integral anchor. -/
theorem exists_prescribed_clock_lower_return_integral {δ : ℝ} {Y Z : ℝ → ℝ} {T τ205 : ℝ}
    (hδ : |δ| < 1 / 4) (hZ : ∀ t, HasDerivAt Z (fastLogCosh δ (Z t)) t)
    (hZlower : ∀ t, 0 ≤ t → 1 + t ≤ Z t) (hT : 1 ≤ T) (hYzero : Y 0 = 0)
    (hY : ∀ t, HasDerivAt Y (g (Y t) + clockFeedback (Z T) (Z (T + 1 / 2)) (Z t)) t)
    (hτ205 : T + 1 / 2 < τ205) (hhit205 : Y τ205 = 205) (hbefore205 : ∀ t ∈ Ico T τ205, 205 < Y t)
    (upBaseTime speedConstant : ℝ) :
    ∃ (X : ℝ → ℝ) (τ0 : ℝ),
      let D := clockGatePassageData upBaseTime τ205 speedConstant
      X 0 = 0 ∧
        (∀ t, HasDerivAt X
          (prescribedClockField (Z T) (Z (T + 1 / 2)) (Z t) (X t)) t) ∧
        EqOn X Y (Icc 0 τ205) ∧
        (∀ t ≥ T + 1 / 2, HasDerivAt X (lowerClockField (X t)) t) ∧
        τ0 ∈ Ioc τ205 (τ205 + 205 / 2) ∧ X τ205 = 205 ∧ X τ0 = 0 ∧
        (∀ t ∈ Ico T τ0, 0 < X t) ∧ StrictAntiOn X (Icc τ205 τ0) ∧
        HasDerivAt X (-8) τ0 ∧
        D.terminalTime = τ0 ∧ τ0 = τ205 + D.downTime 205 ∧
        X '' Icc τ205 τ0 = Icc (0 : ℝ) 205 ∧
        (∀ t ∈ Icc τ205 τ0, D.downTime (X t) = τ0 - t ∧ D.tMinus (X t) = t) ∧
        (∀ y ∈ Icc (0 : ℝ) 205, D.tMinus y ∈ Icc τ205 τ0 ∧ X (D.tMinus y) = y ∧
          ∀ t ∈ Icc τ205 τ0, X t = y ↔ t = D.tMinus y) := by
  obtain ⟨X, τ0, hXzero, hX, heq, hpost, hτ0, hzero, hpositive, hanti, hd0⟩ :=
    exists_prescribed_clock_lower_return hδ hZ hZlower hT hYzero hY hτ205 hhit205 hbefore205
  have hτ205zero : 0 ≤ τ205 := by linarith only [hT, hτ205]
  have hX205 : X τ205 = 205 := (heq ⟨hτ205zero, le_rfl⟩).trans hhit205
  have hident := prescribed_lower_return_integral_identification hτ0.1.le
    (fun t ht ↦ hpost t (hτ205.le.trans ht.1)) hX205 hzero hanti upBaseTime speedConstant
  exact ⟨X, τ0, hXzero, hX, heq, hpost, hτ0, hX205, hzero, hpositive, hanti, hd0, hident⟩

/-- A linear-fast prescribed clock with its lower integral return.
All trajectory, hit, range, and strict-decrease facts come from the
constructor. The arbitrary upward anchor and speed constant do not affect the
lower integral or the new zero time. -/
theorem exists_linear_fast_prescribed_clock_integral (upBaseTime speedConstant : ℝ) :
    ∃ (X Z : ℝ → ℝ) (T τ205 τ0 : ℝ),
      let D := clockGatePassageData upBaseTime τ205 speedConstant
      X 0 = 0 ∧ Z 0 = 1 ∧
        (∀ t, HasDerivAt Z (2 * Z t) t) ∧
        (∀ t, 0 ≤ t → 1 + t ≤ Z t) ∧ T ∈ Ioc 1 (417 / 2) ∧
        Z T ^ 2 < Z (T + 1 / 2) ^ 2 ∧
        (∀ t, HasDerivAt X
          (prescribedClockField (Z T) (Z (T + 1 / 2)) (Z t) (X t)) t) ∧
        X T = 415 / 2 ∧ (∀ t ∈ Ico 0 T, X t < 415 / 2) ∧
        T + 1 / 2 < τ205 ∧ X τ205 = 205 ∧
        (∀ t ∈ Ico T τ205, 205 < X t) ∧
        (∀ t ≥ T + 1 / 2, HasDerivAt X (lowerClockField (X t)) t) ∧
        τ0 ∈ Ioc τ205 (τ205 + 205 / 2) ∧ X τ0 = 0 ∧
        (∀ t ∈ Ico T τ0, 0 < X t) ∧ StrictAntiOn X (Icc τ205 τ0) ∧
        HasDerivAt X (-8) τ0 ∧
        D.terminalTime = τ0 ∧ τ0 = τ205 + D.downTime 205 ∧
        X '' Icc τ205 τ0 = Icc (0 : ℝ) 205 ∧
        (∀ t ∈ Icc τ205 τ0, D.downTime (X t) = τ0 - t ∧ D.tMinus (X t) = t) ∧
        (∀ y ∈ Icc (0 : ℝ) 205, D.tMinus y ∈ Icc τ205 τ0 ∧ X (D.tMinus y) = y ∧
          ∀ t ∈ Icc τ205 τ0, X t = y ↔ t = D.tMinus y) := by
  obtain ⟨X, Z, T, τ205, τ0, hXzero, hZzero, hZ, hZlower, hT, hsq, hX,
    hXT, hbeforeT, hτ205, hX205, hbefore205, hpost, hτ0, hzero, hpositive, hanti, hd0⟩ :=
    exists_linear_fast_prescribed_clock
  have hident := prescribed_lower_return_integral_identification hτ0.1.le
    (fun t ht ↦ hpost t (hτ205.le.trans ht.1)) hX205 hzero hanti upBaseTime speedConstant
  exact ⟨X, Z, T, τ205, τ0, hXzero, hZzero, hZ, hZlower, hT, hsq, hX,
    hXT, hbeforeT, hτ205, hX205, hbefore205, hpost, hτ0, hzero, hpositive, hanti, hd0, hident⟩

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
