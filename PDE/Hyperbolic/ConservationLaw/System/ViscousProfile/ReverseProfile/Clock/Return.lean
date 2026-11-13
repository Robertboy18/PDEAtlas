/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Clock.Switch.Existence
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Clock.Switch.Return

/-!
# A constructed scalar clock with upward and downward crossings

The fast coordinate starts at one and drives a smooth switch in the middle
coordinate. Its first upward crossing determines the switch thresholds. The
same global solution then crosses 205 and zero in that order on its return.
The only input is the size of the log-cosh parameter; trajectories, crossing
times and confinement bounds are all constructed.
-/

@[expose] public noncomputable section

open Set
open PDE.Analysis

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.ClockSwitch

open MiddleClock

/-- For each admissible fast parameter, a single global clock starts at zero,
rises to `415/2`, and returns through 205 to zero. The thresholds are attained
states of its fast coordinate, and each of the three crossings is transverse. -/
theorem exists_clock_upward_and_return {δ : ℝ} (hδ : |δ| < 1 / 4) :
    ∃ (Y Z : ℝ → ℝ) (T τ205 τ0 : ℝ),
      Y 0 = 0 ∧ Z 0 = 1 ∧
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
      HasDerivAt Y (-4) τ0 := by
  obtain ⟨P, Z, T, _, hZzero, _, hZ, hZlower, hT, _, hclock⟩ :=
    exists_clock_first_hit hδ (H := 415 / 2) (by norm_num)
  have hT0 : 0 ≤ T := by linarith [hT.1]
  have hS0 : 0 ≤ T + 1 / 2 := by linarith
  obtain ⟨hsq, _, _⟩ := feedback_switch_properties hδ hZ hZlower hT.1.le
  have hab : Z T < Z (T + 1 / 2) := by
    have ha := hZlower T hT0
    have hb := hZlower (T + 1 / 2) hS0
    nlinarith
  obtain ⟨Y, hYzero, hY, _, hhit, hbefore, hdT, hvT⟩ := hclock (Z (T + 1 / 2)) hab
  obtain ⟨τ205, τ0, horder, _, hoff, hband, hτ205, hτ0, hhit205,
    hhit0, hbefore205, hbefore0, hd205, hv205, hd0⟩ :=
    exists_switch_return hδ hZ hZlower hT.1.le hY hhit
  refine ⟨Y, Z, T, τ205, τ0, hYzero, hZzero, hZ, hY, hZlower, ?_, hhit,
    hbefore, hdT, hvT, horder, hoff, hband, hτ205, hτ0, hhit205, hhit0,
    hbefore205, hbefore0, hd205, hv205, hd0⟩
  norm_num at hT ⊢
  exact hT

end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.ClockSwitch
