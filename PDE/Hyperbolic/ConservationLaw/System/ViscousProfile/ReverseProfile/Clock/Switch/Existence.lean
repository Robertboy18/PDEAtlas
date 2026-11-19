/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Clock.UpwardCrossing

/-!
# Existence of the switched scalar clock

The fast coordinate and preliminary middle coordinate are constructed by the
upward-clock theorem. For every outer threshold beyond the attained fast state,
the switched middle equation has a global solution starting at zero. Uniqueness
identifies it with the preliminary solution through the upward hit, including
the endpoint. The same time is therefore its first upward hit, with the same
positive crossing speed.

The return barriers are proved in `Clock.Switch.Return`.
-/

@[expose] public noncomputable section

open Set
open PDE.Analysis PDE.Analysis.NormalizedPulse

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.ClockSwitch

open MiddleClock

private theorem lipschitzWith_clockField (a b z : ℝ) :
    LipschitzWith (201 / 4000) (fun y : ℝ ↦ g y + clockFeedback a b z) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  simpa only [dist_add_right] using MiddleClock.lipschitzWith_g.dist_le_mul x y

/-- The switched equation has a global solution through any prescribed state.
Continuity of the fast path suffices because the forcing is independent of the middle state. -/
theorem exists_clock {Z : ℝ → ℝ} (hZ : Continuous Z) (a b t₀ y₀ : ℝ) :
    ∃ Y : ℝ → ℝ, Y t₀ = y₀ ∧ ∀ t, HasDerivAt Y (g (Y t) + clockFeedback a b (Z t)) t := by
  have hf : Continuous (fun t ↦ clockFeedback a b (Z t)) :=
    (contDiff_clockFeedback a b).continuous.comp hZ
  exact PDE.Analysis.Evolution.exists_eq_hasDerivAt_of_lipschitz
    ((contDiff_g.continuous.comp continuous_snd).add (hf.comp continuous_fst))
    (fun t ↦ lipschitzWith_clockField a b (Z t)) t₀ y₀

/-- Starting the switched clock at zero preserves a preliminary clock until the
outer transition begins. Agreement includes both endpoints of the comparison interval. -/
theorem exists_clock_eqOn_preliminary {δ : ℝ} {P Z : ℝ → ℝ} (hδ : |δ| < 1 / 4) (hPzero : P 0 = 0)
    (hZzero : Z 0 = 1) (hP : ∀ t, HasDerivAt P (g (P t) + transition (Z t ^ 2 - 1)) t)
    (hZ : ∀ t, HasDerivAt Z (fastLogCosh δ (Z t)) t) (hmono : Monotone P) {T b : ℝ} (hT : 0 ≤ T)
    (hb : Z T ^ 2 < b ^ 2) :
    ∃ Y : ℝ → ℝ, Y 0 = 0 ∧ (∀ t, HasDerivAt Y (g (Y t) + clockFeedback (Z T) b (Z t)) t) ∧
      EqOn Y P (Icc 0 T) := by
  have hPd : Differentiable ℝ P := fun t ↦ (hP t).differentiableAt
  have hZd : Differentiable ℝ Z := fun t ↦ (hZ t).differentiableAt
  have hPfull (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivAt P (g (P t) + clockFeedback (Z T) b (Z t)) t := by
    have hnonneg : 0 ≤ P t := by simpa only [hPzero] using hmono ht.1
    have hcut : cutoff (-P t) = 1 := cutoff_of_le (by linarith)
    simpa only [hcut, one_mul] using
      UpwardClock.hasDerivAt_clock_before_outer_transition hδ hPzero hZzero hP hZ hT hb ht
  obtain ⟨Y, hYzero, hY⟩ := exists_clock hZd.continuous (Z T) b 0 0
  have hYd : Differentiable ℝ Y := fun t ↦ (hY t).differentiableAt
  refine ⟨Y, hYzero, hY, ?_⟩
  exact ODE_solution_unique (v := fun t y ↦ g y + clockFeedback (Z T) b (Z t))
    (fun t ↦ lipschitzWith_clockField (Z T) b (Z t))
    hYd.continuous.continuousOn (fun t _ ↦ (hY t).hasDerivWithinAt) hPd.continuous.continuousOn
    (fun t ht ↦ (hPfull t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt) (hYzero.trans hPzero.symm)

/-- For every `H > 2`, the middle and fast clocks start at `(0, 1)`
and reach the middle level `H` for the first time in `(1, H + 1]`.
The preliminary trajectory, fast trajectory and hit time are chosen before the outer
threshold `b`; every `b > Z T` gives a global switched solution with the same upward hit. -/
theorem exists_clock_first_hit {δ H : ℝ} (hδ : |δ| < 1 / 4) (hH : 2 < H) :
    ∃ (P Z : ℝ → ℝ) (T : ℝ), P 0 = 0 ∧ Z 0 = 1 ∧
      (∀ t, HasDerivAt P (g (P t) + transition (Z t ^ 2 - 1)) t) ∧
      (∀ t, HasDerivAt Z (fastLogCosh δ (Z t)) t) ∧
      (∀ t, 0 ≤ t → 1 + t ≤ Z t) ∧ T ∈ Ioc 1 (H + 1) ∧ P T = H ∧
      ∀ b, Z T < b → ∃ Y : ℝ → ℝ, Y 0 = 0 ∧
        (∀ t, HasDerivAt Y (g (Y t) + clockFeedback (Z T) b (Z t)) t) ∧
        EqOn Y P (Icc 0 T) ∧ Y T = H ∧
        (∀ t ∈ Ico 0 T, Y t < H) ∧
        HasDerivAt Y (g H + 1) T ∧ 1 ≤ g H + 1 := by
  obtain ⟨P, Z, T, hPzero, hZzero, hP, hZ, hZlower, hmono, hT,
    hhit, hbefore, _, hspeed⟩ := UpwardClock.exists_preliminary_clock_first_hit hδ hH
  refine ⟨P, Z, T, hPzero, hZzero, hP, hZ, hZlower, hT, hhit, fun b hb ↦ ?_⟩
  have hTzero : 0 ≤ T := by linarith [hT.1]
  have hZT : 2 < Z T := by linarith [hZlower T hTzero, hT.1]
  have hsum : 0 < b + Z T := by linarith
  have hsq : Z T ^ 2 < b ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hb) hsum]
  obtain ⟨Y, hYzero, hY, heq⟩ :=
    exists_clock_eqOn_preliminary hδ hPzero hZzero hP hZ hmono hTzero hsq
  have hYhit : Y T = H := (heq ⟨hTzero, le_rfl⟩).trans hhit
  have hon : clockFeedback (Z T) b (Z T) = 1 := by
    rw [clockFeedback_of_sq_le hsq le_rfl]
    apply transition_of_one_le
    nlinarith [sq_nonneg (Z T - 2)]
  refine ⟨Y, hYzero, hY, heq, hYhit, ?_, ?_, hspeed⟩
  · intro t ht
    rw [heq ⟨ht.1, ht.2.le⟩]
    exact hbefore t ht
  · simpa only [hYhit, hon] using hY T

end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.ClockSwitch
