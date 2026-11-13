/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Nonautonomous.Lipschitz
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Clock.Middle
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.FastLogCosh
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Feedback
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Cutoff

/-!
# Finite upward crossing of the preliminary clock

The fast coordinate solves the log-cosh equation from one. The middle
coordinate solves its clock equation with the inner feedback, from zero.
Global scalar Lipschitz estimates construct both curves successively. A moving
barrier gives `Z(t) ≥ 1 + t` for nonnegative time, so the inner feedback is one
from time one onward. The middle coordinate consequently reaches every level
`H > 2` for the first time in `(1, H + 1]`, with crossing speed at least one.

The final lemma identifies the same middle equation with the cutoff and
feedback before the outer transition starts at `Z(T)`.
-/

@[expose] public noncomputable section

open Set
open PDE.Analysis PDE.Analysis.NormalizedPulse

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.UpwardClock

open MiddleClock

private theorem fast_zero (δ : ℝ) : fastLogCosh δ 0 = 0 := by
  simp [fastLogCosh]

private theorem lipschitzWith_fast {δ : ℝ} (hδ : |δ| < 1 / 4) :
    LipschitzWith (9 / 4) (fastLogCosh δ) := by
  refine lipschitzWith_of_nnnorm_deriv_le
    (fun s ↦ (hasDerivAt_fastLogCosh δ s).differentiableAt) fun s ↦ ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
  change |deriv (fastLogCosh δ) s| ≤ (9 : ℝ) / 4
  exact abs_le.mpr ⟨by linarith [seven_fourths_lt_deriv_fastLogCosh hδ s],
    (deriv_fastLogCosh_lt_nine_fourths hδ s).le⟩

private theorem mul_le_fast {δ s : ℝ} (hδ : |δ| < 1 / 4) (hs : 0 ≤ s) :
    (7 / 4 : ℝ) * s ≤ fastLogCosh δ s := by
  simpa only [fast_zero, sub_zero] using mul_sub_le_image_sub_of_le_deriv
    (fun x ↦ (hasDerivAt_fastLogCosh δ x).differentiableAt)
    (fun x ↦ (seven_fourths_lt_deriv_fastLogCosh hδ x).le) (x := 0) (y := s) hs

private theorem exists_preliminary_clock {δ : ℝ} (hδ : |δ| < 1 / 4) :
    ∃ Y Z : ℝ → ℝ, Y 0 = 0 ∧ Z 0 = 1 ∧ (∀ t, HasDerivAt Y (g (Y t) + transition (Z t ^ 2 - 1)) t) ∧
      ∀ t, HasDerivAt Z (fastLogCosh δ (Z t)) t := by
  obtain ⟨Z, hZzero, hZ⟩ := PDE.Analysis.Evolution.exists_eq_hasDerivAt_of_lipschitz
      (F := fun (_ : ℝ) z ↦ fastLogCosh δ z)
      ((contDiff_fastLogCosh δ).continuous.comp continuous_snd) (fun _ ↦ lipschitzWith_fast hδ) 0 1
  have hZd : Differentiable ℝ Z := fun t ↦ (hZ t).differentiableAt
  let forcing : ℝ → ℝ := fun t ↦ transition (Z t ^ 2 - 1)
  have hforcing : Continuous forcing :=
    contDiff_transition.continuous.comp ((hZd.continuous.pow 2).sub continuous_const)
  have hLip (t : ℝ) : LipschitzWith (201 / 4000) (fun y ↦ g y + forcing t) :=
    LipschitzWith.of_dist_le_mul fun x y ↦ by
      simpa only [dist_add_right] using lipschitzWith_g.dist_le_mul x y
  obtain ⟨Y, hYzero, hY⟩ := PDE.Analysis.Evolution.exists_eq_hasDerivAt_of_lipschitz
      (F := fun t y ↦ g y + forcing t) ((contDiff_g.continuous.comp continuous_snd).add
        (hforcing.comp continuous_fst)) hLip 0 0
  exact ⟨Y, Z, hYzero, hZzero, hY, hZ⟩

private theorem one_add_le_fast_clock {δ : ℝ} {Z : ℝ → ℝ} (hδ : |δ| < 1 / 4) (hZzero : Z 0 = 1)
    (hZ : ∀ t, HasDerivAt Z (fastLogCosh δ (Z t)) t) {t : ℝ} (ht : 0 ≤ t) :
    1 + t ≤ Z t := by
  apply image_le_of_deriv_right_lt_deriv_boundary (f := fun s : ℝ ↦ 1 + s) (f' := fun _ ↦ 1)
    (B := Z) (B' := fun s ↦ fastLogCosh δ (Z s)) (a := 0) (b := t)
    (continuous_const.add continuous_id).continuousOn
    (fun s _ ↦ ((hasDerivAt_id s).const_add 1).hasDerivWithinAt)
    (by simp only [add_zero, hZzero, le_refl]) hZ
    (fun s hs heq ↦ by linarith [hs.1, mul_le_fast hδ (show 0 ≤ Z s by linarith [hs.1])])
    ⟨ht, le_rfl⟩

private theorem inner_feedback_eq_one {Z : ℝ → ℝ}
    (hZlower : ∀ t, 0 ≤ t → 1 + t ≤ Z t) {t : ℝ} (ht : 1 ≤ t) :
    transition (Z t ^ 2 - 1) = 1 :=
  transition_of_one_le (by nlinarith [sq_nonneg (Z t - 2), hZlower t (by linarith)])

private theorem monotone_clock {Y Z : ℝ → ℝ}
    (hY : ∀ t, HasDerivAt Y (g (Y t) + transition (Z t ^ 2 - 1)) t) :
    Monotone Y :=
  monotone_of_hasDerivAt_nonneg hY fun t ↦ add_nonneg (g_nonneg (Y t)) (transition_nonneg _)

private theorem clock_one_le_two {Y Z : ℝ → ℝ} (hYzero : Y 0 = 0)
    (hY : ∀ t, HasDerivAt Y (g (Y t) + transition (Z t ^ 2 - 1)) t) :
    Y 1 ≤ 2 := by
  have hYd : Differentiable ℝ Y := fun t ↦ (hY t).differentiableAt
  simpa only [mul_one] using image_le_of_deriv_right_lt_deriv_boundary
    (f := Y) (f' := fun t ↦ g (Y t) + transition (Z t ^ 2 - 1))
    (B := fun t : ℝ ↦ 2 * t) (B' := fun _ ↦ 2) (a := 0) (b := 1) hYd.continuous.continuousOn
    (fun t _ ↦ (hY t).hasDerivWithinAt)
    (by simp only [hYzero, mul_zero, le_refl])
    (fun t ↦ by simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul 2)
    (fun t ht heq ↦ by nlinarith [ht.2, g_le_mul (show 0 ≤ Y t by linarith [ht.1]),
      transition_le_one (Z t ^ 2 - 1)])
    (show (1 : ℝ) ∈ Icc 0 1 from ⟨by norm_num, le_rfl⟩)

private theorem clock_progress {Y Z : ℝ → ℝ}
    (hY : ∀ t, HasDerivAt Y (g (Y t) + transition (Z t ^ 2 - 1)) t)
    (hZlower : ∀ t, 0 ≤ t → 1 + t ≤ Z t)
    {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) : t - s ≤ Y t - Y s := by
  have hYd : Differentiable ℝ Y := fun r ↦ (hY r).differentiableAt
  have hbound (r : ℝ) (hr : r ∈ interior (Ici (1 : ℝ))) : 1 ≤ deriv Y r := by
    rw [(hY r).deriv, inner_feedback_eq_one hZlower (interior_subset hr)]
    linarith [g_nonneg (Y r)]
  simpa only [one_mul] using (convex_Ici (1 : ℝ)).mul_sub_le_image_sub_of_le_deriv
      hYd.continuous.continuousOn hYd.differentiableOn hbound s hs t (hs.trans hst) hst

private theorem exists_first_hit {Y Z : ℝ → ℝ} (hYzero : Y 0 = 0)
    (hY : ∀ t, HasDerivAt Y (g (Y t) + transition (Z t ^ 2 - 1)) t)
    (hZlower : ∀ t, 0 ≤ t → 1 + t ≤ Z t) {H : ℝ} (hH : 2 < H) :
    ∃ T ∈ Ioc 1 (H + 1), Y T = H ∧ (∀ t ∈ Ico 0 T, Y t < H) ∧ HasDerivAt Y (g H + 1) T ∧
      1 ≤ g H + 1 := by
  have hYd : Differentiable ℝ Y := fun t ↦ (hY t).differentiableAt
  have hmono := monotone_clock hY
  have hone := clock_one_le_two hYzero hY
  have hnonneg : 0 ≤ Y 1 := by
    simpa only [hYzero] using hmono (show (0 : ℝ) ≤ 1 by norm_num)
  have hprogress := clock_progress hY hZlower (s := 1) (t := H + 1)
    le_rfl (by linarith)
  obtain ⟨T, hT, hhit⟩ := intermediate_value_Icc
    (a := 1) (b := H + 1) (by linarith) hYd.continuous.continuousOn
    (show H ∈ Icc (Y 1) (Y (H + 1)) from ⟨by linarith, by linarith⟩)
  have hTlower : 1 < T := hT.1.lt_of_ne fun h ↦ by rw [← h] at hhit; linarith
  refine ⟨T, ⟨hTlower, hT.2⟩, hhit, fun t ht ↦ ?_,
    by simpa only [hhit, inner_feedback_eq_one hZlower hTlower.le] using hY T,
    by linarith [g_nonneg H]⟩
  by_cases htone : t ≤ 1
  · exact (hmono htone).trans_lt (hone.trans_lt hH)
  · have hprogress := clock_progress hY hZlower (s := t) (t := T) (not_le.mp htone).le ht.2.le
    rw [hhit] at hprogress
    linarith [ht.2]

/-- The preliminary clock reaches every level above two by time `H + 1`.
Both curves are constructed from the scalar laws; no solution or hit is an input. -/
theorem exists_preliminary_clock_first_hit {δ H : ℝ} (hδ : |δ| < 1 / 4) (hH : 2 < H) :
    ∃ (Y Z : ℝ → ℝ) (T : ℝ), Y 0 = 0 ∧ Z 0 = 1 ∧
      (∀ t, HasDerivAt Y (g (Y t) + transition (Z t ^ 2 - 1)) t) ∧
      (∀ t, HasDerivAt Z (fastLogCosh δ (Z t)) t) ∧
      (∀ t, 0 ≤ t → 1 + t ≤ Z t) ∧ Monotone Y ∧
      T ∈ Ioc 1 (H + 1) ∧ Y T = H ∧
      (∀ t ∈ Ico 0 T, Y t < H) ∧
      HasDerivAt Y (g H + 1) T ∧ 1 ≤ g H + 1 := by
  obtain ⟨Y, Z, hYzero, hZzero, hY, hZ⟩ := exists_preliminary_clock hδ
  have hZlower (t : ℝ) (ht : 0 ≤ t) : 1 + t ≤ Z t := one_add_le_fast_clock hδ hZzero hZ ht
  obtain ⟨T, hT, hhit, hbefore, hderiv, hspeed⟩ := exists_first_hit hYzero hY hZlower hH
  exact ⟨Y, Z, T, hYzero, hZzero, hY, hZ, hZlower, monotone_clock hY,
    hT, hhit, hbefore, hderiv, hspeed⟩

/-- Choosing the outer threshold to start at the attained fast state leaves the
preliminary middle equation unchanged through that hit, including its endpoint. -/
theorem hasDerivAt_clock_before_outer_transition {δ : ℝ} {Y Z : ℝ → ℝ}
    (hδ : |δ| < 1 / 4) (hYzero : Y 0 = 0) (hZzero : Z 0 = 1)
    (hY : ∀ t, HasDerivAt Y (g (Y t) + transition (Z t ^ 2 - 1)) t)
    (hZ : ∀ t, HasDerivAt Z (fastLogCosh δ (Z t)) t)
    {T b : ℝ} (hT : 0 ≤ T) (hb : Z T ^ 2 < b ^ 2) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivAt Y (g (Y t) + cutoff (-Y t) * clockFeedback (Z T) b (Z t)) t := by
  have hZlower (s : ℝ) (hs : 0 ≤ s) : 1 + s ≤ Z s := one_add_le_fast_clock hδ hZzero hZ hs
  have hZd : Differentiable ℝ Z := fun s ↦ (hZ s).differentiableAt
  have hZmono : MonotoneOn Z (Ici 0) := StrictMonoOn.monotoneOn <|
    strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ)) hZd.continuous.continuousOn fun s hs ↦ by
      have hs0 : (0 : ℝ) ≤ s := interior_subset hs
      rw [(hZ s).deriv]
      linarith [hZlower s hs0, mul_le_fast hδ (show 0 ≤ Z s by linarith [hZlower s hs0])]
  have hsquare : Z t ^ 2 ≤ Z T ^ 2 :=
    pow_le_pow_left₀ (by linarith [ht.1, hZlower t ht.1]) (hZmono ht.1 hT ht.2) 2
  have hy0 : 0 ≤ Y t := by simpa only [hYzero] using monotone_clock hY ht.1
  rw [cutoff_of_le (by linarith), one_mul, clockFeedback_of_sq_le hb hsquare]
  exact hY t

end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.UpwardClock
