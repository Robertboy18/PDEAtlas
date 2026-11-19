/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.BumpMoments.NormalizedPulse.Transition

/-!
# The smooth feedback used in the returning clock

The first transition turns the feedback on away from the central interval.
A second transition, placed farther out, moves it to the value `-4`. Writing
this second step as a convex combination keeps the range bound immediate,
even before the two transition regions have been separated.
-/

@[expose] public section

noncomputable section

open PDE.Analysis.NormalizedPulse
open scoped ContDiff

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile

/-- An even feedback with an inner positive transition and an outer negative plateau. -/
def clockFeedback (a b z : ℝ) : ℝ :=
  (1 - transition ((z ^ 2 - a ^ 2) / (b ^ 2 - a ^ 2))) * transition (z ^ 2 - 1) -
    4 * transition ((z ^ 2 - a ^ 2) / (b ^ 2 - a ^ 2))

/-- The feedback is smooth as a function of the fast coordinate. -/
theorem contDiff_clockFeedback (a b : ℝ) : ContDiff ℝ ∞ (clockFeedback a b) := by
  have hinner : ContDiff ℝ ∞ (fun z : ℝ ↦ transition (z ^ 2 - 1)) :=
    contDiff_transition.comp ((contDiff_id.pow 2).sub contDiff_const)
  have houter : ContDiff ℝ ∞ (fun z : ℝ ↦ transition ((z ^ 2 - a ^ 2) / (b ^ 2 - a ^ 2))) :=
    contDiff_transition.comp (((contDiff_id.pow 2).sub contDiff_const).div_const (b ^ 2 - a ^ 2))
  exact ((contDiff_const.sub houter).mul hinner).sub (contDiff_const.mul houter)

/-- The two values being interpolated both lie in `[-4, 1]`. -/
theorem clockFeedback_mem_Icc (a b z : ℝ) :
    clockFeedback a b z ∈ Set.Icc (-4) 1 := by
  have hi0 := transition_nonneg (z ^ 2 - 1)
  have hi1 := transition_le_one (z ^ 2 - 1)
  have ho0 := transition_nonneg ((z ^ 2 - a ^ 2) / (b ^ 2 - a ^ 2))
  have ho1 := transition_le_one ((z ^ 2 - a ^ 2) / (b ^ 2 - a ^ 2))
  have hprod0 := mul_nonneg (sub_nonneg.mpr ho1) hi0
  have hprod1 := mul_le_mul_of_nonneg_left hi1 (sub_nonneg.mpr ho1)
  change -4 ≤ (1 - _) * _ - 4 * _ ∧ (1 - _) * _ - 4 * _ ≤ 1
  constructor <;> nlinarith

/-- Reflection of the fast coordinate leaves the feedback unchanged. -/
theorem clockFeedback_neg (a b z : ℝ) : clockFeedback a b (-z) = clockFeedback a b z := by
  simp only [clockFeedback, neg_sq]

/-- Before the outer transition, the feedback is exactly its inner transition. -/
theorem clockFeedback_of_sq_le {a b z : ℝ} (hab : a ^ 2 < b ^ 2) (hz : z ^ 2 ≤ a ^ 2) :
    clockFeedback a b z = transition (z ^ 2 - 1) := by
  have hout : transition ((z ^ 2 - a ^ 2) / (b ^ 2 - a ^ 2)) = 0 := transition_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hz) (sub_pos.mpr hab).le)
  simp only [clockFeedback, hout, sub_zero, one_mul, mul_zero]

/-- The central interval is unaffected when the outer transition lies beyond it. -/
theorem clockFeedback_eq_zero_of_abs_le_one {a b z : ℝ}
    (ha : 1 ≤ a ^ 2) (hab : a ^ 2 < b ^ 2) (hz : |z| ≤ 1) :
    clockFeedback a b z = 0 := by
  have hzsq := (sq_le_one_iff_abs_le_one z).2 hz
  rw [clockFeedback_of_sq_le hab (hzsq.trans ha)]
  exact transition_of_nonpos (sub_nonpos.mpr hzsq)

/-- After the outer transition, the feedback has its exact negative plateau value. -/
theorem clockFeedback_of_le_sq {a b z : ℝ} (hab : a ^ 2 < b ^ 2) (hz : b ^ 2 ≤ z ^ 2) :
    clockFeedback a b z = -4 := by
  have hout : transition ((z ^ 2 - a ^ 2) / (b ^ 2 - a ^ 2)) = 1 := by
    apply transition_of_one_le
    apply (le_div_iff₀ (sub_pos.mpr hab)).2
    nlinarith
  simp only [clockFeedback, hout, sub_self, zero_mul, mul_one, zero_sub]

end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
