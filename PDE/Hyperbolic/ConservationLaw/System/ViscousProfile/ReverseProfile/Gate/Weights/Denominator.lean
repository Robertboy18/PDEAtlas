/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Clock.Middle
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Cutoff

/-!
# The full lower clock denominator

The middle-clock bound at 210 and cutoff nonnegativity give a strict lower
bound on the full denominator throughout `[0,210]`.
-/

@[expose] public noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.MiddleClock

/-- The full lower denominator is strictly greater than `13/5` on `[0,210]`. -/
theorem thirteen_fifths_lt_lower_denominator {y : ℝ} (hy0 : 0 ≤ y) (hy210 : y ≤ 210) :
    13 / 5 < 4 - g y + 4 * cutoff y := by
  have hg := monotoneOn_g_nonneg hy0 (by norm_num : (0 : ℝ) ≤ 210) hy210
  linarith only [hg, g_210_lt, cutoff_nonneg y]

/-- Positivity holds with the entire cutoff contribution, including at both endpoints. -/
theorem lower_denominator_pos {y : ℝ} (hy0 : 0 ≤ y) (hy210 : y ≤ 210) :
    0 < 4 - g y + 4 * cutoff y :=
  lt_trans (by norm_num : (0 : ℝ) < 13 / 5) (thirteen_fifths_lt_lower_denominator hy0 hy210)

end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.MiddleClock
