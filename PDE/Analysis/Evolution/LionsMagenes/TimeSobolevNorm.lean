/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.LionsMagenes.TimeSobolev

/-!
# A data-only bound for the time Sobolev trace constant

The quantitative time Sobolev estimate is bounded by the sum of the two
Bochner norms, with a constant depending only on the interval length.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

/-- Bound the time Sobolev trace constant by the two data norms. -/
theorem timeSobolevBound_le_sum_norm {H : Type*}
    [NormedAddCommGroup H]
    {a b : ℝ} (hab : a < b)
    (f df : Lp H 2 (volume.restrict (Ioc a b))) :
    timeSobolevBound f df ≤ Real.sqrt (1 / (b - a) + 2) * (‖f‖ + ‖df‖) := by
  have hlen : 0 < b - a := sub_pos.mpr hab
  have hs : ‖f‖ ^ 2 ≤ (‖f‖ + ‖df‖) ^ 2 := by
    nlinarith [norm_nonneg f, norm_nonneg df]
  have hp : ‖f‖ * ‖df‖ ≤ (‖f‖ + ‖df‖) ^ 2 := by
    nlinarith [norm_nonneg f, norm_nonneg df, sq_nonneg (‖f‖ - ‖df‖)]
  calc
    _ ≤ Real.sqrt ((1 / (b - a) + 2) * (‖f‖ + ‖df‖) ^ 2) := by
      apply Real.sqrt_le_sqrt
      have hd := div_le_div_of_nonneg_right hs hlen.le
      simp only [div_eq_mul_inv, one_mul] at hd ⊢
      nlinarith
    _ = _ := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

end PDE.Analysis.Evolution
