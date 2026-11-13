/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Basic.Real.Basic
import CAS.ExactTactic

/-!
# A quadratic estimate for decaying polynomial profiles

Completing the square gives an explicit coefficient that dominates a linear
growth term and a positive constant. The result does not depend on a PDE.
-/

@[expose] public section

namespace PDE.Analysis

/-- A negative quadratic with this coefficient absorbs any linear term. -/
theorem quadratic_decay_nonpos {D R : ℝ} (hD : 0 < D) (hR : 0 < R) (K h : ℝ) :
    -(K ^ 2 / (4 * D * R ^ 2)) * h ^ 2 + K * h - D * R ^ 2 ≤ 0 := by
  have hden : 0 < 4 * D * R ^ 2 := by positivity
  have hid :
      -(K ^ 2 / (4 * D * R ^ 2)) * h ^ 2 + K * h - D * R ^ 2 =
        -((K * h - 2 * D * R ^ 2) ^ 2 / (4 * D * R ^ 2)) := by
    cas
  rw [hid]
  exact neg_nonpos.mpr (div_nonneg (sq_nonneg _) hden.le)

/-- Exponential decay absorbs the quadratic growth of a cubic bump. The
sum of the radial gap and squared distance need only have a positive lower
bound, so the estimate applies to both fixed and expanding radii. -/
theorem cubic_decay_nonpos {D R c δ K h z : ℝ}
    (hD : 0 < D) (hR : 0 < R) (hh : 0 ≤ h) (hradius : R ^ 2 ≤ h + z)
    (hdecay : c + (K + D) ^ 2 / (4 * D * R ^ 2) ≤ δ) :
    (c - δ) * h ^ 3 + K * h ^ 2 - D * h * z ≤ 0 := by
  have hcoefficient : c - δ ≤ -((K + D) ^ 2 / (4 * D * R ^ 2)) := by linarith
  calc
    _ ≤ -((K + D) ^ 2 / (4 * D * R ^ 2)) * h ^ 3 + K * h ^ 2 - D * h * z :=
      sub_le_sub
        (add_le_add (mul_le_mul_of_nonneg_right hcoefficient (pow_nonneg hh _)) le_rfl) le_rfl
    _ = h * (-((K + D) ^ 2 / (4 * D * R ^ 2)) * h ^ 2 +
        (K + D) * h - D * (h + z)) := by cas
    _ ≤ h * (-((K + D) ^ 2 / (4 * D * R ^ 2)) * h ^ 2 +
        (K + D) * h - D * R ^ 2) :=
      mul_le_mul_of_nonneg_left
        (sub_le_sub_left (mul_le_mul_of_nonneg_left hradius hD.le) _) hh
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hh (quadratic_decay_nonpos hD hR (K + D) h)

end PDE.Analysis
