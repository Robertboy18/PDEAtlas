/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Difference bounds from power growth of a derivative

The mean-value estimate on the interval between two inputs retains both the
constant and the power term in the derivative bound. No second derivative is
needed.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Power growth of the first derivative gives a two-point difference
estimate, including the constant part of the growth bound. -/
theorem norm_sub_le_of_deriv_power_growth
    {f df : ℝ → F} {C r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hd : ∀ z, HasDerivAt f (df z) z)
    (hbound : ∀ z, ‖df z‖ ≤ C * (1 + ‖z‖ ^ r)) (x y : ℝ) :
    ‖f x - f y‖ ≤ (C + C * (‖x‖ + ‖y‖) ^ r) * ‖x - y‖ := by
  have hb : ∀ z ∈ Metric.closedBall (0 : ℝ) (‖x‖ + ‖y‖),
      ‖df z‖ ≤ C + C * (‖x‖ + ‖y‖) ^ r := by
    intro z hz
    have hz' : ‖z‖ ≤ ‖x‖ + ‖y‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    calc
      ‖df z‖ ≤ C * (1 + ‖z‖ ^ r) := hbound z
      _ ≤ C * (1 + (‖x‖ + ‖y‖) ^ r) :=
        mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (Real.rpow_le_rpow (norm_nonneg _) hz' hr)) hC
      _ = C + C * (‖x‖ + ‖y‖) ^ r := by rw [mul_add, mul_one]
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ ↦ (hd z).hasDerivWithinAt) hb
    (convex_closedBall (0 : ℝ) (‖x‖ + ‖y‖))
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using
      le_add_of_nonneg_left (norm_nonneg x))
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using
      le_add_of_nonneg_right (norm_nonneg y))

end PDE.Analysis
