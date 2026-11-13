/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Differentiating the norm of a Hilbert-space curve

Away from zero, the derivative of the norm is the radial component of the velocity.
The within-set version also applies to one-sided derivatives.
-/

@[expose] public section

open scoped RealInnerProductSpace

namespace PDE.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The norm derivative of a nonzero curve, including within arbitrary sets. -/
theorem hasDerivWithinAt_norm_of_ne_zero {u : ℝ → H} {v : H} {s : Set ℝ} {t : ℝ}
    (hu : HasDerivWithinAt u v s t) (hne : u t ≠ 0) :
    HasDerivWithinAt (fun x ↦ ‖u x‖) (⟪u t, v⟫ / ‖u t‖) s t := by
  have hn : ‖u t‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  simpa only [Real.sqrt_sq_eq_abs, abs_norm,
    mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)] using
    hu.norm_sq.sqrt (pow_ne_zero 2 hn)

end PDE.Analysis
