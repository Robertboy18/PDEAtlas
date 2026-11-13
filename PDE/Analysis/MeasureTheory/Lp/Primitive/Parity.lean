/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Primitive

/-!
# Parity of the normalized L² primitive

The primitive normalized at zero is odd when its integrand is even almost everywhere.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set

namespace PDE.Analysis

/-- The primitive normalized at zero is odd when its L² integrand is even
almost everywhere. -/
theorem odd_l2Primitive_of_ae_even (g : Lp ℝ 2 (volume : Measure ℝ))
    (hg : ∀ᵐ x ∂volume, g (-x) = g x) :
    Function.Odd (l2Primitive g) := by
  intro x
  have hi := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := x) g
  rw [intervalIntegral.integral_congr_ae (hg.mono fun _ hx _ ↦ hx), neg_zero,
    intervalIntegral.integral_symm (a := 0) (b := -x)] at hi
  exact neg_eq_iff_eq_neg.mp hi.symm

end PDE.Analysis
