/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Reflection of supported real integrals

For an even integrand supported in a symmetric interval, reflection reduces
the full-line integral to twice its positive half. The identity also respects
the totalized integral convention.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace MeasureTheory

/-- For an even function vanishing to the right of `L`, the full-line integral is twice
the integral on `(0,L)`. Reflection also respects the totalized integral convention. -/
theorem integral_eq_two_mul_integral_Ioo_of_even_support {g : ℝ → ℝ} {L : ℝ}
    (hg : Function.Even g) (hsupport : ∀ y, L ≤ y → g y = 0) :
    (∫ x, g x) = 2 * ∫ x in Ioo 0 L, g x := by
  have habs : (fun x ↦ g |x|) = g := by
    funext x
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, hg x]
  calc
    _ = 2 * ∫ x in Ioi 0, g x := by rw [← integral_comp_abs, habs]
    _ = _ := by
      congr 1
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        (fun _ hx ↦ hx.1)
      intro x hx
      exact hsupport x (not_lt.mp fun hlt ↦ hx.2 ⟨hx.1, hlt⟩)

end MeasureTheory
