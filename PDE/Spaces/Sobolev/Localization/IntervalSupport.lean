/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Localization to an interval

A function supported in an open interval has derivative supported in the same interval.
At either endpoint, a one-sided zero derivative determines the ordinary derivative whenever
it exists; Lean's total derivative is zero when it does not. No differentiability assumption
is needed for the support conclusion.

The integral lemma reduces half-line integrals to the supporting interval, without requiring
integrability. These facts localize both sides of the one-dimensional Hardy inequalities.
-/

@[expose] public section

open Set Function MeasureTheory

namespace PDE

/-- Support inside an open interval is preserved by the total derivative. At the endpoints,
one-sided constancy suffices, so no differentiability hypothesis is needed. -/
theorem support_deriv_subset_Ioo {u : ℝ → ℝ} {a b : ℝ}
    (hsupp : support u ⊆ Ioo a b) : support (deriv u) ⊆ Ioo a b := by
  intro x hx
  by_contra h
  have hzero : deriv u x = 0 := by
    have hout : x ≤ a ∨ b ≤ x := by simpa only [mem_Ioo, not_and_or, not_lt] using h
    rcases hout with hx | hx
    · have heq : EqOn u (fun _ ↦ 0) (Iic x) := by
        intro y hy
        apply notMem_support.mp
        intro hmem
        exact (not_lt_of_ge (hy.trans hx)) (hsupp hmem).1
      exact ((hasDerivWithinAt_const x (Iic x) (0 : ℝ)).congr heq
        (heq (le_refl x))).deriv_eq_zero (uniqueDiffWithinAt_Iic x)
    · have heq : EqOn u (fun _ ↦ 0) (Ici x) := by
        intro y hy
        apply notMem_support.mp
        intro hmem
        exact (not_lt_of_ge (hx.trans hy)) (hsupp hmem).2
      exact ((hasDerivWithinAt_const x (Ici x) (0 : ℝ)).congr heq
        (heq (le_refl x))).deriv_eq_zero (uniqueDiffWithinAt_Ici x)
  exact hx hzero

end PDE

namespace MeasureTheory

/-- A half-line integral of a function supported in `(a,b)` equals its integral over `(a,b]`
whenever the half-line starts at or to the left of `a`. -/
theorem setIntegral_Ioi_eq_Ioc_of_support_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b c : ℝ} {μ : Measure ℝ}
    (hca : c ≤ a) (hsupp : support f ⊆ Ioo a b) :
    (∫ x in Ioi c, f x ∂μ) = ∫ x in Ioc a b, f x ∂μ := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun _ hx ↦ lt_of_le_of_lt hca hx.1)
  intro x hx
  exact notMem_support.mp fun hmem ↦ hx.2 (Ioo_subset_Ioc_self (hsupp hmem))

end MeasureTheory
