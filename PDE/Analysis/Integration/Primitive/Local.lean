/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Primitive.Regularity

/-!
# Moving primitives on a closed interval

The fundamental theorem of calculus holds relative to the closed interval,
including its boundary. Smoothness of the integrand on that interval therefore
gives one more derivative of its oriented primitive there. The fixed anchor may
lie anywhere in the interval; no extension of the integrand is assumed.
-/

@[expose] public section

open MeasureTheory Set
open scoped ContDiff Interval

namespace PDE.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E} {a b c x : ℝ}

/-- A continuous integrand on the closed interval differentiates its oriented
primitive within that interval, also at either endpoint. -/
theorem hasDerivWithinAt_intervalIntegral_uIcc
    (hf : ContinuousOn f (uIcc a b)) (hc : c ∈ uIcc a b) (hx : x ∈ uIcc a b) :
    HasDerivWithinAt (fun t ↦ ∫ s in c..t, f s) (f x) (uIcc a b) x := by
  let : Fact (x ∈ uIcc a b) := ⟨hx⟩
  exact intervalIntegral.integral_hasDerivWithinAt_right
    ((hf.mono (uIcc_subset_uIcc hc hx)).intervalIntegrable)
    (hf.stronglyMeasurableAtFilter_nhdsWithin measurableSet_uIcc x) (hf x hx)

/-- On a closed interval, integration gains one derivative relative to the
interval. This includes all finite orders, infinite smoothness, either
orientation, and a degenerate interval. -/
theorem contDiffOn_intervalIntegral_of_contDiffOn {n : ℕ∞}
    (hf : ContDiffOn ℝ n f (uIcc a b)) (hc : c ∈ uIcc a b) :
    ContDiffOn ℝ ((n : ℕ∞ω) + 1) (fun t ↦ ∫ s in c..t, f s) (uIcc a b) := by
  by_cases hab : a = b
  · subst b
    simp only [uIcc_self, mem_singleton_iff] at hc
    subst c
    apply (contDiffOn_const (c := (0 : E))).congr
    intro x hx
    simp only [uIcc_self, mem_singleton_iff] at hx
    simp [hx]
  have hs := uniqueDiffOn_uIcc hab
  have hd (x : ℝ) (hx : x ∈ uIcc a b) :=
    hasDerivWithinAt_intervalIntegral_uIcc hf.continuousOn hc hx
  refine (contDiffOn_succ_iff_derivWithin hs).mpr
    ⟨fun x hx ↦ (hd x hx).differentiableWithinAt, ?_, ?_⟩
  · simp
  · exact hf.congr fun x hx ↦ (hd x hx).derivWithin (hs x hx)

end PDE.Analysis
