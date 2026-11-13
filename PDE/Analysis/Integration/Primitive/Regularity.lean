/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Regularity of a Banach-valued primitive

The fundamental theorem of calculus identifies the derivative of the primitive with
its integrand. Thus integration gains one finite derivative and preserves smoothness.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace PDE.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Integration from a fixed initial time gains one derivative, in any Banach space.
The index includes all finite orders and `∞`. -/
theorem contDiff_intervalIntegral_of_contDiff {n : ℕ∞} {f : ℝ → E}
    (hf : ContDiff ℝ n f) (a : ℝ) :
    ContDiff ℝ ((n : ℕ∞ω) + 1) (fun t ↦ ∫ s in a..t, f s) := by
  have hd (t : ℝ) : HasDerivAt (fun t ↦ ∫ s in a..t, f s) (f t) t :=
    intervalIntegral.integral_hasDerivAt_right (hf.continuous.intervalIntegrable a t)
      hf.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hf.continuous.continuousAt
  refine contDiff_succ_iff_deriv.mpr ⟨fun t ↦ (hd t).differentiableAt, ?_, ?_⟩
  · simp
  · have heq : deriv (fun t ↦ ∫ s in a..t, f s) = f := funext fun t ↦ (hd t).deriv
    rwa [heq]

end PDE.Analysis
