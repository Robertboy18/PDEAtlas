/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import PDE.Parabolic.Heat.ConvolutionSpace.JointContinuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Positivity.Finset

/-!
# Joint continuity of the Duhamel integral

A bounded continuous source gives a jointly continuous Duhamel integral.
-/

@[expose] public section

open Set MeasureTheory Filter PDE.Common
open scoped Interval Topology

namespace HeatEquation

variable {n : ℕ}

/-- A continuous bounded source gives a jointly continuous Duhamel integral, including the zero
upper endpoint. -/
theorem continuous_integral_initialValueSolution_family
    (g : ℝ → ℝ^n → ℝ) (hg : Continuous (Function.uncurry g))
    {M : ℝ} (hbound : ∀ s x, ‖g s x‖ ≤ M) :
    Continuous (fun p : ℝ^n × ℝ ↦
      ∫ s in 0..p.2, initialValueSolution (g s) p.1 (p.2 - s)) := by
  have hheat := continuous_initialValueSolution_family hg (fun p ↦ hbound p.1 p.2)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun p : ℝ^n × ℝ ↦ fun s ↦ initialValueSolution (g s) p.1 (p.2 - s))
    (by
      exact hheat.comp (continuous_snd.prodMk
        (continuous_fst.fst.prodMk (continuous_fst.snd.sub continuous_snd)))) continuous_snd

end HeatEquation
