/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.InitialValue
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Measurability of heat evolution with varying data

Totalized heat evolution is jointly measurable when the initial datum varies measurably
in a real parameter.
-/

@[expose] public section

namespace HeatEquation

open MeasureTheory

variable {n : ℕ}

/-- Joint measurability of the totalized heat evolution when the datum varies measurably in a
real parameter. -/
theorem stronglyMeasurable_initialValueSolution_varying
    (G : ℝ → ℝ^n → ℝ)
    (hG : Measurable fun p : ℝ × ℝ^n ↦ G p.1 p.2)
    (x : ℝ^n) (τ : ℝ) :
    StronglyMeasurable
      (fun s ↦ initialValueSolution (n := n) (G s) x (τ - s)) := by
  have hkernel : Measurable fun p : (ℝ^n) × ℝ ↦ fundamentalSolutionHeat (n := n) p.1 p.2 := by
    unfold fundamentalSolutionHeat
    exact Measurable.ite (measurableSet_le measurable_snd measurable_const) measurable_const
      (by fun_prop)
  exact StronglyMeasurable.ite (measurableSet_le (measurable_const.sub measurable_id)
      measurable_const)
    (hG.comp (measurable_id.prodMk measurable_const)).stronglyMeasurable
    ((hkernel.comp ((measurable_const.sub measurable_snd).prodMk
      (measurable_const.sub measurable_fst))).mul hG).stronglyMeasurable.integral_prod_right

end HeatEquation
