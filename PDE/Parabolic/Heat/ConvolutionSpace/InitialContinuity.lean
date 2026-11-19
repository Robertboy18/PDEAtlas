/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.ConvolutionSpace.Scaling
import PDE.Parabolic.Heat.Kernel.Integrability
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Continuity of bounded-data heat evolution through initial time

The fixed-Gaussian representation and dominated convergence give joint continuity,
including at time zero. At nonpositive times `initialValueSolution` is the datum itself.
-/

@[expose] public section

open MeasureTheory Filter

namespace HeatEquation

variable {n : ℕ}

/-- Bounded continuous initial data give joint continuity of the heat evolution at
every time, including the initial time. -/
theorem continuous_initialValueSolution_timeSpace
    (g : ℝ^n → ℝ) (hg : Continuous g) (hgb : ∃ M, ∀ y, |g y| ≤ M) :
    Continuous (fun p : ℝ × ℝ^n ↦ initialValueSolution g p.2 p.1) := by
  obtain ⟨M, hM⟩ := hgb
  let K : ℝ^n → ℝ := fun y ↦ fundamentalSolutionHeat (0 - y) 1
  have hK : Integrable K :=
    (fundamentalSolutionHeat_integrable 1 zero_lt_one).comp_sub_left 0
  have hKpos (y : ℝ^n) : 0 ≤ K y :=
    (fundamentalSolutionHeat_pos (0 - y) 1 zero_lt_one).le
  simp only [initialValueSolution_eq_fixed_gaussian]
  apply continuous_of_dominated (bound := fun y ↦ K y * M)
  · intro p
    exact hK.aestronglyMeasurable.mul
      (hg.comp (by fun_prop)).aestronglyMeasurable
  · intro p
    exact ae_of_all _ fun y ↦ by
      rw [norm_mul, Real.norm_of_nonneg (hKpos y)]
      exact mul_le_mul_of_nonneg_left (hM _) (hKpos y)
  · exact hK.mul_const M
  · exact ae_of_all _ fun y ↦
      continuous_const.mul (hg.comp (by fun_prop))

end HeatEquation
