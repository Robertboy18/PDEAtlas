/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.ConvolutionSpace.SpatialDifferentiation
import PDE.Parabolic.Heat.ConvolutionSpace.JointContinuity

/-!
# Joint continuity of heat-evolved spatial derivatives

Transferring derivatives to the data lets the joint-continuity theorem apply directly,
including at heat age zero.
-/

@[expose] public section

open Set MeasureTheory Filter PDE.Common
open scoped Interval Topology

namespace HeatEquation

variable {n : ℕ}

/-- Joint continuity of a bounded first spatial derivative is preserved by heat evolution of a
parameter family. -/
theorem continuous_partialDeriv_initialValueSolution_family
    {T : Type*} [TopologicalSpace T] [FirstCountableTopology T]
    (g : T → ℝ^n → ℝ) (hg : ∀ t, ContDiff ℝ 1 (g t))
    (hgc : ∀ t, HasCompactSupport (g t)) (i : Fin n)
    (hpartial : Continuous (fun p : T × ℝ^n ↦ (∂[i] (g p.1)) p.2))
    {M : ℝ} (hbound : ∀ t x, ‖(∂[i] (g t)) x‖ ≤ M) :
    Continuous (fun p : T × ℝ^n × ℝ ↦
      (∂[i] (fun z ↦ initialValueSolution (g p.1) z p.2.2)) p.2.1) := by
  simp_rw [partialDeriv_initialValueSolution_eq_source _ (hg _) (hgc _)]
  exact continuous_initialValueSolution_family hpartial (fun p ↦ hbound p.1 p.2)

/-- Joint continuity of bounded mixed second spatial derivatives is preserved by heat evolution of
a parameter family. -/
theorem continuous_secondPartial_initialValueSolution_family
    {T : Type*} [TopologicalSpace T] [FirstCountableTopology T]
    (g : T → ℝ^n → ℝ) (hg : ∀ t, ContDiff ℝ 2 (g t))
    (hgc : ∀ t, HasCompactSupport (g t)) (i j : Fin n)
    (hpartial : Continuous
      (fun p : T × ℝ^n ↦ (∂[i] (∂[j] (g p.1))) p.2))
    {M : ℝ} (hbound : ∀ t x, ‖(∂[i] (∂[j] (g t))) x‖ ≤ M) :
    Continuous (fun p : T × ℝ^n × ℝ ↦
      (∂[i] (∂[j]
        (fun z ↦ initialValueSolution (g p.1) z p.2.2))) p.2.1) := by
  simp_rw [secondPartial_initialValueSolution_eq_source_all_time _ (hg _) (hgc _)]
  exact continuous_initialValueSolution_family hpartial (fun p ↦ hbound p.1 p.2)

end HeatEquation
