/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.EuclideanBall
public import PDE.Common.Euclidean.SpaceTime
import PDE.Analysis.Integration.Cone.Continuity

/-!
# Continuity in the radius of a spatial ball

A continuous density in three dimensions has a continuous ball integral at each
positive radius. This follows from continuity on shrinking balls by reversing time.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter PDE PDE.Common PDE.Analysis
open scoped ENNReal Topology

namespace PDE.Analysis

/-- A continuous density has continuous ball integrals at every positive radius. -/
theorem continuousAt_ballIntegral_radius {f : ℝ^3 → ℝ} (hf : Continuous f)
    (c : ℝ^3) {r : ℝ} (hr : 0 < r) :
    ContinuousAt (fun R ↦ ballIntegral 3 f c R) r := by
  let P : ℝ^4 → ℝ := fun p ↦ f ((timeSpaceContinuousLinearEquiv 3 p).2)
  have hP : Continuous P := hf.comp
    ((timeSpaceContinuousLinearEquiv 3).continuous.snd)
  have hc := continuousOn_ballIntegral_shrinking hP c 0 (-r) (by change -r ≤ 0; linarith)
  have ha := hc.continuousAt (Iic_mem_nhds (by linarith : -r < 0))
  have hcomp := ha.comp (x := r) continuous_neg.continuousAt
  simpa only [P, timeSpaceContinuousLinearEquiv_apply,
    spatialPart_timeSpaceCons, Function.comp_def, zero_sub, neg_neg] using hcomp

end PDE.Analysis
