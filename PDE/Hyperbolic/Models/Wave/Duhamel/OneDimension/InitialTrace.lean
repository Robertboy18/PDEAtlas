/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.Models.Wave.Duhamel.OneDimension.Construction

/-!
# Initial traces of the one-dimensional forced wave

The zero displacement of each emitted wave makes the full initial derivative
of their superposition vanish. Its `C²` regularity then gives both joint
spacetime limits.
-/

@[expose] public noncomputable section

namespace WaveEquation

open PDE (partialDeriv)
open PDE.Common

/-- Every first derivative of the retarded field vanishes on the initial slice. -/
theorem fderiv_dAlembertDuhamelSolution_initial
    {f : ℝ^2 → ℝ} (hf : ContDiffOn ℝ 1 f {p | 0 ≤ p 0}) (x : ℝ^1) :
    fderiv ℝ (dAlembertDuhamelSolution f) (timeSpaceCons 0 x) = 0 :=
  fderiv_retardedWave_initial (contDiff_two_dAlembertSolution1D_forward hf)
    (fun _ hj ↦ continuous_iteratedFDeriv_dAlembertSolution1D_forward hf hj)
    x (dAlembert_satisfies_initial_pos _ _ x)

/-- The initial velocity of the retarded field is zero. -/
theorem partialDeriv_dAlembertDuhamelSolution_initial
    {f : ℝ^2 → ℝ} (hf : ContDiffOn ℝ 1 f {p | 0 ≤ p 0}) (x : ℝ^1) :
    (∂[0] (dAlembertDuhamelSolution f)) (timeSpaceCons 0 x) = 0 := by
  simp [partialDeriv, fderiv_dAlembertDuhamelSolution_initial hf x]

/-- Displacement tends to zero jointly in space and time at each initial point. -/
theorem tendsto_dAlembertDuhamelSolution_initial
    {f : ℝ^2 → ℝ} (hf : ContDiffOn ℝ 1 f {p | 0 ≤ p 0}) (x : ℝ^1) :
    Filter.Tendsto (dAlembertDuhamelSolution f) (nhds (timeSpaceCons 0 x)) (nhds 0) := by
  simpa only [ContinuousAt, dAlembertDuhamelSolution_initial] using
    (contDiff_two_dAlembertDuhamelSolution hf).continuous.continuousAt (x := timeSpaceCons 0 x)

/-- Velocity tends to zero jointly in space and time at each initial point. -/
theorem tendsto_partialDeriv_dAlembertDuhamelSolution_initial
    {f : ℝ^2 → ℝ} (hf : ContDiffOn ℝ 1 f {p | 0 ≤ p 0}) (x : ℝ^1) :
    Filter.Tendsto (∂[0] (dAlembertDuhamelSolution f)) (nhds (timeSpaceCons 0 x)) (nhds 0) := by
  have hreg := PDE.contDiff_partialDeriv_of_succ (m := 1) (i := 0)
    (contDiff_two_dAlembertDuhamelSolution hf)
  simpa only [ContinuousAt, partialDeriv_dAlembertDuhamelSolution_initial hf] using
    hreg.continuous.continuousAt (x := timeSpaceCons 0 x)

end WaveEquation
