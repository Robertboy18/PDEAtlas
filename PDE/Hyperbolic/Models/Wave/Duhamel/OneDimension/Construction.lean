/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.Models.Wave.Duhamel.OneDimension.SourceFamily
public import PDE.Hyperbolic.Models.Wave.Duhamel.SpaceTime

/-!
# The one-dimensional retarded wave

We superpose the d'Alembert wave emitted by each forcing slice. One source
derivative suffices: the characteristic integral gives a second wave
derivative before we integrate over source times.
-/

@[expose] public noncomputable section

namespace WaveEquation

open PDE.Common

/-- Duhamel's formula in one space dimension, with zero initial position and velocity. -/
def dAlembertDuhamelSolution (f : ℝ^2 → ℝ) : ℝ^2 → ℝ :=
  retardedWave (fun s ↦ dAlembertSolution1D (fun _ ↦ 0)
    (fun x ↦ f (timeSpaceCons (max 0 s) x)))

/-- The retarded field has zero initial displacement. -/
@[simp]
theorem dAlembertDuhamelSolution_initial (f : ℝ^2 → ℝ) (x : ℝ^1) :
    dAlembertDuhamelSolution f (timeSpaceCons 0 x) = 0 :=
  retardedWave_initial _ x

/-- A forward `C¹` source gives a jointly `C²` retarded field, including at time zero. -/
theorem contDiff_two_dAlembertDuhamelSolution {f : ℝ^2 → ℝ} (hf : ContDiffOn ℝ 1 f {p | 0 ≤ p 0}) :
    ContDiff ℝ 2 (dAlembertDuhamelSolution f) :=
  contDiff_two_retardedWave (contDiff_two_dAlembertSolution1D_forward hf)
    (fun _ hj ↦ continuous_iteratedFDeriv_dAlembertSolution1D_forward hf hj)
    (fun _ x ↦ dAlembert_satisfies_initial_pos _ _ x)

end WaveEquation
