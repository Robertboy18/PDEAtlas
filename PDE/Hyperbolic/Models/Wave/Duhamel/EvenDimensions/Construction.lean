/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.Models.Wave.Duhamel.EvenDimensions.SourceFamily
public import PDE.Hyperbolic.Models.Wave.Duhamel.SpaceTime
public import PDE.Hyperbolic.Models.Wave.EvenDimensions.ClassicalSolution

/-!
# Even-dimensional Duhamel construction

Integrate the homogeneous wave with zero displacement and forcing-slice
velocity. Its normalization and dimension descent are those of `evenWaveSolution`.
Only the source index is clipped, so forward `C^(k+2)` forcing gives joint `C²` regularity.
-/

@[expose] public noncomputable section

open PDE (time)

namespace WaveEquation

open PDE.Analysis PDE.Common

/-- The retarded integral of the even-dimensional velocity solution. -/
def evenDuhamelSolution (k : ℕ) (f : ℝ^(2 * k + 2 + 1) → ℝ) :
    ℝ^(2 * k + 2 + 1) → ℝ :=
  fun p ↦ retardedIntegral (fun s q ↦
    evenWaveSolution k (fun _ ↦ 0) (fun x ↦ f (timeSpaceCons (max 0 s) x))
      (joinSpaceTime q)) (splitSpaceTime p)

/-- The even-dimensional formula is jointly `C²` through time zero. -/
theorem contDiff_two_evenDuhamelSolution (k : ℕ) {f : ℝ^(2 * k + 2 + 1) → ℝ}
    (hf : ContDiffOn ℝ (k + 2) f {p | 0 ≤ p 0}) :
    ContDiff ℝ 2 (evenDuhamelSolution k f) :=
  contDiff_two_retardedWave (contDiff_two_evenWaveSolution_forward k hf)
    (fun _ hj ↦ continuous_iteratedFDeriv_evenWaveSolution_forward k hf hj)
    (fun _ x ↦ evenWaveSolution_initial_position k contDiff_const x)

/-- The collapsed integral has zero initial displacement. -/
theorem evenDuhamelSolution_initial (k : ℕ) (f : ℝ^(2 * k + 2 + 1) → ℝ) (x : ℝ^(2 * k + 2)) :
    evenDuhamelSolution k f (timeSpaceCons 0 x) = 0 := by
  simp [evenDuhamelSolution, retardedIntegral, splitSpaceTime, time]

end WaveEquation
