/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.Models.Wave.Duhamel.OddDimensions.ClassicalSolution
import CAS.IntegrationTactic
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# A time-dependent forced wave

For the source `sin t`, the three-dimensional Duhamel integral is `t - sin t`
at nonnegative times, and the Duhamel theorem
`oddDuhamelSolution_satisfiesResidualAssignedCauchyData` shows that it solves the
forced wave equation with zero Cauchy data.
-/

open PDE (SatisfiesPDEProblem)

@[expose] public noncomputable section

namespace WaveEquation.Examples

open PDE.Analysis PDE.Common

/-- For `t ≥ 0` the Duhamel integral of `sin t` is `t - sin t`. -/
theorem oddDuhamelSolution_zero_sin (x : ℝ^3) {t : ℝ} (ht : 0 ≤ t) :
    oddDuhamelSolution 0 (fun p ↦ Real.sin (p 0)) (timeSpaceCons t x) =
      t - Real.sin t := by
  have hmean (s r : ℝ) :
      unitSphereAverage 3 (fun y ↦ Real.sin ((timeSpaceCons s y) 0)) x r =
        Real.sin s := by
    calc
      _ = unitSphereAverage 3 (fun _ ↦ Real.sin s) x 0 := rfl
      _ = Real.sin s := unitSphereAverage_zero _ _
  rw [oddDuhamelSolution_eq_integral 0 _ x ht]
  simp only [Nat.mul_zero, Nat.doubleFactorial, Nat.cast_one, inv_one,
    one_mul, oddWavePotential_timeSpaceCons, oddSphericalProfile_zero, hmean]
  cas

/-- The Duhamel integral solves the wave equation with source `sin t` and zero data. -/
theorem sineDuhamel_satisfiesResidualAssignedCauchyData :
    SatisfiesPDEProblem
      (forcedWaveResidualAssignedCauchyDataProblem (n := 3)
        (fun p ↦ Real.sin (p 0)) (fun _ ↦ 0) (fun _ ↦ 0))
      (oddDuhamelSolution 0 (fun p ↦ Real.sin (p 0))) :=
  oddDuhamelSolution_satisfiesResidualAssignedCauchyData 0 (by fun_prop)

end WaveEquation.Examples
