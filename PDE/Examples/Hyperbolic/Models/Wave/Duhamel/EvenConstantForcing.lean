/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.Models.Wave.Duhamel.EvenDimensions.ClassicalSolution
import CAS.IntegrationTactic

/-!
# Constant forcing in two and four spatial dimensions

The descended kernels give the retarded integral `c t²/2` in both dimensions. In two
dimensions the Duhamel theorem `evenDuhamelSolution_satisfiesResidualAssignedCauchyData`
shows that it solves the forced wave equation with zero Cauchy data.
-/

open PDE (SatisfiesPDEProblem)

@[expose] public noncomputable section

namespace WaveEquation.Examples

open PDE.Analysis PDE.Common

private theorem evenWaveSolution_zero_constant_velocity
    (c : ℝ) (x : ℝ^2) (t : ℝ) :
    evenWaveSolution 0 (fun _ ↦ 0) (fun _ ↦ c) (timeSpaceCons t x) = t * c := by
  have hmean (a : ℝ) (z : ℝ^3) (r : ℝ) :
      unitSphereAverage 3 (fun _ ↦ a) z r = a := by
    calc
      _ = unitSphereAverage 3 (fun _ ↦ a) z 0 := rfl
      _ = a := unitSphereAverage_zero _ _
  rw [evenWaveSolution_timeSpaceCons]
  simp only [Function.comp_def, oddWaveSolution,
    partialDeriv_oddWavePotential_time 0 contDiff_const, oddWavePotential_timeSpaceCons,
    oddSphericalProfile_zero, hmean]
  have hd : deriv (fun r : ℝ ↦ r * 0) t = 0 := by cas
  simp only [hd, zero_add, Nat.doubleFactorial, Nat.cast_one, inv_one, one_mul]

private theorem evenWaveSolution_one_constant_velocity
    (c : ℝ) (x : ℝ^4) (t : ℝ) :
    evenWaveSolution 1 (fun _ ↦ 0) (fun _ ↦ c) (timeSpaceCons t x) = t * c := by
  have hprofile (a : ℝ) (z : ℝ^5) :
      oddSphericalProfile 1 (fun _ ↦ a) z = fun r ↦ 3 * r * a := by
    have hmean (r : ℝ) : unitSphereAverage 5 (fun _ ↦ a) z r = a := by
      calc
        _ = unitSphereAverage 5 (fun _ ↦ a) z 0 := rfl
        _ = a := unitSphereAverage_zero _ _
    unfold oddSphericalProfile
    simp only [hmean]
    change oddRadialTransform (0 + 1) (fun r ↦ r ^ (2 * 0 + 3) * a) = _
    rw [oddRadialTransform_step 0 contDiff_const]
    simp only [oddRadialTransform_zero, deriv_const]
    funext r
    cas
  rw [evenWaveSolution_timeSpaceCons]
  simp only [Function.comp_def, oddWaveSolution,
    partialDeriv_oddWavePotential_time 1 contDiff_const, oddWavePotential_timeSpaceCons,
    hprofile]
  have hd : deriv (fun r : ℝ ↦ 3 * r * 0) t = 0 := by cas
  simp only [hd, zero_add]
  norm_num [Nat.doubleFactorial]
  cas

/-- The two-dimensional Duhamel integral for a nonzero constant source. -/
theorem evenDuhamelSolution_zero_constant (c : ℝ) (x : ℝ^2) {t : ℝ} (ht : 0 ≤ t) :
    evenDuhamelSolution 0 (fun _ ↦ c) (timeSpaceCons t x) = c * t ^ 2 / 2 := by
  rw [evenDuhamelSolution_eq_integral 0 (fun _ ↦ c) x ht]
  simp only [evenWaveSolution_zero_constant_velocity]
  cas

/-- The four-dimensional Duhamel integral for a constant source `c` is also `c t²/2`. -/
theorem evenDuhamelSolution_one_constant (c : ℝ) (x : ℝ^4) {t : ℝ} (ht : 0 ≤ t) :
    evenDuhamelSolution 1 (fun _ ↦ c) (timeSpaceCons t x) = c * t ^ 2 / 2 := by
  rw [evenDuhamelSolution_eq_integral 1 (fun _ ↦ c) x ht]
  simp only [evenWaveSolution_one_constant_velocity]
  cas

/-- In two dimensions the Duhamel integral solves the forced problem with zero data. -/
example (c : ℝ) :
    SatisfiesPDEProblem
      (forcedWaveResidualAssignedCauchyDataProblem (n := 2)
        (fun _ ↦ c) (fun _ ↦ 0) (fun _ ↦ 0))
      (evenDuhamelSolution 0 (fun _ ↦ c)) :=
  evenDuhamelSolution_satisfiesResidualAssignedCauchyData 0 contDiff_const.contDiffOn

end WaveEquation.Examples
