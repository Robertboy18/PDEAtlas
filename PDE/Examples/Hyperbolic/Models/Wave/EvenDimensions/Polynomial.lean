/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.EvenDimensions.ClassicalSolution
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# A four-dimensional polynomial wave

Writing `R = x₀²+x₁²+x₂²+x₃²`, quartic displacement `R²` and cubic velocity
`x₀³+x₁x₂x₃` give `R²+12t²R+8t⁴+t(x₀³+x₁x₂x₃)+t³x₀`. The polynomial solves the wave
equation with these data, so by `eq_evenWaveSolution_of_satisfiesResidualAssignedCauchyData`
it equals the even-dimensional solution formula (`evenWaveSolution_eq_polynomial`) and
the weighted ball formula (38) of Evans, §2.4.1(e)
(`evansEvenDimensionalFormula_one_eq_polynomial`). The data are unbounded and involve all four
spatial coordinates.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.1(e), (38), p. 79, and Theorem 3 (Solution of
  wave equation in even dimensions), p. 80.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (laplacian SatisfiesPDEProblem)

namespace WaveEquation.Examples

open PDE.Common

/-- Quartic displacement using all four spatial coordinates. -/
def quarticEvenDisplacement (x : ℝ^4) : ℝ :=
  (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) ^ 2

/-- Cubic velocity with both a pure cube and a mixed term. -/
def cubicEvenVelocity (x : ℝ^4) : ℝ := x 0 ^ 3 + x 1 * x 2 * x 3

/-- The corresponding polynomial in canonical spacetime coordinates. -/
def polynomialEvenWave (p : ℝ^5) : ℝ :=
  (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 + p 4 ^ 2) ^ 2 +
    12 * p 0 ^ 2 * (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 + p 4 ^ 2) + 8 * p 0 ^ 4 +
      p 0 * (p 1 ^ 3 + p 2 * p 3 * p 4) + p 0 ^ 3 * p 1

/-- The polynomial is `C^m` for every `m`. -/
theorem contDiff_polynomialEvenWave (m : ℕ) : ContDiff ℝ m polynomialEvenWave := by
  unfold polynomialEvenWave
  fun_prop

/-- The time derivative of the polynomial. -/
theorem partialDeriv_polynomialEvenWave_time (p : ℝ^5) :
    (∂[0] polynomialEvenWave) p =
      24 * p 0 * (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 + p 4 ^ 2) + 32 * p 0 ^ 3 +
        (p 1 ^ 3 + p 2 * p 3 * p 4) + 3 * p 0 ^ 2 * p 1 := by
  unfold polynomialEvenWave
  cas

/-- The second time derivative of the polynomial. -/
theorem secondPartialDeriv_polynomialEvenWave_time (p : ℝ^5) :
    (∂[0] (∂[0] polynomialEvenWave)) p =
      24 * (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 + p 4 ^ 2) + 96 * p 0 ^ 2 +
        6 * p 0 * p 1 := by
  rw [show ∂[0] polynomialEvenWave = _ from
    funext partialDeriv_polynomialEvenWave_time]
  cas

/-- The spatial Laplacian of the polynomial at time `t`. -/
theorem laplacian_polynomialEvenWave_slice (x : ℝ^4) (t : ℝ) :
    laplacian (fun y ↦ polynomialEvenWave (timeSpaceCons t y)) x =
      24 * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) + 96 * t ^ 2 + 6 * t * x 0 := by
  simp only [polynomialEvenWave, timeSpaceCons, WithLp.ofLp_toLp, Matrix.cons_val_zero]
  cas

/-- The polynomial solves the coordinate wave equation. -/
theorem waveOperator_polynomialEvenWave (p : ℝ^5) : waveOperator polynomialEvenWave p = 0 := by
  obtain ⟨⟨t, x⟩, rfl⟩ := (timeSpaceContinuousLinearEquiv 4).symm.surjective p
  change waveOperator polynomialEvenWave (timeSpaceCons t x) = 0
  rw [waveOperator, ← laplacian_timeSlice polynomialEvenWave t x (contDiff_polynomialEvenWave 2),
    laplacian_polynomialEvenWave_slice, secondPartialDeriv_polynomialEvenWave_time]
  simp [timeSpaceCons]

/-- The polynomial solves the wave equation with displacement `R²` and velocity `x₀³ + x₁x₂x₃`. -/
theorem polynomialEvenWave_satisfiesResidualAssignedCauchyData :
    SatisfiesPDEProblem
      (waveResidualAssignedCauchyDataProblem (n := 4)
        quarticEvenDisplacement cubicEvenVelocity) polynomialEvenWave := by
  refine forcedWaveResidualAssignedCauchyDataProblem.of_residual_initial ?_ ?_ ?_
  · intro p _
    exact waveOperator_polynomialEvenWave p
  · intro p hp
    simp [polynomialEvenWave, quarticEvenDisplacement, hp, spatialPartCLM_apply]
  · intro p hp
    rw [partialDeriv_polynomialEvenWave_time]
    simp [cubicEvenVelocity, hp, spatialPartCLM_apply]

/-- The even-dimensional solution formula agrees with the polynomial at every nonnegative time. -/
theorem evenWaveSolution_eq_polynomial (x : ℝ^4) {t : ℝ} (ht : 0 ≤ t) :
    evenWaveSolution 1 quarticEvenDisplacement cubicEvenVelocity (timeSpaceCons t x) =
      polynomialEvenWave (timeSpaceCons t x) := by
  exact (eq_evenWaveSolution_of_satisfiesResidualAssignedCauchyData 1
    (by unfold quarticEvenDisplacement; fun_prop) (by unfold cubicEvenVelocity; fun_prop)
    (contDiff_polynomialEvenWave 2)
    polynomialEvenWave_satisfiesResidualAssignedCauchyData ht x).symm

/-- The weighted ball and radial derivative formula has this polynomial value. -/
theorem evansEvenDimensionalFormula_one_eq_polynomial (x : ℝ^4) (t : Set.Ioi (0 : ℝ)) :
    evansEvenDimensionalFormula 1 quarticEvenDisplacement cubicEvenVelocity x t =
      (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) ^ 2 +
        12 * (t : ℝ) ^ 2 * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) + 8 * (t : ℝ) ^ 4 +
          (t : ℝ) * (x 0 ^ 3 + x 1 * x 2 * x 3) + (t : ℝ) ^ 3 * x 0 := by
  rw [← evenWaveSolution_eq_evansEvenDimensionalFormula 1
    (by unfold quarticEvenDisplacement; fun_prop) (by unfold cubicEvenVelocity; fun_prop),
    evenWaveSolution_eq_polynomial x t.property.le]
  simp [polynomialEvenWave, timeSpaceCons]

end WaveEquation.Examples
