/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.OddDimensions.ClassicalSolution
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# A five-dimensional polynomial wave

The unbounded data `g(x)=x₀⁴` and `h(x)=x₁³` give
`u(x,t)=x₀⁴+6t²x₀²+t⁴+t x₁³+t³x₁`, which solves the wave equation with these data. By
`eq_oddWaveSolution_of_satisfiesResidualAssignedCauchyData` it equals the odd-dimensional
solution formula (`oddWaveSolution_eq_polynomial`) and the representation formula (31) of
Evans, §2.4.1(d) (`evansOddDimensionalFormula_one_eq_polynomial`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.1(d), (31), p. 76, and Theorem 2 (Solution of
  wave equation in odd dimensions), p. 77.
  <https://doi.org/10.1090/gsm/019>
-/

open PDE (SatisfiesPDEProblem)

@[expose] public noncomputable section

namespace WaveEquation.Examples

open PDE.Common

/-- A wave with quartic displacement and cubic velocity in five space dimensions. -/
def polynomialOddWave : ℝ^6 → ℝ :=
  fun p ↦ p 1 ^ 4 + 6 * p 0 ^ 2 * p 1 ^ 2 + p 0 ^ 4 +
    p 0 * p 2 ^ 3 + p 0 ^ 3 * p 2

/-- The polynomial is `C^m` for every `m`. -/
theorem contDiff_polynomialOddWave (m : ℕ) : ContDiff ℝ m polynomialOddWave := by
  unfold polynomialOddWave
  fun_prop

/-- The time derivative of the polynomial. -/
theorem partialDeriv_polynomialOddWave_time (p : ℝ^6) :
    (∂[0] polynomialOddWave) p =
      12 * p 0 * p 1 ^ 2 + 4 * p 0 ^ 3 + p 2 ^ 3 + 3 * p 0 ^ 2 * p 2 := by
  unfold polynomialOddWave
  cas

/-- The second time derivative of the polynomial. -/
theorem secondPartialDeriv_polynomialOddWave_time (p : ℝ^6) :
    (∂[0] (∂[0] polynomialOddWave)) p =
      12 * p 1 ^ 2 + 12 * p 0 ^ 2 + 6 * p 0 * p 2 := by
  rw [show ∂[0] polynomialOddWave = _ from
    funext partialDeriv_polynomialOddWave_time]
  cas

/-- The first spatial derivatives of the polynomial. -/
theorem partialDeriv_polynomialOddWave_space (i : Fin 5) (p : ℝ^6) :
    (∂[i.succ] polynomialOddWave) p =
      if i = 0 then 4 * p 1 ^ 3 + 12 * p 0 ^ 2 * p 1
      else if i = 1 then 3 * p 0 * p 2 ^ 2 + p 0 ^ 3 else 0 := by
  unfold polynomialOddWave
  fin_cases i <;> norm_num only [Fin.isValue, Fin.reduceEq, ↓reduceIte] <;> cas

/-- The pure second spatial derivatives of the polynomial. -/
theorem secondPartialDeriv_polynomialOddWave_space (i : Fin 5) (p : ℝ^6) :
    (∂[i.succ] (∂[i.succ] polynomialOddWave)) p =
      if i = 0 then 12 * p 1 ^ 2 + 12 * p 0 ^ 2
      else if i = 1 then 6 * p 0 * p 2 else 0 := by
  rw [show ∂[i.succ] polynomialOddWave = _ from
    funext (partialDeriv_polynomialOddWave_space i)]
  fin_cases i
  · change (∂[1] ((fun q : ℝ^6 ↦ 4 * q 1 ^ 3 + 12 * q 0 ^ 2 * q 1) : ℝ^6 → ℝ)) p =
      12 * p 1 ^ 2 + 12 * p 0 ^ 2
    cas
  · change (∂[2] ((fun q : ℝ^6 ↦ 3 * q 0 * q 2 ^ 2 + q 0 ^ 3) : ℝ^6 → ℝ)) p =
      6 * p 0 * p 2
    cas
  · change (∂[3] (fun _ : ℝ^6 ↦ (0 : ℝ))) p = 0
    cas
  · change (∂[4] (fun _ : ℝ^6 ↦ (0 : ℝ))) p = 0
    cas
  · change (∂[5] (fun _ : ℝ^6 ↦ (0 : ℝ))) p = 0
    cas

/-- The polynomial solves the coordinate wave equation. -/
theorem waveOperator_polynomialOddWave (p : ℝ^6) :
    waveOperator polynomialOddWave p = 0 := by
  unfold waveOperator
  rw [secondPartialDeriv_polynomialOddWave_time]
  simp_rw [secondPartialDeriv_polynomialOddWave_space]
  norm_num [Fin.sum_univ_succ]

/-- The initial velocity of the polynomial is `x₁³`. -/
theorem partialDeriv_polynomialOddWave_initial (x : ℝ^5) :
    (∂[0] polynomialOddWave) (timeSpaceCons 0 x) = x 1 ^ 3 := by
  simpa [timeSpaceCons] using partialDeriv_polynomialOddWave_time (timeSpaceCons 0 x)

/-- The polynomial satisfies the residual equation and both Cauchy data. -/
theorem polynomialOddWave_satisfiesResidualAssignedCauchyData :
    SatisfiesPDEProblem
      (waveResidualAssignedCauchyDataProblem (n := 5)
        (fun x ↦ x 0 ^ 4) (fun x ↦ x 1 ^ 3)) polynomialOddWave := by
  refine forcedWaveResidualAssignedCauchyDataProblem.of_residual_initial ?_ ?_ ?_
  · intro p _
    exact waveOperator_polynomialOddWave p
  · intro p hp
    simp [polynomialOddWave, hp, spatialPartCLM_apply]
  · intro p hp
    have he := timeSpaceCons_spatialPartCLM p
    rw [hp] at he
    have hi := partialDeriv_polynomialOddWave_initial (spatialPartCLM 5 p)
    rw [he] at hi
    exact hi

/-- The odd-dimensional solution formula equals the polynomial at every nonnegative time. -/
theorem oddWaveSolution_eq_polynomial
    (x : ℝ^5) {t : ℝ} (ht : 0 ≤ t) :
    oddWaveSolution 1 (fun y ↦ y 0 ^ 4) (fun y ↦ y 1 ^ 3) (timeSpaceCons t x) =
      polynomialOddWave (timeSpaceCons t x) := by
  exact (eq_oddWaveSolution_of_satisfiesResidualAssignedCauchyData 1
    (by fun_prop) (by fun_prop) (contDiff_polynomialOddWave 2)
    polynomialOddWave_satisfiesResidualAssignedCauchyData ht x).symm

/-- Evans's representation formula (31) equals the polynomial for `t > 0`. -/
theorem evansOddDimensionalFormula_one_eq_polynomial
    (x : ℝ^5) (t : Set.Ioi (0 : ℝ)) :
    evansOddDimensionalFormula 1 (fun y ↦ y 0 ^ 4) (fun y ↦ y 1 ^ 3) x t =
      x 0 ^ 4 + 6 * (t : ℝ) ^ 2 * x 0 ^ 2 + (t : ℝ) ^ 4 +
        (t : ℝ) * x 1 ^ 3 + (t : ℝ) ^ 3 * x 1 := by
  rw [← oddWaveSolution_eq_evansOddDimensionalFormula 1 (by fun_prop),
    oddWaveSolution_eq_polynomial x t.property.le]
  simp [polynomialOddWave, timeSpaceCons]

end WaveEquation.Examples
