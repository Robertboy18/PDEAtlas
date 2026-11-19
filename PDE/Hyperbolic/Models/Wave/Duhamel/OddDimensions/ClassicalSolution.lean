/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.Models.Wave.Duhamel.OddDimensions.Equation
public import PDE.Hyperbolic.Models.Wave.Duhamel.OddDimensions.InitialTrace

/-!
# The classical nonhomogeneous wave in odd dimensions

The retarded formula solves the forced wave problem with zero
initial data. In dimension `2k+3` the source is only required to be `C^(k+2)`
within the closed forward halfspace. Its values at negative times are unused.
The construction and initial-trace modules supply joint `C²` regularity and
both joint initial traces.

The regularity is local up to the closure. This is Evans, §2.4.2, Theorem 4, for odd `n ≥ 3`,
where `⌊n/2⌋ + 1 = k + 2`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.2, equation (41) and Theorem 4.
  <https://doi.org/10.1090/gsm/019>
-/

open PDE (SatisfiesPDEProblem)

@[expose] public noncomputable section

namespace WaveEquation

open PDE.Analysis PDE.Common

/-- On a forward interval the retarded formula uses the original forcing
index, with no extension or alteration of the source on that interval. -/
theorem oddDuhamelSolution_eq_integral (k : ℕ) (f : ℝ^(2 * k + 3 + 1) → ℝ) (x : ℝ^(2 * k + 3))
    {t : ℝ} (ht : 0 ≤ t) :
    oddDuhamelSolution k f (timeSpaceCons t x) = (Nat.doubleFactorial (2 * k + 1) : ℝ)⁻¹ *
      ∫ s in (0 : ℝ)..t,
      oddWavePotential k (fun y ↦ f (timeSpaceCons s y)) (timeSpaceCons (t - s) x) := by
  change (Nat.doubleFactorial (2 * k + 1) : ℝ)⁻¹ *
    (∫ s in (0 : ℝ)..t, oddWavePotential k (fun y ↦ f (timeSpaceCons (max 0 s) y))
      (timeSpaceCons (t - s) x)) = _
  congr 1
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  rw [Set.uIcc_of_le ht] at hs
  simp only [max_eq_right hs.1]

/-- The normalized potential integral is exactly the integral of the
homogeneous waves whose initial velocity is the forcing slice. -/
theorem oddDuhamelSolution_eq_integral_oddWaveSolution (k : ℕ) (f : ℝ^(2 * k + 3 + 1) → ℝ)
    (x : ℝ^(2 * k + 3)) {t : ℝ} (ht : 0 ≤ t) :
    oddDuhamelSolution k f (timeSpaceCons t x) = ∫ s in (0 : ℝ)..t, oddWaveSolution k (fun _ ↦ 0)
      (fun y ↦ f (timeSpaceCons s y)) (timeSpaceCons (t - s) x) := by
  have hradial : oddRadialTransform k (fun _ : ℝ ↦ 0) = fun _ ↦ 0 :=
    Function.iterate_fixed (show evansRadialDerivative (fun _ ↦ 0) = (fun _ ↦ 0) by
      funext r
      simp [evansRadialDerivative]) k
  have hzero : oddWavePotential k (fun _ ↦ 0) = fun _ ↦ 0 := by
    funext p
    simp [oddWavePotential, spaceTimeUncurry, oddSphericalProfile, unitSphereAverage, hradial]
  rw [oddDuhamelSolution_eq_integral k f x ht]
  simp only [oddWaveSolution, hzero, PDE.partialDeriv_const, zero_add,
    intervalIntegral.integral_const_mul]

/-- The constructed integral satisfies the forced residual and both
assigned Cauchy data under the exact finite-order forward-source hypothesis. -/
theorem oddDuhamelSolution_satisfiesResidualAssignedCauchyData (k : ℕ) {f : ℝ^(2 * k + 3 + 1) → ℝ}
    (hf : ContDiffOn ℝ (k + 2) f {p | 0 ≤ p 0}) :
    SatisfiesPDEProblem (forcedWaveResidualAssignedCauchyDataProblem (n := 2 * k + 3) f (fun _ ↦ 0)
      (fun _ ↦ 0)) (oddDuhamelSolution k f) := by
  refine forcedWaveResidualAssignedCauchyDataProblem.of_residual_initial ?_ ?_ ?_
  · exact fun p hp ↦ waveOperator_oddDuhamelSolution k hf hp.le
  · intro p hp
    have he := timeSpaceCons_spatialPartCLM p
    rw [hp] at he
    have hi := oddDuhamelSolution_initial k f (spatialPartCLM (2 * k + 3) p)
    rwa [he] at hi
  · intro p hp
    have he := timeSpaceCons_spatialPartCLM p
    rw [hp] at he
    have hi := partialDeriv_oddDuhamelSolution_initial k hf (spatialPartCLM (2 * k + 3) p)
    rwa [he] at hi

end WaveEquation
