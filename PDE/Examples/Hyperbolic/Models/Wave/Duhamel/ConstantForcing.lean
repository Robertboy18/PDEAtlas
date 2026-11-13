/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.Models.Wave.Duhamel.OddDimensions.ClassicalSolution
import PDE.Analysis.Calculus.SpaceTime.ClosedSlab
import CAS.IntegrationTactic
import PDE.Symbolic.PDEDerivatives

/-!
# A constant forced wave in three dimensions

For a constant source `c` the Duhamel integral (41) of Evans, §2.4.2, is `c t²/2`. The Duhamel
theorem `oddDuhamelSolution_satisfiesResidualAssignedCauchyData` shows that it solves the forced
wave equation with zero Cauchy data, also when `c ≠ 0` at time zero.

For unit forcing the constructed field is not uniformly continuous on the forward half-space. This
records the obstruction to a global uniform-continuity reading of the closed-half-space regularity
`u ∈ C²(ℝⁿ × [0, ∞))` in Evans, §2.4.2, Theorem 4(i).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.2, (39)-(42) and Theorem 4 (Solution of
  nonhomogeneous wave equation), pp. 80-81.
  <https://doi.org/10.1090/gsm/019>
-/

open PDE (SatisfiesPDEProblem)

@[expose] public noncomputable section

namespace WaveEquation.Examples

open PDE.Analysis PDE.Common

/-- For constant forcing `c` the three-dimensional Duhamel integral is `c t²/2`, at every
real time `t`. -/
theorem oddDuhamelSolution_zero_constant (c : ℝ) (p : ℝ^4) :
    oddDuhamelSolution 0 (fun _ ↦ c) p = c * p 0 ^ 2 / 2 := by
  have hmean (x : ℝ^3) (r : ℝ) :
      unitSphereAverage 3 (fun _ ↦ c) x r = c := by
    calc
      _ = unitSphereAverage 3 (fun _ ↦ c) x 0 := rfl
      _ = c := unitSphereAverage_zero _ _
  change (Nat.doubleFactorial 1 : ℝ)⁻¹ *
    (∫ s in (0 : ℝ)..p 0, oddWavePotential 0 (fun _ ↦ c)
      (timeSpaceCons (p 0 - s) (spatialPartCLM 3 p))) = _
  simp only [Nat.doubleFactorial, Nat.cast_one, inv_one, one_mul,
    oddWavePotential_timeSpaceCons, oddSphericalProfile_zero, hmean]
  cas

/-- The Duhamel integral solves the forced wave equation with zero Cauchy data. -/
theorem constantDuhamel_satisfiesResidualAssignedCauchyData (c : ℝ) :
    SatisfiesPDEProblem
      (forcedWaveResidualAssignedCauchyDataProblem (n := 3)
        (fun _ ↦ c) (fun _ ↦ 0) (fun _ ↦ 0))
      (oddDuhamelSolution 0 (fun _ ↦ c)) :=
  oddDuhamelSolution_satisfiesResidualAssignedCauchyData 0 contDiff_const.contDiffOn

/-- The field for unit forcing fails uniform continuity on the whole
forward half-space. Arbitrarily close times can give a value difference above two. -/
theorem not_uniformContinuousOn_oddDuhamelSolution_zero_one :
    ¬ UniformContinuousOn (oddDuhamelSolution 0 (fun _ ↦ (1 : ℝ))) {p | 0 ≤ p 0} := by
  intro hu
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp hu 1 zero_lt_one
  have hδ0 : δ ≠ 0 := hδ.ne'
  have hstep : 4 / δ + δ / 2 - 4 / δ = δ / 2 := by
    cas using hδ0
  have hgap :
      (4 / δ + δ / 2) ^ 2 / 2 - (4 / δ) ^ 2 / 2 = 2 + δ ^ 2 / 8 := by
    cas using hδ0
  have hnear :
      dist (timeSpaceCons (4 / δ + δ / 2) (0 : ℝ^3))
        (timeSpaceCons (4 / δ) (0 : ℝ^3)) < δ := by
    rw [dist_eq_norm, norm_timeSpaceCons_sub_timeSpaceCons, hstep,
      Real.norm_eq_abs, abs_of_pos (half_pos hδ)]
    exact half_lt_self hδ
  have h := hclose
    (timeSpaceCons (4 / δ + δ / 2) (0 : ℝ^3))
    (by simp only [Set.mem_ofPred_eq, timeSpaceCons_zero]; positivity)
    (timeSpaceCons (4 / δ) (0 : ℝ^3))
    (by simp only [Set.mem_ofPred_eq, timeSpaceCons_zero]; positivity)
    hnear
  rw [oddDuhamelSolution_zero_constant, oddDuhamelSolution_zero_constant] at h
  simp only [timeSpaceCons_zero, one_mul, Real.dist_eq] at h
  rw [hgap, abs_of_pos (by positivity)] at h
  nlinarith [sq_nonneg δ]

-- The field without uniform continuity is the one the Duhamel theorem constructs.
example :
    ContDiff ℝ 2 (oddDuhamelSolution 0 (fun _ ↦ (1 : ℝ))) ∧
      SatisfiesPDEProblem
        (forcedWaveResidualAssignedCauchyDataProblem (n := 3)
          (fun _ ↦ (1 : ℝ)) (fun _ ↦ 0) (fun _ ↦ 0))
        (oddDuhamelSolution 0 (fun _ ↦ (1 : ℝ))) ∧
      ¬ UniformContinuousOn (oddDuhamelSolution 0 (fun _ ↦ (1 : ℝ))) {p | 0 ≤ p 0} :=
  ⟨contDiff_two_oddDuhamelSolution 0 contDiff_const.contDiffOn,
    constantDuhamel_satisfiesResidualAssignedCauchyData 1,
    not_uniformContinuousOn_oddDuhamelSolution_zero_one⟩

end WaveEquation.Examples
