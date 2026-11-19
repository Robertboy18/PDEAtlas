/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.Models.Wave.Duhamel.OneDimension.Equation
public import PDE.Hyperbolic.Models.Wave.Duhamel.OneDimension.InitialTrace

/-!
# Classical forced waves in one space dimension

Forward `C¹` forcing gives a `C²` solution with zero Cauchy data. The
construction uses the characteristic integral directly, so it needs neither
a second source derivative nor an extension of the forcing to negative time. Evans, §2.4.2,
Example (i), treats this case with formula (43).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.2, Example (i), equation (43).
  <https://doi.org/10.1090/gsm/019>
-/

open PDE (SatisfiesPDEProblem)

@[expose] public noncomputable section

namespace WaveEquation

open PDE.Common

/-- Duhamel's one-dimensional formula satisfies the forced PDE and both zero Cauchy data. -/
theorem dAlembertDuhamelSolution_satisfiesResidualAssignedCauchyData
    {f : ℝ^2 → ℝ} (hf : ContDiffOn ℝ 1 f {p | 0 ≤ p 0}) :
    SatisfiesPDEProblem (forcedWaveResidualAssignedCauchyDataProblem (n := 1) f (fun _ ↦ 0)
      (fun _ ↦ 0)) (dAlembertDuhamelSolution f) := by
  refine forcedWaveResidualAssignedCauchyDataProblem.of_residual_initial ?_ ?_ ?_
  · exact fun p hp ↦ waveOperator_dAlembertDuhamelSolution hf hp.le
  · intro p hp
    have he := timeSpaceCons_spatialPartCLM p
    rw [hp] at he
    have hi := dAlembertDuhamelSolution_initial f (spatialPartCLM 1 p)
    rwa [he] at hi
  · intro p hp
    have he := timeSpaceCons_spatialPartCLM p
    rw [hp] at he
    have hi := partialDeriv_dAlembertDuhamelSolution_initial hf (spatialPartCLM 1 p)
    rwa [he] at hi

end WaveEquation
