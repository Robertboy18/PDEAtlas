/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.Models.Wave.Duhamel.EvenDimensions.Equation
public import PDE.Hyperbolic.Models.Wave.Duhamel.EvenDimensions.InitialTrace
public import PDE.Hyperbolic.Models.Wave.Duhamel.EvenDimensions.Representation

/-!
# The classical nonhomogeneous wave in even dimensions

In dimension `2k+2`, forward `C^(k+2)` forcing gives the retarded solution
with its forced residual and zero Cauchy data. The construction
and trace modules prove joint `C²` regularity through zero and both joint traces.

The regularity is local up to the closure. This is Evans, §2.4.2, Theorem 4, for even `n`, where
`⌊n/2⌋ + 1 = k + 2`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.2, equation (41) and Theorem 4.
  <https://doi.org/10.1090/gsm/019>
-/

open PDE (SatisfiesPDEProblem)

@[expose] public noncomputable section

namespace WaveEquation

open PDE.Analysis PDE.Common

/-- The even-dimensional formula satisfies the forced problem under
the exact finite-order forward-source hypothesis. -/
theorem evenDuhamelSolution_satisfiesResidualAssignedCauchyData (k : ℕ) {f : ℝ^(2 * k + 2 + 1) → ℝ}
    (hf : ContDiffOn ℝ (k + 2) f {p | 0 ≤ p 0}) :
    SatisfiesPDEProblem (forcedWaveResidualAssignedCauchyDataProblem (n := 2 * k + 2) f (fun _ ↦ 0)
      (fun _ ↦ 0)) (evenDuhamelSolution k f) := by
  refine forcedWaveResidualAssignedCauchyDataProblem.of_residual_initial ?_ ?_ ?_
  · exact fun p hp ↦ waveOperator_evenDuhamelSolution k hf hp.le
  · intro p hp
    have he := timeSpaceCons_spatialPartCLM p
    rw [hp] at he
    have hi := evenDuhamelSolution_initial k f (spatialPartCLM (2 * k + 2) p)
    rwa [he] at hi
  · intro p hp
    have he := timeSpaceCons_spatialPartCLM p
    rw [hp] at he
    have hi := partialDeriv_evenDuhamelSolution_initial k hf (spatialPartCLM (2 * k + 2) p)
    rwa [he] at hi

end WaveEquation
