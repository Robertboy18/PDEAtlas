/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace

/-!
# Bessel potential spaces as distributions

The inclusion into tempered distributions is continuous for every real order and every
exponent `p ≥ 1`. Applying the inverse Bessel potential to the stored `Lp` representative
gives this inclusion directly, including at negative orders.
-/

@[expose] public noncomputable section

namespace BesselPotentialSpace

open MeasureTheory TemperedDistribution
open scoped BesselPotentialSpace ENNReal SchwartzMap

variable (E F : Type*) [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℂ F] [CompleteSpace F]
  (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The canonical continuous inclusion of a Bessel potential space into tempered distributions. -/
def toDistrCLM : H^{s, p}(E, F) →L[ℂ] 𝓢'(E, F) :=
  (besselPotential E F (-s)).comp
    ((Lp.toTemperedDistributionCLM F volume p).comp
      (toLpₗᵢ E F s p).toContinuousLinearEquiv.toContinuousLinearMap)

/-- The continuous inclusion returns the distribution already carried by the Sobolev element. -/
@[simp]
theorem toDistrCLM_apply (u : H^{s, p}(E, F)) :
    toDistrCLM E F s p u = u.toDistr := by
  simp [toDistrCLM]

/-- Convergence in a Bessel potential norm implies convergence as tempered distributions. -/
@[fun_prop]
theorem continuous_toDistr : Continuous (toDistr : H^{s, p}(E, F) → 𝓢'(E, F)) := by
  exact (toDistrCLM E F s p).continuous.congr (toDistrCLM_apply E F s p)

end BesselPotentialSpace
