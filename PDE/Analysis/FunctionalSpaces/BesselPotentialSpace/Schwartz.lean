/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace

/-!
# Schwartz functions in Bessel potential spaces

Convergence in Schwartz space implies convergence in every Bessel potential norm.
The inclusion is the composition of the Bessel Fourier multiplier, the inclusion
into `Lp`, and Mathlib's inverse Bessel isometry. This keeps the same distribution
as the original Schwartz function.
-/

@[expose] public noncomputable section

namespace SchwartzMap

open MeasureTheory BesselPotentialSpace TemperedDistribution
open scoped BesselPotentialSpace ENNReal SchwartzMap

variable (E F : Type*) [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℂ F] [CompleteSpace F]
  (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The canonical continuous inclusion of Schwartz functions into a Bessel potential space. -/
def toBesselPotentialSpaceCLM : 𝓢(E, F) →L[ℂ] H^{s, p}(E, F) :=
  (toLpₗᵢ E F s p).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((toLpCLM ℂ F p volume).comp
      (fourierMultiplierCLM F (fun x : E ↦
        Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (s / 2)))))

/-- The continuous inclusion agrees with the Sobolev element supplied by Mathlib. -/
@[simp]
theorem toBesselPotentialSpaceCLM_apply (f : 𝓢(E, F)) :
    toBesselPotentialSpaceCLM E F s p f =
      (memSobolev (s := s) (p := p) f).toBesselPotentialSpace := by
  apply BesselPotentialSpace.ext
  simp only [toBesselPotentialSpaceCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    toLpₗᵢ_symm_apply, toLpCLM_apply,
    TemperedDistribution.MemSobolev.toBesselPotentialSpace_toDistr]
  rw [besselPotential_neg_apply_eq_iff]
  rw [besselPotential, Lp.toTemperedDistribution_toLp_eq,
    TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop)]

/-- Schwartz convergence controls every real Bessel potential order and every `p ≥ 1`. -/
@[fun_prop]
theorem continuous_toBesselPotentialSpace :
    Continuous (fun f : 𝓢(E, F) ↦
      (memSobolev (s := s) (p := p) f).toBesselPotentialSpace) :=
  (toBesselPotentialSpaceCLM E F s p).continuous.congr
    (toBesselPotentialSpaceCLM_apply E F s p)

end SchwartzMap
