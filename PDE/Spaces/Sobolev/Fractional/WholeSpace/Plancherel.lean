/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Definitions

/-!
# The Fourier description of the fractional Sobolev norm

`BesselPotentialSpace.norm_toLp_eq` describes the `H^s` norm on the
physical side, as the `L²` norm of the Bessel representative.  On the Fourier
side,

`‖u‖_{H^s} = ‖(1 + ‖ξ‖²) ^ (s/2) · 𝓕 u‖_{L²}`,

where the symbol times the distributional `𝓕 u` is the `L²` function
`𝓕 (toLp u)` (`smulLeftCLM_fourier_toDist`), whose norm is `‖u‖` by Mathlib's
`BesselPotentialSpace.norm_fourier_toLp_eq`.

Two Mathlib results do the work: `fourier_besselPotential_eq_smulLeftCLM_fourier_apply`
turns the Bessel potential into multiplication by the symbol on the Fourier side,
and `MeasureTheory.Lp.fourier_toTemperedDistribution_eq` says the `L²` Fourier
transform agrees with the distributional one.  Plancherel
(`MeasureTheory.Lp.norm_fourier_eq`) then transports the norm.

As noted in `Fractional.WholeSpace.Definitions`, the symbol is
`(1 + ‖ξ‖²) ^ (s/2)`, corresponding to `(1 - (2π)^{-2} Δ) ^ (s/2)` and not to
`(1 - Δ) ^ (s/2)`.

The Fourier representative is Mathlib's `𝓕 (BesselPotentialSpace.toLp u)`;
we use it directly throughout the fractional-space theory.

## Main definitions

* `SobolevSpace.Fractional.besselSymbol`: the symbol `(1 + ‖ξ‖²) ^ (s/2)`.

## Main statements

* `SobolevSpace.Fractional.smulLeftCLM_fourier_toDist`: the symbol times `𝓕 u`
  is represented by `𝓕 (toLp u)`.
-/

@[expose] public section

open TemperedDistribution MeasureTheory FourierTransform
open scoped BesselPotentialSpace ENNReal SchwartzMap

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ}

open BesselPotentialSpace

/-- The Bessel symbol `(1 + ‖ξ‖²) ^ (s/2)` of order `s`, as a complex-valued
function on frequency space. -/
noncomputable def besselSymbol (n : ℕ) (s : ℝ) : ℝ^n → ℂ :=
  fun x ↦ ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ)

/-- Multiplying `𝓕 u` by the Bessel symbol is represented by `𝓕 (toLp u)`.

This is the precise sense in which `u` lies in `H^s` exactly when
`(1 + ‖ξ‖²) ^ (s/2) 𝓕 u` is square integrable. -/
theorem smulLeftCLM_fourier_toDist (u : H^{s}(ℝ^n)) :
    smulLeftCLM ℂ (besselSymbol n s) (𝓕 (toDistr u))
      = ((𝓕 (toLp u) : Lp ℂ 2 (volume : Measure (ℝ^n))) : 𝓢'(ℝ^n, ℂ)) := by
  have h := fourier_besselPotential_eq_smulLeftCLM_fourier_apply
    (E := ℝ^n) (F := ℂ) s (toDistr u)
  rw [bessel_toDistr_eq_toLp, MeasureTheory.Lp.fourier_toTemperedDistribution_eq] at h
  exact h.symm

end SobolevSpace.Fractional
