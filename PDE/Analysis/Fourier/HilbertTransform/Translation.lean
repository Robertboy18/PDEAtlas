/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform
import PDE.Spaces.Sobolev.Fractional.WholeSpace.Translation
import CAS.ExactTactic

/-!
# Translation of the spectral Hilbert transform

The concrete `L²` Hilbert transform commutes with every translation of the real line. The
translation `f ↦ f (· + a)` of complex `L²(ℝ)` is Mathlib's `Lp.compMeasurePreserving` along
`x ↦ x + a`.

## Main results

* `PDE.Analysis.hilbertTransform_compMeasurePreserving_add_right`: for every real `a` and every
  `f` in complex `L²(ℝ)`, the Hilbert transform of `f (· + a)` is the Hilbert transform of `f`,
  translated by `a`.

## How it works

The Fourier transform turns the translation by `a` into multiplication by the character
`ξ ↦ e^{2πi a ξ}` (`SobolevSpace.Fractional.fourier_compMeasurePreserving_add_right` on
`L²(ℝ; ℂ)`). Multiplication by a character commutes with multiplication by the symbol
`-i sgn ξ` of the Hilbert transform.

The statement is a standard fact on the Hilbert transform, and the proof follows no particular
source.
-/

@[expose] public section

noncomputable section

open FourierTransform MeasureTheory
open SobolevSpace.Fractional (charMulL2 coeFn_charMulL2 fourier_compMeasurePreserving_add_right)

namespace PDE.Analysis

private theorem hilbertMultiplier_charMulL2 (a : ℝ) (g : ComplexL2) :
    hilbertMultiplier (charMulL2 a g) = charMulL2 a (hilbertMultiplier g) := by
  apply Lp.ext
  filter_upwards [coe_hilbertMultiplier (charMulL2 a g), coeFn_charMulL2 a g,
    coeFn_charMulL2 a (hilbertMultiplier g), coe_hilbertMultiplier g] with ξ h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]
  cas

/-- **The Hilbert transform commutes with translations.** For every real `a` and every `f` in
complex `L²(ℝ)`, the Hilbert transform of the translate `f (· + a)` is the translate of the
Hilbert transform of `f`. -/
theorem hilbertTransform_compMeasurePreserving_add_right (a : ℝ) (f : ComplexL2) :
    hilbertTransform
        (Lp.compMeasurePreserving (· + a) (measurePreserving_add_right volume a) f) =
      Lp.compMeasurePreserving (· + a) (measurePreserving_add_right volume a)
        (hilbertTransform f) := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  change 𝓕 (hilbertTransform
      (Lp.compMeasurePreserving (· + a) (measurePreserving_add_right volume a) f)) =
    𝓕 (Lp.compMeasurePreserving (· + a) (measurePreserving_add_right volume a)
      (hilbertTransform f))
  rw [fourier_hilbertTransform, fourier_compMeasurePreserving_add_right,
    fourier_compMeasurePreserving_add_right, fourier_hilbertTransform,
    hilbertMultiplier_charMulL2]

end PDE.Analysis
