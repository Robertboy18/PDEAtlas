/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.Dilation

/-!
# Reflection of the spectral Hilbert transform

The Hilbert symbol is odd, so reflection anticommutes with the concrete `L²`
Hilbert transform. The Fourier change of variables is the dilation identity
`fourier_complexL2Dilation` at scale `-1`.
-/

@[expose] public section

noncomputable section

open FourierTransform MeasureTheory
open scoped FourierTransform

namespace PDE.Analysis

/-- The Hilbert symbol changes sign under frequency reflection, also at zero. -/
theorem hilbertSymbol_neg (ξ : ℝ) : hilbertSymbol (-ξ) = -hilbertSymbol ξ := by
  rcases lt_trichotomy ξ 0 with hξ | rfl | hξ
  · rw [hilbertSymbol_of_neg hξ, hilbertSymbol_of_pos (neg_pos.mpr hξ)]
  · simp
  · rw [hilbertSymbol_of_pos hξ, hilbertSymbol_of_neg (neg_neg_of_pos hξ), neg_neg]

/-- Reflection anticommutes with multiplication by the Hilbert symbol. -/
theorem hilbertMultiplier_complexL2Dilation_neg_one (f : ComplexL2) :
    hilbertMultiplier (complexL2Dilation (-1) (by norm_num) f) =
      -(complexL2Dilation (-1) (by norm_num) (hilbertMultiplier f)) := by
  apply Lp.ext
  filter_upwards [coe_hilbertMultiplier (complexL2Dilation (-1) (by norm_num) f),
    coe_complexL2Dilation (-1) (by norm_num) f,
    Lp.coeFn_neg (complexL2Dilation (-1) (by norm_num) (hilbertMultiplier f)),
    coe_complexL2Dilation (-1) (by norm_num) (hilbertMultiplier f),
    (quasiMeasurePreserving_real_dilation (c := -1) (by norm_num)).ae_eq_comp
      (coe_hilbertMultiplier f)] with ξ hmult hdil hneg hright hcomp
  simp only [Function.comp_apply, neg_one_mul, hilbertSymbol_neg] at hcomp
  rw [hmult, hdil, hneg, Pi.neg_apply, hright]
  simp only [hcomp, neg_mul, neg_neg, one_mul]

/-- Reflection anticommutes with the spectral Hilbert transform. -/
theorem hilbertTransform_complexL2Dilation_neg_one (f : ComplexL2) :
    hilbertTransform (complexL2Dilation (-1) (by norm_num) f) =
      -(complexL2Dilation (-1) (by norm_num) (hilbertTransform f)) := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  change 𝓕 (hilbertTransform (complexL2Dilation (-1) (by norm_num) f)) =
    𝓕 (-(complexL2Dilation (-1) (by norm_num) (hilbertTransform f)))
  rw [fourier_hilbertTransform, FourierTransform.fourier_neg, fourier_complexL2Dilation,
    fourier_complexL2Dilation, fourier_hilbertTransform]
  simpa using hilbertMultiplier_complexL2Dilation_neg_one (𝓕 f)

end PDE.Analysis
