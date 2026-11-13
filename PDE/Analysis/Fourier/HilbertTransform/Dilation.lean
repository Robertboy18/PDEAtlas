/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform
public import PDE.Analysis.MeasureTheory.Lp.Composition.Dilation
import PDE.Analysis.Fourier.UnitaryNormalization

/-!
# Dilation of the spectral Hilbert transform

Spatial dilation acts continuously on complex `L²(ℝ)`. Its Fourier transform is
the reciprocal dilation, multiplied by the change-of-variables Jacobian.
Positive dilation preserves the Hilbert symbol and therefore commutes with the
concrete spectral Hilbert transform.
-/

@[expose] public section

namespace PDE.Analysis

open FourierTransform MeasureTheory
open scoped FourierTransform SchwartzMap

noncomputable section

/-- Dilation preserves null sets, so it acts on almost-everywhere representatives. -/
theorem quasiMeasurePreserving_real_dilation {c : ℝ} (hc : c ≠ 0) :
    QuasiMeasurePreserving (fun x : ℝ ↦ c * x) volume volume :=
  Measure.quasiMeasurePreserving_smul volume hc

/-- The pullback `f(x) ↦ f(c x)` on complex `L²(ℝ)`: the one-dimensional case of
`MeasureTheory.Lp.compSMul`. -/
def complexL2Dilation (c : ℝ) (hc : c ≠ 0) : ComplexL2 →L[ℝ] ComplexL2 :=
  Lp.compSMul volume 2 c hc

/-- Representatives of the `L²` dilation agree almost everywhere with composition. -/
theorem coe_complexL2Dilation (c : ℝ) (hc : c ≠ 0) (f : ComplexL2) :
    complexL2Dilation c hc f =ᵐ[volume] fun x ↦ f (c * x) :=
  Lp.coeFn_compSMul volume 2 c hc f

/-- Fourier dilation on `L²`: the one-dimensional case of `Fourier.fourier_compSMul`. -/
theorem fourier_complexL2Dilation (c : ℝ) (hc : c ≠ 0) (f : ComplexL2) :
    𝓕 (complexL2Dilation c hc f) =
      |c⁻¹| • complexL2Dilation c⁻¹ (inv_ne_zero hc) (𝓕 f) := by
  simpa only [complexL2Dilation, Module.finrank_self, pow_one] using
    Fourier.fourier_compSMul c hc f

/-- A positive dilation leaves the sign of every frequency unchanged. -/
theorem hilbertSymbol_dilate {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    hilbertSymbol (c * ξ) = hilbertSymbol ξ := by
  simp [hilbertSymbol, mul_neg_iff, hc, not_lt_of_ge hc.le]

/-- Positive dilation commutes with multiplication by the Hilbert symbol. -/
theorem hilbertMultiplier_complexL2Dilation {c : ℝ} (hc : 0 < c) (f : ComplexL2) :
    hilbertMultiplier (complexL2Dilation c hc.ne' f) =
      complexL2Dilation c hc.ne' (hilbertMultiplier f) := by
  apply Lp.ext
  filter_upwards [coe_hilbertMultiplier (complexL2Dilation c hc.ne' f),
    coe_complexL2Dilation c hc.ne' f,
    coe_complexL2Dilation c hc.ne' (hilbertMultiplier f),
    (quasiMeasurePreserving_real_dilation hc.ne').ae_eq_comp
      (coe_hilbertMultiplier f)] with ξ hmult hdil hright hcomp
  simpa only [Function.comp_apply, hmult, hdil, hright, hilbertSymbol_dilate hc] using
    hcomp.symm

/-- The concrete spectral Hilbert transform commutes with every positive dilation. -/
theorem hilbertTransform_complexL2Dilation {c : ℝ} (hc : 0 < c) (f : ComplexL2) :
    hilbertTransform (complexL2Dilation c hc.ne' f) =
      complexL2Dilation c hc.ne' (hilbertTransform f) := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  change 𝓕 (hilbertTransform (complexL2Dilation c hc.ne' f)) =
    𝓕 (complexL2Dilation c hc.ne' (hilbertTransform f))
  rw [fourier_hilbertTransform, fourier_complexL2Dilation, fourier_complexL2Dilation,
    fourier_hilbertTransform]
  calc
    _ = |c⁻¹| • hilbertMultiplier
        (complexL2Dilation c⁻¹ (inv_ne_zero hc.ne') (𝓕 f)) :=
      hilbertMultiplier.map_smul_of_tower _ _
    _ = _ := congrArg (fun g : ComplexL2 ↦ |c⁻¹| • g)
      (hilbertMultiplier_complexL2Dilation (inv_pos.mpr hc) (𝓕 f))

end

end PDE.Analysis
