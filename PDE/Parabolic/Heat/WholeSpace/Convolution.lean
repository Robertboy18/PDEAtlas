/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.Semigroup
public import PDE.Parabolic.Heat.Fourier.Representation
public import PDE.Parabolic.Heat.Kernel.Integrability
public import PDE.Analysis.Fourier.L2Compatibility
public import PDE.Analysis.Integration.ConvolutionL2

/-!
# Gaussian Bochner convolution is the physical Fourier heat operator

The known Fourier integral formula proves equality for integrable L² data.
Density then removes integrability of the datum. This identifies the abstract
L² Fourier construction with the actual Gaussian average of spatial translations.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform PDE.Analysis
open scoped ENNReal NNReal Topology Convolution SchwartzMap

namespace HeatEquation.WholeSpace

variable {n : ℕ}

/-- Complexification of scalar real Lebesgue L². -/
def complexifyRealL2 (n : ℕ) :
    Lp ℝ 2 (volume : Measure (ℝ^n)) →L[ℝ] Lp ℂ 2 (volume : Measure (ℝ^n)) :=
  Complex.ofRealCLM.compLpL 2 volume

/-- Actual Gaussian heat convolution as a bounded operator on real L². -/
def heatConvolutionRealL2 (n : ℕ) (t : ℝ) (ht : 0 < t) :
    Lp ℝ 2 (volume : Measure (ℝ^n)) →L[ℝ] Lp ℝ 2 (volume : Measure (ℝ^n)) :=
  convolutionL2CLM (fun x ↦ fundamentalSolutionHeat (n := n) x t)
    (fundamentalSolutionHeat_integrable t ht)

theorem heatSymbol_eq_fourierMultiplier (t : ℝ≥0) (ξ : ℝ^n) :
    heatSymbol n t ξ = fourierMultiplier (t : ℝ) ξ := by
  unfold heatSymbol fourierMultiplier
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

private theorem convolution_eq_initialValueSolution (t : ℝ) (ht : 0 < t)
    (u : ℝ^n → ℝ) (x : ℝ^n) :
    ((fun y ↦ fundamentalSolutionHeat (n := n) y t) ⋆ u) x =
      initialValueSolution u x t := by
  change (∫ y, fundamentalSolutionHeat y t * u (x - y)) = _
  rw [← integral_sub_left_eq_self (μ := (volume : Measure (ℝ^n))) _ x]
  simp only [sub_sub_self]
  rw [initialValueSolution, ite_eq_right ht.not_ge]

private theorem heatL2_complexify_eq_convolution_of_integrable (t : ℝ≥0)
    (ht : 0 < (t : ℝ)) (u : Lp ℝ 2 (volume : Measure (ℝ^n))) (hu : Integrable u) :
    heatL2 n t (complexifyRealL2 n u) =
      complexifyRealL2 n (heatConvolutionRealL2 n (t : ℝ) ht u) := by
  let g : ℝ^n → ℂ := fun x ↦ (u x : ℂ)
  have hg : Integrable g := Complex.ofRealCLM.integrable_comp hu
  have hgAE : g =ᵐ[volume] (complexifyRealL2 n u : ℝ^n → ℂ) :=
    (Complex.ofRealCLM.coeFn_compLpL u).symm
  have hfourier := PDE.Analysis.Fourier.fourierIntegral_eq_L2_ae hg
    (complexifyRealL2 n u) hgAE
  have hsymbolAE : ⇑(heatSymbolLinf n t) =ᵐ[volume] heatSymbol n t :=
    (memLp_top_heatSymbol (n := n) t).coeFn_toLp
  have hprodAE : (fun ξ ↦ fourierMultiplier (t : ℝ) ξ * 𝓕 g ξ) =ᵐ[volume]
      (heatSymbolLinf n t • 𝓕 (complexifyRealL2 n u) : Lp ℂ 2 volume) := by
    filter_upwards [hfourier, hsymbolAE,
      Lp.coeFn_lpSMul (r := 2) (heatSymbolLinf n t) (𝓕 (complexifyRealL2 n u))]
      with ξ hF hsymbol hmul
    rw [hmul, Pi.smul_apply', smul_eq_mul, hsymbol, hF,
      heatSymbol_eq_fourierMultiplier]
  have hinverse := PDE.Analysis.Fourier.fourierInvIntegral_eq_L2_ae
    (integrable_fourierMultiplier_mul hg ht)
    (heatSymbolLinf n t • 𝓕 (complexifyRealL2 n u) : Lp ℂ 2 volume) hprodAE
  rw [← PDE.Analysis.Fourier.fourierMultiplierL2_apply] at hinverse
  change (fourierSolution g · (t : ℝ)) =ᵐ[volume]
    (heatL2 n t (complexifyRealL2 n u) : ℝ^n → ℂ) at hinverse
  apply Lp.ext
  have hconv := convolutionL2CLM_ae_eq
    (fun x ↦ fundamentalSolutionHeat (n := n) x (t : ℝ))
    (fundamentalSolutionHeat_integrable (t : ℝ) ht) u
  filter_upwards [hinverse,
    Complex.ofRealCLM.coeFn_compLpL (heatConvolutionRealL2 n (t : ℝ) ht u), hconv]
    with x hInv hcx hconv
  change complexifyRealL2 n (heatConvolutionRealL2 n (t : ℝ) ht u) x =
    (heatConvolutionRealL2 n (t : ℝ) ht u x : ℂ) at hcx
  change heatConvolutionRealL2 n (t : ℝ) ht u x = _ at hconv
  rw [← hInv, hcx]
  rw [fourierSolution_ofReal_eq_initialValueSolution hu x ht]
  exact congrArg Complex.ofReal
    ((convolution_eq_initialValueSolution (t : ℝ) ht u x).symm.trans hconv.symm)

/-- Gaussian convolution agrees with the actual Fourier heat evolution for every real L² datum. -/
theorem heatL2_complexify_eq_convolution (t : ℝ≥0) (ht : 0 < (t : ℝ))
    (u : Lp ℝ 2 (volume : Measure (ℝ^n))) :
    heatL2 n t (complexifyRealL2 n u) =
      complexifyRealL2 n (heatConvolutionRealL2 n (t : ℝ) ht u) := by
  have hEq := (SchwartzMap.denseRange_toLpCLM (E := ℝ^n) (F := ℝ)
    (p := 2) (μ := (volume : Measure (ℝ^n))) ENNReal.ofNat_ne_top).equalizer
      ((heatL2 n t).continuous.comp (complexifyRealL2 n).continuous)
      ((complexifyRealL2 n).continuous.comp (heatConvolutionRealL2 n (t : ℝ) ht).continuous)
      (by
        funext φ
        apply heatL2_complexify_eq_convolution_of_integrable t ht
        exact φ.integrable.congr (φ.coeFn_toLp 2 volume).symm)
  exact congrFun hEq u

end HeatEquation.WholeSpace
