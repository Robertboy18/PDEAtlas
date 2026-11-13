/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Strichartz.NewtonIdentification
public import PDE.Hyperbolic.Models.Wave.Strichartz.KirchhoffNewton
public import PDE.Hyperbolic.Models.Wave.Strichartz.CosineCauchy
public import PDE.Hyperbolic.Models.Wave.Kirchhoff.ClassicalSolution
import PDE.Elliptic.PotentialTheory.FundamentalSolution.LocalIntegrability

/-!
# Fourier identification of the Newtonian wave kernel

Cauchy uniqueness identifies the inverse Fourier cosine evolution of
Newton data with the Kirchhoff formula. The physical exterior Newtonian kernel
then follows at every nonzero signed time, with its exact normalization.
All regularity and initial traces come from the compact Schwartz source.
-/

@[expose] public section

open MeasureTheory FourierTransform PDE.Common
open scoped SchwartzMap

namespace WaveEquation.Strichartz

/-- The Fourier cosine evolution of Newton data equals its Kirchhoff evolution
at every signed time. All regularity and initial traces are derived from the source. -/
theorem re_cosine_wave_newtonFrequency_eq_kirchhoffFormula
    (f : 𝓢(ℝ^3, ℝ)) (hfc : HasCompactSupport (f : ℝ^3 → ℝ)) (t : ℝ) (x : ℝ^3) :
    (Fourier.waveSolution (newtonFrequency (𝓕 (f.postcompCLM Complex.ofRealCLM))) 0 (t, x)).re =
      kirchhoffFormula (convolution (PotentialTheory.fundamentalSolution 3) f
        (ContinuousLinearMap.mul ℝ ℝ)) (fun _ ↦ 0) x t := by
  let F := 𝓕 (f.postcompCLM Complex.ofRealCLM)
  let G := newtonFrequency F
  let v := convolution (PotentialTheory.fundamentalSolution 3) f (ContinuousLinearMap.mul ℝ ℝ)
  have hG : Integrable G := integrable_newtonFrequency F
  have hG₁ : Integrable (fun ξ ↦ ‖ξ‖ * ‖G ξ‖) := integrable_norm_mul_newtonFrequency F
  have hG₂ : Integrable (fun ξ ↦ ‖ξ‖ ^ 2 * ‖G ξ‖) := integrable_norm_sq_mul_newtonFrequency F
  have hinit : (fun y ↦ (𝓕⁻ G y).re) = v :=
    funext (re_fourierInv_newtonFrequency_eq_convolution f hfc)
  have hv : ContDiff ℝ 3 v := hfc.contDiff_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) (PotentialTheory.locallyIntegrable_fundamentalSolution 3)
    (f.smooth 3)
  have hsol := Fourier.realCosineSolution_satisfiesResidualAssignedCauchyData hG hG₁ hG₂
  rw [hinit] at hsol
  have he := eq_on_nonnegative_time_of_satisfiesResidualAssignedCauchyData
    (Fourier.contDiff_two_realCosineSolution hG hG₁ hG₂)
    (contDiff_two_kirchhoffFormula hv contDiff_const) hsol
    (kirchhoffFormula_satisfiesResidualAssignedCauchyData hv contDiff_const) (abs_nonneg t) x
  have hpos : (Fourier.waveSolution G 0 (|t|, x)).re =
      kirchhoffFormula v (fun _ ↦ 0) x |t| := by
    simpa only [Fourier.realCosineSolution, Function.comp_apply,
      timeSpaceContinuousLinearEquiv_apply, PDE.time, timeSpaceCons_zero,
      spatialPart_timeSpaceCons, Complex.reCLM_apply, spaceTimeUncurry] using he
  have heven : Fourier.waveSolution G 0 (t, x) = Fourier.waveSolution G 0 (|t|, x) := by
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · simp only [abs_of_nonpos ht, Fourier.waveSolution, Fourier.waveValue,
        mul_neg, Real.cos_neg, Pi.zero_apply, smul_zero, add_zero]
  change (Fourier.waveSolution G 0 (t, x)).re = kirchhoffFormula v (fun _ ↦ 0) x t
  rw [heven, hpos]
  simp only [kirchhoffFormula, abs_abs, mul_zero]

/-- The Fourier multiplier and physical exterior Newtonian kernel coincide at every
nonzero signed time, including the exact factor `1/(4π)`. -/
theorem re_cosine_wave_newtonFrequency_eq_exteriorNewtonKernel (f : 𝓢(ℝ^3, ℝ))
    (hfc : HasCompactSupport (f : ℝ^3 → ℝ)) {t : ℝ} (ht : t ≠ 0) (x : ℝ^3) :
    (Fourier.waveSolution (newtonFrequency (𝓕 (f.postcompCLM Complex.ofRealCLM))) 0 (t, x)).re =
      (4 * Real.pi)⁻¹ * ∫ y, exteriorNewtonKernel |t| (x - y) * f y := by
  rw [re_cosine_wave_newtonFrequency_eq_kirchhoffFormula f hfc]
  exact kirchhoffFormula_convolution_fundamentalSolution (f.smooth 1) hfc x ht

end WaveEquation.Strichartz
