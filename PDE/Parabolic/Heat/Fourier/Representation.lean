/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Fourier.Inversion
public import PDE.Parabolic.Heat.InitialValue
import CAS.ExactTactic

/-!
# Fourier representation of heat evolution

The Fourier convention is `exp (-2πi ⟪ξ,x⟫)`, so the heat multiplier is
`exp (-4π²t ‖ξ‖²)`. Gaussian integration and the integrable Fourier pairing
identify its inverse transform with the heat-kernel convolution.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace HeatEquation

variable {n : ℕ}

/-- The heat evolution multiplier for the Fourier convention with phase `-2πi ⟪ξ,x⟫`. -/
def fourierMultiplier (t : ℝ) (ξ : ℝ^n) : ℂ :=
  Complex.exp (-(4 * Real.pi ^ 2 * t : ℝ) * (‖ξ‖ : ℂ) ^ 2)

/-- The inverse Fourier heat formula, as a total complex-valued expression.
Analytic solution claims below concern nonnegative time. -/
def fourierSolution (g : ℝ^n → ℂ) (x : ℝ^n) (t : ℝ) : ℂ :=
  𝓕⁻ (fun ξ ↦ fourierMultiplier t ξ * 𝓕 g ξ) x

/-- Gaussian decay makes the evolved Fourier data integrable at every positive time,
even when the Fourier transform of the initial datum is not integrable. -/
theorem integrable_fourierMultiplier_mul {g : ℝ^n → ℂ} (hg : Integrable g)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun ξ ↦ fourierMultiplier t ξ * 𝓕 g ξ) := by
  have hb : 0 < (4 * Real.pi ^ 2 * t : ℝ) := by positivity
  have hM : Integrable (fourierMultiplier t : ℝ^n → ℂ) := by
    unfold fourierMultiplier
    simpa only [zero_mul, add_zero] using
      (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
        (b := ((4 * Real.pi ^ 2 * t : ℝ) : ℂ)) (by exact hb) 0 (0 : ℝ^n))
  exact hM.mul_bdd
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hg).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ ↦
      VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ g ξ)

private theorem fourier_heatPhase {t : ℝ} (ht : 0 < t) (x y : ℝ^n) :
    𝓕 (fun ξ : ℝ^n ↦ Complex.exp
      (-(4 * Real.pi ^ 2 * t : ℝ) * (‖ξ‖ : ℂ) ^ 2 +
        2 * Real.pi * Complex.I * ⟪x, ξ⟫)) y =
      (fundamentalSolutionHeat (x - y) t : ℂ) := by
  have hb : 0 < (4 * Real.pi ^ 2 * t : ℝ) := by positivity
  rw [fourier_gaussian_innerProductSpace' (b := ((4 * Real.pi ^ 2 * t : ℝ) : ℂ))
    (by exact hb)]
  have hscale : Real.pi / (4 * Real.pi ^ 2 * t) = (4 * Real.pi * t)⁻¹ := by
    have hπ := Real.pi_ne_zero
    cas using ht.ne'
  have hexp : -Real.pi ^ 2 * ‖x - y‖ ^ 2 / (4 * Real.pi ^ 2 * t) =
      -(‖x - y‖ ^ 2 / (4 * t)) := by
    have hπ := Real.pi_ne_zero
    cas using ht.ne'
  simp only [fundamentalSolutionHeat, ite_eq_right ht.not_ge, Complex.ofReal_mul,
    Complex.ofReal_exp]
  congr 1
  · rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_div, hscale]
    rw [show (Module.finrank ℝ (ℝ^n) : ℂ) / 2 = ((n : ℝ) / 2 : ℝ) by simp]
    rw [← Complex.ofReal_cpow (by positivity), ← Real.rpow_neg_eq_inv_rpow]
    congr 1
    congr 1
    cas
  · congr 1
    exact_mod_cast hexp

/-- At positive time the inverse Fourier heat formula is the Gaussian convolution.
Only integrability of the initial datum is needed for this representation identity. -/
theorem fourierSolution_eq_integral {g : ℝ^n → ℂ} (hg : Integrable g)
    (x : ℝ^n) {t : ℝ} (ht : 0 < t) :
    fourierSolution g x t =
      ∫ y : ℝ^n, (fundamentalSolutionHeat (x - y) t : ℂ) * g y := by
  let P : ℝ^n → ℂ := fun ξ ↦ Complex.exp
    (-(4 * Real.pi ^ 2 * t : ℝ) * (‖ξ‖ : ℂ) ^ 2 +
      2 * Real.pi * Complex.I * ⟪x, ξ⟫)
  have hb : 0 < (4 * Real.pi ^ 2 * t : ℝ) := by positivity
  have hP : Integrable P :=
    GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (b := ((4 * Real.pi ^ 2 * t : ℝ) : ℂ)) (by exact hb) _ _
  calc
    fourierSolution g x t = ∫ ξ : ℝ^n, P ξ * 𝓕 g ξ := by
      rw [fourierSolution, Real.fourierInv_eq']
      apply integral_congr_ae
      exact ae_of_all _ fun ξ ↦ by
        simp only [fourierMultiplier, smul_eq_mul, P, ← mul_assoc, ← Complex.exp_add]
        congr 2
        rw [real_inner_comm ξ x]
        push_cast
        ring
    _ = ∫ y : ℝ^n, 𝓕 P y * g y := by
      simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip
        (L := innerₗ (ℝ^n)) Real.continuous_fourierChar continuous_inner hP hg).symm
    _ = _ := by simp_rw [P, fourier_heatPhase ht]

/-- For real integrable data the positive-time inverse Fourier formula is real
and agrees with the Gaussian heat evolution. -/
theorem fourierSolution_ofReal_eq_initialValueSolution
    {g : ℝ^n → ℝ} (hg : Integrable g) (x : ℝ^n) {t : ℝ} (ht : 0 < t) :
    fourierSolution (fun y ↦ (g y : ℂ)) x t = (initialValueSolution g x t : ℂ) := by
  have hgC : Integrable (fun y ↦ (g y : ℂ)) :=
    Complex.ofRealCLM.integrable_comp hg
  rw [fourierSolution_eq_integral hgC x ht, initialValueSolution, ite_eq_right ht.not_ge]
  simp only [← Complex.ofReal_mul, integral_complex_ofReal]

/-- Fourier inversion recovers the assigned initial datum whenever both it and
its Fourier transform are integrable and the datum is continuous at the point. -/
theorem fourierSolution_initial_value {g : ℝ^n → ℂ} (hg : Integrable g)
    (hfg : Integrable (𝓕 g)) {x : ℝ^n} (hx : ContinuousAt g x) :
    fourierSolution g x 0 = g x := by
  simpa only [fourierSolution, fourierMultiplier, mul_zero, Complex.ofReal_zero,
    neg_zero, zero_mul, Complex.exp_zero, one_mul] using hg.fourierInv_fourier_eq hfg hx

end HeatEquation
