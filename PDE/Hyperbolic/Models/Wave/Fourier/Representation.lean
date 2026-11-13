/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Fourier.Inversion
public import PDE.Hyperbolic.Models.Wave.DAlembert.Formula

/-!
# The one-dimensional wave Fourier representation

With Mathlib's `2π` convention, displacement evolves by `cos (2πξt)` and
velocity by `t sinc (2πξt)`. The latter equals `sin (2πξt) / (2πξ)` away
from zero frequency and has value `t` at zero frequency.

The inverse transform is identified with d'Alembert's formula by Fourier
inversion and Fubini over a bounded interval. The representation is the case `n = 1` of (26)
in Evans, §4.3.1, Example 4, and the identification recovers d'Alembert's formula (8) of
Evans, §2.4.1(a). Evans's transform (1) of §4.3.1 has no `2π` in the exponent, so his
multipliers are `cos(t|y|)` and `sin(t|y|)/|y|`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.1(a), equation (8); §4.3.1, equation (1) and
  Example 4, equations (24)-(26).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace WaveEquation

/-- The cosine/sine inverse Fourier formula for unit-speed waves on the real line.
The continuous `sinc` extension includes the zero-frequency velocity mode. -/
def fourierSolution (g h : ℝ → ℂ) (x t : ℝ) : ℂ :=
  𝓕⁻ (fun ξ ↦ (Real.cos (2 * Real.pi * ξ * t) : ℂ) * 𝓕 g ξ +
    (t * Real.sinc (2 * Real.pi * ξ * t) : ℝ) * 𝓕 h ξ) x

private def phase (x ξ : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * ξ * x : ℝ) * Complex.I)

private theorem norm_phase (x ξ : ℝ) : ‖phase x ξ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private theorem phase_add (x t ξ : ℝ) :
    phase (x + t) ξ = phase x ξ * phase t ξ := by
  unfold phase
  rw [mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

private theorem integrable_phase_mul {F : ℝ → ℂ} (hF : Integrable F) (x : ℝ) :
    Integrable (fun ξ ↦ phase x ξ * F ξ) := by
  apply hF.bdd_mul (by unfold phase; fun_prop)
  exact Filter.Eventually.of_forall fun ξ ↦ (norm_phase x ξ).le

private theorem integral_phase_mul (F : ℝ → ℂ) (x : ℝ) :
    (∫ ξ, phase x ξ * F ξ) = 𝓕⁻ F x := by
  rw [Real.fourierInv_eq']
  congr 1
  funext ξ
  simp only [phase, RCLike.inner_apply, conj_trivial, smul_eq_mul]
  congr 2
  push_cast
  ring

private theorem integral_phase_unit (c : ℝ) :
    (∫ s in (-1 : ℝ)..1, Complex.exp ((c * s : ℝ) * Complex.I)) = (2 * Real.sinc c : ℝ) := by
  by_cases hc : c = 0
  · norm_num [hc]
  have H := intervalIntegral.integral_comp_mul_left
    (fun r : ℝ ↦ Complex.exp ((r : ℂ) * Complex.I)) (a := -1) (b := 1) hc
  rw [mul_neg_one, mul_one, integral_exp_mul_I_eq_sinc] at H
  rw [H]
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_inv]
  field_simp [Complex.ofReal_ne_zero.mpr hc]

private theorem integral_phase_segment (x t ξ : ℝ) :
    (∫ s in (-1 : ℝ)..1, phase (x + t * s) ξ) =
      phase x ξ * (2 * Real.sinc (2 * Real.pi * ξ * t) : ℝ) := by
  simp_rw [phase_add]
  rw [intervalIntegral.integral_const_mul]
  congr 1
  convert integral_phase_unit (2 * Real.pi * ξ * t) using 1
  simp only [phase, mul_assoc]

private theorem intervalIntegral_inverse (F : ℝ → ℂ) (hF : Integrable F)
    (hFc : Continuous F) (x t : ℝ) :
    (∫ s in (-1 : ℝ)..1, 𝓕⁻ F (x + t * s)) =
      ∫ ξ, phase x ξ * (2 * Real.sinc (2 * Real.pi * ξ * t) : ℝ) * F ξ := by
  have hi : Integrable (fun p : ℝ × ℝ ↦ phase (x + t * p.1) p.2 * F p.2)
      ((volume.restrict (Set.uIoc (-1) 1)).prod volume) := by
    apply (integrable_prod_iff (by unfold phase; fun_prop)).mpr
    refine ⟨Filter.Eventually.of_forall fun s ↦ ?_, ?_⟩
    · simpa only using! integrable_phase_mul hF (x + t * s)
    · simp only [norm_mul, norm_phase, one_mul, Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact integrable_const _
  simp_rw [← integral_phase_mul]
  rw [intervalIntegral_integral_swap hi]
  congr 1
  funext ξ
  rw [intervalIntegral.integral_mul_const, integral_phase_segment]

private theorem cosine_eq_phases (t ξ : ℝ) :
    (Real.cos (2 * Real.pi * ξ * t) : ℂ) = (phase t ξ + phase (-t) ξ) / 2 := by
  rw [Complex.ofReal_cos, Complex.cos]
  simp only [phase, mul_neg, Complex.ofReal_neg, neg_mul]

private theorem integral_cosine (F : ℝ → ℂ) (hF : Integrable F) (x t : ℝ) :
    (∫ ξ, phase x ξ * (Real.cos (2 * Real.pi * ξ * t) : ℂ) * F ξ) =
      (𝓕⁻ F (x + t) + 𝓕⁻ F (x - t)) / 2 := by
  calc
    _ = ∫ ξ, (phase (x + t) ξ * F ξ + phase (x - t) ξ * F ξ) / 2 := by
      congr 1
      funext ξ
      rw [cosine_eq_phases, sub_eq_add_neg, phase_add, phase_add]
      ring
    _ = _ := by
      rw [integral_div, integral_add (integrable_phase_mul hF _) (integrable_phase_mul hF _),
        integral_phase_mul, integral_phase_mul]

private theorem integrable_cosine_mul {F : ℝ → ℂ} (hF : Integrable F) (t : ℝ) :
    Integrable (fun ξ ↦ (Real.cos (2 * Real.pi * ξ * t) : ℂ) * F ξ) := by
  apply hF.bdd_mul (by fun_prop) (c := 1)
  exact Filter.Eventually.of_forall fun ξ ↦ by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using Real.abs_cos_le_one _

private theorem integrable_sine_mul {F : ℝ → ℂ} (hF : Integrable F) (t : ℝ) :
    Integrable (fun ξ ↦ (t * Real.sinc (2 * Real.pi * ξ * t) : ℝ) * F ξ) := by
  apply hF.bdd_mul (by fun_prop) (c := |t|)
  exact Filter.Eventually.of_forall fun ξ ↦ by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_mul, mul_one] using
      mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one (2 * Real.pi * ξ * t)) (abs_nonneg t)

/-- Both evolved Fourier modes are integrable when the two initial Fourier transforms
are integrable. No division by a zero frequency is involved. -/
theorem integrable_fourierSolution_multiplier {g h : ℝ → ℂ}
    (hfg : Integrable (𝓕 g)) (hfh : Integrable (𝓕 h)) (t : ℝ) :
    Integrable (fun ξ ↦ (Real.cos (2 * Real.pi * ξ * t) : ℂ) * 𝓕 g ξ +
      (t * Real.sinc (2 * Real.pi * ξ * t) : ℝ) * 𝓕 h ξ) :=
  (integrable_cosine_mul hfg t).add (integrable_sine_mul hfh t)

/-- The inverse transform of the wave multipliers is a characteristic integral
of the inverse transforms of its frequency data. This form also applies to
filtered data whose inverse transforms need not be Schwartz functions. -/
theorem fourierInv_waveMultiplier_eq_characteristicIntegral {G H : ℝ → ℂ}
    (hG : Integrable G) (hH : Integrable H) (hHc : Continuous H) (x t : ℝ) :
    𝓕⁻ (fun ξ ↦ (Real.cos (2 * Real.pi * ξ * t) : ℂ) * G ξ +
      (t * Real.sinc (2 * Real.pi * ξ * t) : ℝ) * H ξ) x =
      (𝓕⁻ G (x + t) + 𝓕⁻ G (x - t)) / 2 + (1 / 2 : ℂ) * ∫ y in x - t..x + t, 𝓕⁻ H y := by
  have hc := integrable_phase_mul (integrable_cosine_mul hG t) x
  have hs := integrable_phase_mul (integrable_sine_mul hH t) x
  have hi := intervalIntegral_inverse H hH hHc x t
  have hvelocity : (∫ ξ, phase x ξ * (t * Real.sinc (2 * Real.pi * ξ * t) : ℝ) * H ξ) =
        (t : ℂ) / 2 * ∫ s in (-1 : ℝ)..1, 𝓕⁻ H (x + t * s) := by
    rw [hi, ← integral_const_mul]
    congr 1
    funext ξ
    push_cast
    ring
  have hsegment : (t : ℂ) * (∫ s in (-1 : ℝ)..1, 𝓕⁻ H (x + t * s)) =
      ∫ y in x - t..x + t, 𝓕⁻ H y := by
    have he := intervalIntegral.smul_integral_comp_mul_left
      (fun r ↦ 𝓕⁻ H (x + r)) (a := -1) (b := 1) t
    simp only [Complex.real_smul, mul_neg_one, mul_one] at he
    rw [he, intervalIntegral.integral_comp_add_left]
    simp only [sub_eq_add_neg]
  rw [← integral_phase_mul]
  simp_rw [mul_add]
  rw [integral_add hc hs]
  simp only [← mul_assoc]
  rw [integral_cosine _ hG, hvelocity]
  rw [div_mul_eq_mul_div, hsegment]
  ring

/-- Fourier inversion gives the characteristic formula on the real line, including
the integral of the initial velocity. The data and their Fourier transforms are
integrable; continuity fixes the pointwise representatives. -/
theorem fourierSolution_eq_characteristicIntegral {g h : ℝ → ℂ}
    (hg : Integrable g) (hh : Integrable h) (hgc : Continuous g) (hhc : Continuous h)
    (hfg : Integrable (𝓕 g)) (hfh : Integrable (𝓕 h)) (x t : ℝ) :
    fourierSolution g h x t =
      (g (x + t) + g (x - t)) / 2 + (1 / 2 : ℂ) * ∫ y in x - t..x + t, h y := by
  rw [fourierSolution, fourierInv_waveMultiplier_eq_characteristicIntegral hfg hfh
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hh)]
  simp only [hg.fourierInv_fourier_eq hfg hgc.continuousAt,
    hh.fourierInv_fourier_eq hfh hhc.continuousAt]

/-- For real data, the cosine/sine inverse transform is real and equals d'Alembert's
formula. This identity is valid at every real time, including the initial slice. -/
theorem fourierSolution_ofReal_eq_dAlembertFormula {g h : ℝ → ℝ}
    (hg : Integrable g) (hh : Integrable h) (hgc : Continuous g) (hhc : Continuous h)
    (hfg : Integrable (𝓕 (fun y ↦ (g y : ℂ))))
    (hfh : Integrable (𝓕 (fun y ↦ (h y : ℂ)))) (x t : ℝ) :
    fourierSolution (fun y ↦ (g y : ℂ)) (fun y ↦ (h y : ℂ)) x t =
      (dAlembertFormula g h x t : ℂ) := by
  rw [fourierSolution_eq_characteristicIntegral (g := fun y ↦ (g y : ℂ)) (h := fun y ↦ (h y : ℂ))
    (Complex.ofRealCLM.integrable_comp hg) (Complex.ofRealCLM.integrable_comp hh)
    (Complex.continuous_ofReal.comp hgc) (Complex.continuous_ofReal.comp hhc) hfg hfh]
  simp only [dAlembertFormula, intervalIntegral.integral_ofReal, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

end WaveEquation
