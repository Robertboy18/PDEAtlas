/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import CAS.ExactTactic

/-!
# Cosine and sine wave multipliers

The sine propagator is `t * sinc (ω*t)`, so zero frequency is included without
a denominator convention. Its first two time derivatives and uniform
bounds supply the Fourier integral construction.
-/

@[expose] public noncomputable section

namespace WaveEquation.Fourier

/-- The sine propagator at zero frequency is multiplication by time. -/
def sineKernel (ω t : ℝ) : ℝ := t * Real.sinc (ω * t)

/-- Away from zero frequency the sine propagator has its usual quotient form. -/
theorem sineKernel_eq_div {ω : ℝ} (hω : ω ≠ 0) (t : ℝ) :
    sineKernel ω t = Real.sin (ω * t) / ω := by
  by_cases ht : t = 0
  · simp [sineKernel, ht]
  · rw [sineKernel, Real.sinc_of_ne_zero (mul_ne_zero hω ht)]
    cas using [hω, ht]

/-- The derivative formula holds also at zero frequency and zero time. -/
theorem hasDerivAt_sineKernel (ω t : ℝ) :
    HasDerivAt (sineKernel ω) (Real.cos (ω * t)) t := by
  by_cases hω : ω = 0
  · subst ω
    change HasDerivAt (fun s : ℝ ↦ s * Real.sinc (0 * s)) (Real.cos (0 * t)) t
    simp only [zero_mul, Real.sinc_zero, mul_one, Real.cos_zero]
    exact hasDerivAt_id' t
  · have heq : sineKernel ω = fun s ↦ Real.sin (ω * s) / ω := funext (sineKernel_eq_div hω)
    rw [heq]
    cas using hω

/-- Multiplication by frequency recovers the sine multiplier, including frequency zero. -/
theorem frequency_mul_sineKernel (ω t : ℝ) :
    ω * sineKernel ω t = Real.sin (ω * t) := by
  by_cases hω : ω = 0
  · simp [hω]
  · rw [sineKernel_eq_div hω]
    cas using hω

/-- The sine propagator grows at most linearly in absolute time. -/
theorem abs_sineKernel_le (ω t : ℝ) : |sineKernel ω t| ≤ |t| := by
  simpa only [sineKernel, abs_mul, mul_one] using
    mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one (ω * t)) (abs_nonneg t)

/-- The displacement multiplier for frequency ω and displacement/velocity coefficients g and h. -/
def waveValue (ω : ℝ) (g h : ℂ) (t : ℝ) : ℂ :=
  Real.cos (ω * t) • g + sineKernel ω t • h

/-- The first time derivative of the displacement multiplier. -/
def waveVelocity (ω : ℝ) (g h : ℂ) (t : ℝ) : ℂ :=
  (-ω * Real.sin (ω * t)) • g + Real.cos (ω * t) • h

/-- The second time derivative of the displacement multiplier. -/
def waveAcceleration (ω : ℝ) (g h : ℂ) (t : ℝ) : ℂ :=
  (-(ω ^ 2) * Real.cos (ω * t)) • g + (-ω * Real.sin (ω * t)) • h

/-- The derivative of the cosine multiplier. -/
theorem hasDerivAt_cos_frequency (ω t : ℝ) :
    HasDerivAt (fun s ↦ Real.cos (ω * s)) (-ω * Real.sin (ω * t)) t := by
  cas

/-- The second derivative of the cosine multiplier. -/
theorem hasDerivAt_velocity_frequency (ω t : ℝ) :
    HasDerivAt (fun s ↦ -ω * Real.sin (ω * s)) (-(ω ^ 2) * Real.cos (ω * t)) t := by
  cas

/-- The velocity multiplier is the derivative of the displacement multiplier. -/
theorem hasDerivAt_waveValue (ω t : ℝ) (g h : ℂ) :
    HasDerivAt (waveValue ω g h) (waveVelocity ω g h t) t :=
  ((hasDerivAt_cos_frequency ω t).smul_const g).add ((hasDerivAt_sineKernel ω t).smul_const h)

/-- The acceleration multiplier is the derivative of the velocity multiplier. -/
theorem hasDerivAt_waveVelocity (ω t : ℝ) (g h : ℂ) :
    HasDerivAt (waveVelocity ω g h) (waveAcceleration ω g h t) t :=
  ((hasDerivAt_velocity_frequency ω t).smul_const g).add
    ((hasDerivAt_cos_frequency ω t).smul_const h)

/-- Each frequency solves the harmonic oscillator equation. -/
theorem waveAcceleration_eq (ω t : ℝ) (g h : ℂ) :
    waveAcceleration ω g h t = -(ω ^ 2) • waveValue ω g h t := by
  have hs : -ω * Real.sin (ω * t) = -(ω ^ 2) * sineKernel ω t := by
    rw [← frequency_mul_sineKernel ω t]
    ring
  simp only [waveAcceleration, waveValue, smul_add, ← mul_smul, hs]

/-- Displacement has a bound uniform on every bounded time interval. -/
theorem norm_waveValue_le (ω t T : ℝ) (g h : ℂ) (ht : |t| ≤ T) :
    ‖waveValue ω g h t‖ ≤ ‖g‖ + T * ‖h‖ := by
  calc
    ‖waveValue ω g h t‖ ≤ |Real.cos (ω * t)| * ‖g‖ + |sineKernel ω t| * ‖h‖ := by
      simpa only [waveValue, norm_smul, Real.norm_eq_abs] using
        norm_add_le (Real.cos (ω * t) • g) (sineKernel ω t • h)
    _ ≤ 1 * ‖g‖ + T * ‖h‖ := add_le_add
      (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right ((abs_sineKernel_le ω t).trans ht) (norm_nonneg _))
    _ = _ := by rw [one_mul]

/-- The differentiated cosine multiplier is bounded by its nonnegative frequency. -/
theorem abs_velocity_frequency_le {ω : ℝ} (hω : 0 ≤ ω) (t : ℝ) :
    |-ω * Real.sin (ω * t)| ≤ ω := by
  simpa only [abs_mul, abs_neg, abs_of_nonneg hω, mul_one] using
    mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (ω * t)) hω

/-- Velocity is bounded by one frequency moment of displacement and the velocity datum. -/
theorem norm_waveVelocity_le {ω : ℝ} (hω : 0 ≤ ω) (t : ℝ) (g h : ℂ) :
    ‖waveVelocity ω g h t‖ ≤ ω * ‖g‖ + ‖h‖ := by
  calc
    ‖waveVelocity ω g h t‖ ≤ |-ω * Real.sin (ω * t)| * ‖g‖ +
        |Real.cos (ω * t)| * ‖h‖ := by
      simpa only [waveVelocity, norm_smul, Real.norm_eq_abs] using
        norm_add_le ((-ω * Real.sin (ω * t)) • g) (Real.cos (ω * t) • h)
    _ ≤ ω * ‖g‖ + 1 * ‖h‖ := add_le_add
      (mul_le_mul_of_nonneg_right (abs_velocity_frequency_le hω t) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (norm_nonneg _))
    _ = _ := by rw [one_mul]

/-- Acceleration costs two displacement moments and one velocity moment. -/
theorem norm_waveAcceleration_le {ω : ℝ} (hω : 0 ≤ ω) (t : ℝ) (g h : ℂ) :
    ‖waveAcceleration ω g h t‖ ≤ ω ^ 2 * ‖g‖ + ω * ‖h‖ := by
  have hc : |-(ω ^ 2) * Real.cos (ω * t)| ≤ ω ^ 2 := by
    simpa only [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg ω), mul_one] using
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (ω * t)) (sq_nonneg ω)
  calc
    ‖waveAcceleration ω g h t‖ ≤ |-(ω ^ 2) * Real.cos (ω * t)| * ‖g‖ +
        |-ω * Real.sin (ω * t)| * ‖h‖ := by
      simpa only [waveAcceleration, norm_smul, Real.norm_eq_abs] using
        norm_add_le ((-(ω ^ 2) * Real.cos (ω * t)) • g) ((-ω * Real.sin (ω * t)) • h)
    _ ≤ ω ^ 2 * ‖g‖ + ω * ‖h‖ := add_le_add (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (abs_velocity_frequency_le hω t) (norm_nonneg _))

end WaveEquation.Fourier
