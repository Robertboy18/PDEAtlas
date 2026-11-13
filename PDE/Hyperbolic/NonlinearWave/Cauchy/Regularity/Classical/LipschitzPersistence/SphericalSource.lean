/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.OddDimensions.ClassicalSolution

/-!
# Lipschitz reactions in the five-dimensional wave formula

The velocity propagator in dimension five differentiates the spherical source
once. Its estimate for `f ∘ u` therefore uses the Lipschitz constant of `f` and
spherical averages of `|u|` and `‖Du‖`. No second derivative of `f` occurs.

These are estimates of the wave formula. Obtaining a bound for a
nonlinear evolution still requires spatial trace estimates and identification
of its Duhamel term with this propagator.
-/

@[expose] public noncomputable section

open MeasureTheory PDE.Analysis PDE.Common
open scoped NNReal

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n : ℕ} [Fact (0 < n)]

/-- A zero-preserving Lipschitz reaction is bounded on each spherical slice
by the spherical average of the absolute value of its input. -/
theorem norm_unitSphereAverage_comp_le {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hf0 : f 0 = 0) {u : ℝ^n → ℝ} (hu : Continuous u) (x : ℝ^n) (r : ℝ) :
    ‖unitSphereAverage n (f ∘ u) x r‖ ≤ K * unitSphereAverage n (fun y ↦ ‖u y‖) x r := by
  have hc : Continuous (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦
      u (x + r • (ω : ℝ^n))) := by fun_prop
  have hi : Integrable (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦ (K : ℝ) * ‖u (x + r • (ω : ℝ^n))‖)
      (volume : Measure (ℝ^n)).toSphere := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    fun_prop
  have hb : ‖∫ ω : Metric.sphere (0 : ℝ^n) 1,
      f (u (x + r • (ω : ℝ^n))) ∂(volume : Measure (ℝ^n)).toSphere‖ ≤
      ∫ ω : Metric.sphere (0 : ℝ^n) 1,
        (K : ℝ) * ‖u (x + r • (ω : ℝ^n))‖ ∂(volume : Measure (ℝ^n)).toSphere := by
    apply norm_integral_le_of_norm_le hi
    filter_upwards with ω
    simpa only [hf0, dist_zero_right] using hf.dist_le_mul (u (x + r • (ω : ℝ^n))) 0
  unfold unitSphereAverage
  rw [norm_div, Real.norm_of_nonneg unitSphereArea_pos.le]
  simpa only [integral_const_mul, Function.comp_apply, mul_div_assoc] using
    div_le_div_of_nonneg_right hb unitSphereArea_pos.le

/-- Differentiating a spherical reaction average uses only `f'`. The
Lipschitz constant bounds that derivative before angular integration. -/
theorem norm_deriv_unitSphereAverage_comp_le {f : ℝ → ℝ} {K : ℝ≥0} (hf : ContDiff ℝ 1 f)
    (hl : LipschitzWith K f) {u : ℝ^n → ℝ} (hu : ContDiff ℝ 1 u) (x : ℝ^n) (r : ℝ) :
    ‖deriv (unitSphereAverage n (f ∘ u) x) r‖ ≤
      K * unitSphereAverage n (fun y ↦ ‖fderiv ℝ u y‖) x r := by
  rw [(hasDerivAt_unitSphereAverage (f ∘ u) x r (hf.comp hu)).deriv]
  have hc : Continuous (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦
      ‖fderiv ℝ u (x + r • (ω : ℝ^n))‖) := by
    apply (hu.continuous_fderiv one_ne_zero).norm.comp
    fun_prop
  have hi : Integrable (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦
      (K : ℝ) * ‖fderiv ℝ u (x + r • (ω : ℝ^n))‖)
      (volume : Measure (ℝ^n)).toSphere := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    fun_prop
  have hb : ‖∫ ω : Metric.sphere (0 : ℝ^n) 1, fderiv ℝ (f ∘ u) (x + r • (ω : ℝ^n)) (ω : ℝ^n)
        ∂(volume : Measure (ℝ^n)).toSphere‖ ≤ ∫ ω : Metric.sphere (0 : ℝ^n) 1,
        (K : ℝ) * ‖fderiv ℝ u (x + r • (ω : ℝ^n))‖
          ∂(volume : Measure (ℝ^n)).toSphere := by
    apply norm_integral_le_of_norm_le hi
    filter_upwards with ω
    rw [fderiv_comp _ (hf.differentiable one_ne_zero _)
      (hu.differentiable one_ne_zero _), ContinuousLinearMap.comp_apply]
    calc
      _ ≤ ‖fderiv ℝ f (u (x + r • (ω : ℝ^n)))‖ * ‖fderiv ℝ u (x + r • (ω : ℝ^n)) (ω : ℝ^n)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (K : ℝ) * (‖fderiv ℝ u (x + r • (ω : ℝ^n))‖ * ‖(ω : ℝ^n)‖) :=
        mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hl)
          (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _) K.coe_nonneg
      _ = _ := by rw [mem_sphere_zero_iff_norm.mp ω.property, mul_one]
  unfold unitSphereAverage
  rw [norm_div, Real.norm_of_nonneg unitSphereArea_pos.le]
  simpa only [integral_const_mul, mul_div_assoc] using
    div_le_div_of_nonneg_right hb unitSphereArea_pos.le

/-- Expanding the single radial differentiation in dimension five gives an
identity of derivatives and integrals, valid also at signed age zero. -/
theorem oddSphericalProfile_one_eq {u : ℝ^5 → ℝ} (hu : ContDiff ℝ 1 u) (x : ℝ^5) (r : ℝ) :
    WaveEquation.oddSphericalProfile 1 u x r =
      3 * r * unitSphereAverage 5 u x r + r ^ 2 * deriv (unitSphereAverage 5 u x) r := by
  have hd := ((hasDerivAt_pow 3 r).mul (hasDerivAt_unitSphereAverage u x r hu)).deriv
  have hm := (hasDerivAt_unitSphereAverage u x r hu).deriv
  simp only [WaveEquation.oddSphericalProfile, oddRadialTransform_succ,
    oddRadialTransform_zero, evansRadialDerivative]
  norm_num only [Nat.reduceMul, Nat.reduceAdd] at *
  change deriv ((fun s : ℝ ↦ s ^ 3) * unitSphereAverage 5 u x) r / r = _
  rw [hd, ← hm]
  by_cases hr : r = 0
  · simp [hr]
  · field_simp

/-- The five-dimensional homogeneous wave with zero displacement needs
only the first spatial derivative of its velocity datum for this formula. -/
theorem oddWaveSolution_one_zero_eq {u : ℝ^5 → ℝ} (hu : ContDiff ℝ 1 u) (x : ℝ^5) (r : ℝ) :
    WaveEquation.oddWaveSolution 1 (fun _ ↦ 0) u (timeSpaceCons r x) =
      r * unitSphereAverage 5 u x r + r ^ 2 / 3 * deriv (unitSphereAverage 5 u x) r := by
  rw [WaveEquation.oddWaveSolution,
    WaveEquation.partialDeriv_oddWavePotential_time 1 contDiff_const,
    WaveEquation.oddWavePotential_timeSpaceCons]
  have hz : WaveEquation.oddSphericalProfile 1 (fun _ ↦ 0) x = fun _ ↦ 0 := by
    funext t
    rw [oddSphericalProfile_one_eq contDiff_const]
    have hm : unitSphereAverage 5 (fun _ ↦ 0) x = fun _ ↦ 0 := by
      funext s
      simp [unitSphereAverage]
    rw [hm, deriv_const]
    ring
  rw [hz, deriv_const, zero_add, oddSphericalProfile_one_eq hu]
  norm_num [Nat.doubleFactorial]
  ring

/-- A five-dimensional reaction source is controlled by zeroth and first
spherical observations of the input. -/
theorem norm_oddWaveSolution_one_comp_le {f : ℝ → ℝ} {K : ℝ≥0} (hf : ContDiff ℝ 1 f)
    (hl : LipschitzWith K f) (hf0 : f 0 = 0) {u : ℝ^5 → ℝ} (hu : ContDiff ℝ 1 u) (x : ℝ^5) {r : ℝ}
    (hr : 0 ≤ r) :
    ‖WaveEquation.oddWaveSolution 1 (fun _ ↦ 0) (f ∘ u) (timeSpaceCons r x)‖ ≤
      K * (r * unitSphereAverage 5 (fun y ↦ ‖u y‖) x r +
        r ^ 2 / 3 * unitSphereAverage 5 (fun y ↦ ‖fderiv ℝ u y‖) x r) := by
  rw [oddWaveSolution_one_zero_eq (hf.comp hu)]
  calc
    _ ≤ ‖r * unitSphereAverage 5 (f ∘ u) x r‖ +
        ‖r ^ 2 / 3 * deriv (unitSphereAverage 5 (f ∘ u) x) r‖ := norm_add_le _ _
    _ = r * ‖unitSphereAverage 5 (f ∘ u) x r‖ +
        r ^ 2 / 3 * ‖deriv (unitSphereAverage 5 (f ∘ u) x) r‖ := by
      rw [norm_mul, norm_mul, Real.norm_of_nonneg hr,
        Real.norm_of_nonneg (by positivity : 0 ≤ r ^ 2 / 3)]
    _ ≤ r * (K * unitSphereAverage 5 (fun y ↦ ‖u y‖) x r) +
        r ^ 2 / 3 * (K * unitSphereAverage 5 (fun y ↦ ‖fderiv ℝ u y‖) x r) :=
      add_le_add (mul_le_mul_of_nonneg_left (norm_unitSphereAverage_comp_le hl hf0
        hu.continuous x r) hr) (mul_le_mul_of_nonneg_left
          (norm_deriv_unitSphereAverage_comp_le hf hl hu x r) (by positivity))
    _ = _ := by ring

end PDE.Hyperbolic.NonlinearWave.Cauchy
