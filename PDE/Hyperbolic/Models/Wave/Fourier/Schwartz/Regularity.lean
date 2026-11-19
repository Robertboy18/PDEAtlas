/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Fourier.L1Reconstruction.SecondDerivative
public import PDE.Common.Euclidean
public import PDE.Hyperbolic.Models.Wave.Fourier.Schwartz.Kernel
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Joint regularity and the wave equation for Schwartz Fourier data

Schwartz decay supplies all frequency moments needed for two joint derivatives.
The Hessian of the inverse Fourier integral has zero wave trace, by the
oscillator identity and the Euclidean norm-square formula. Fourier inversion
then gives both physical initial data and the joint initial traces.

The spatial dimension is arbitrary, including zero. The real spacetime solution
built from these estimates is in `Fourier.Schwartz.Cauchy`.

In the notation of Evans, §4.3.1, Example 4, `cauchySolution g h` is the inverse transform of
`ĝ cos(t|y|) + ĥ sin(t|y|)/|y|` from (26), with Mathlib's `2π` convention, and the vanishing
wave trace of its Hessian is the oscillator equation (25) on the Fourier side.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.3.1, Example 4, equations (24)-(26).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform PDE.Analysis.Fourier
open scoped Topology

namespace WaveEquation.Fourier

/-- Real-linear derivatives with complex values carry the operator norm. -/
local instance instNormedAddCommGroupComplexDerivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] : NormedAddCommGroup (E →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- Keep the real scalar action when differentiating a complex-valued field. -/
local instance instNormedSpaceComplexDerivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] : NormedSpace ℝ (E →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedSpace

/-- The Hessian uses the operator norm twice. -/
local instance instNormedAddCommGroupComplexHessian {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The Hessian trace is a real-linear map on real bilinear forms. -/
local instance instNormedSpaceComplexHessian {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedSpace

section Schwartz
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The inverse cosine/sinc Fourier integral for displacement and velocity frequency data. -/
def waveSolution (G H : E → ℂ) (p : ℝ × E) : ℂ :=
  𝓕⁻ (fun ξ ↦ waveValue (2 * Real.pi * ‖ξ‖) (G ξ) (H ξ) p.1) p.2

/-- The joint first derivative of the frequency integrand. -/
def waveFirstKernel (G H : E → ℂ) (p : ℝ × E) (ξ : E) : (ℝ × E) →L[ℝ] ℂ :=
  PDE.Analysis.Fourier.inverseKernelDerivative ξ p
    (waveValue (2 * Real.pi * ‖ξ‖) (G ξ) (H ξ) p.1)
    (waveVelocity (2 * Real.pi * ‖ξ‖) (G ξ) (H ξ) p.1)

/-- The joint second derivative of the frequency integrand. -/
def waveSecondKernel (G H : E → ℂ) (p : ℝ × E) (ξ : E) :
    (ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℂ :=
  PDE.Analysis.Fourier.inverseKernelDerivative ξ p
    (derivativeDatum ξ (waveValue (2 * Real.pi * ‖ξ‖) (G ξ) (H ξ) p.1)
      (waveVelocity (2 * Real.pi * ‖ξ‖) (G ξ) (H ξ) p.1))
    (derivativeDatum ξ (waveVelocity (2 * Real.pi * ‖ξ‖) (G ξ) (H ξ) p.1)
      (waveAcceleration (2 * Real.pi * ‖ξ‖) (G ξ) (H ξ) p.1))

/-- Use the operator norm when integrating the wave's joint derivative. -/
local instance instContinuousENormWaveDerivative :
    ContinuousENorm ((ℝ × E) →L[ℝ] ℂ) :=
  (@SeminormedAddGroup.toESeminormedAddMonoid ((ℝ × E) →L[ℝ] ℂ) inferInstance).toContinuousENorm

/-- The second kernel is integrated in the iterated operator norm. -/
local instance instContinuousENormWaveHessian :
    ContinuousENorm ((ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℂ) :=
  (@SeminormedAddGroup.toESeminormedAddMonoid
    ((ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℂ) inferInstance).toContinuousENorm

/-- Joint regularity and the Hessian, with every bound derived from Schwartz data. -/
theorem schwartz_wave_regular (G H : SchwartzMap E ℂ) :
    ContDiff ℝ 2 (waveSolution G H) ∧
      ∀ p : ℝ × E, Integrable (waveFirstKernel G H p) ∧
        HasFDerivAt (waveSolution G H) (∫ ξ, waveFirstKernel G H p ξ) p ∧
        Integrable (waveSecondKernel G H p) ∧
        HasFDerivAt (fderiv ℝ (waveSolution G H)) (∫ ξ, waveSecondKernel G H p ξ) p := by
  apply contDiff_two_fourierInv_family (fun t ξ ↦ waveValue (2 * Real.pi * ‖ξ‖) (G ξ) (H ξ) t)
    (fun t ξ ↦ waveVelocity (2 * Real.pi * ‖ξ‖) (G ξ) (H ξ) t)
    (fun t ξ ↦ waveAcceleration (2 * Real.pi * ‖ξ‖) (G ξ) (H ξ) t) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t
    apply Continuous.aestronglyMeasurable
    unfold waveValue sineKernel
    fun_prop
  · intro t
    apply Continuous.aestronglyMeasurable
    unfold waveVelocity
    fun_prop
  · intro t
    apply Continuous.aestronglyMeasurable
    unfold waveAcceleration
    fun_prop
  · exact fun ξ t ↦ hasDerivAt_waveValue _ _ _ _
  · exact fun ξ t ↦ hasDerivAt_waveVelocity _ _ _ _
  · intro ξ
    unfold waveAcceleration
    fun_prop
  · intro T hT
    let b (ξ : E) := ‖G ξ‖ + T * ‖H ξ‖
    let c (ξ : E) := (2 * Real.pi) * (‖ξ‖ * ‖G ξ‖) + ‖H ξ‖
    let a (ξ : E) := (2 * Real.pi) ^ 2 * (‖ξ‖ ^ 2 * ‖G ξ‖) + (2 * Real.pi) * (‖ξ‖ * ‖H ξ‖)
    have hb (k : ℕ) : Integrable (fun ξ ↦ ‖ξ‖ ^ k * b ξ) := by
      convert (G.integrable_pow_mul volume k).add
        ((H.integrable_pow_mul volume k).const_mul T) using 1
      ext ξ
      dsimp only [b, Pi.add_apply]
      ring
    have hc (k : ℕ) : Integrable (fun ξ ↦ ‖ξ‖ ^ k * c ξ) := by
      convert ((G.integrable_pow_mul volume (k + 1)).const_mul (2 * Real.pi)).add
        (H.integrable_pow_mul volume k) using 1
      ext ξ
      dsimp only [c, Pi.add_apply]
      rw [pow_succ]
      ring
    have ha : Integrable a := by
      convert ((G.integrable_pow_mul volume 2).const_mul ((2 * Real.pi) ^ 2)).add
        ((H.integrable_pow_mul volume 1).const_mul (2 * Real.pi)) using 1
      ext ξ
      simp only [a, pow_one, Pi.add_apply]
    refine ⟨b, c, a, ?_, ?_, hb 2, ?_, ?_, ha, ?_⟩
    · simpa only [pow_zero, one_mul] using hb 0
    · simpa only [pow_one] using hb 1
    · simpa only [pow_zero, one_mul] using hc 0
    · simpa only [pow_one] using hc 1
    · intro t ht ξ
      have hω : 0 ≤ 2 * Real.pi * ‖ξ‖ := by positivity
      refine ⟨norm_waveValue_le _ _ _ _ _ ht, ?_, ?_⟩
      · simpa only [c, mul_assoc] using norm_waveVelocity_le hω t (G ξ) (H ξ)
      · convert norm_waveAcceleration_le hω t (G ξ) (H ξ) using 1
        dsimp only [a]
        ring

/-- Schwartz frequency data give a field that is C² jointly in time and space. -/
theorem contDiff_two_schwartz_wave (G H : SchwartzMap E ℂ) :
    ContDiff ℝ 2 (waveSolution G H) := (schwartz_wave_regular G H).1

/-- At zero time the multiplier selects the displacement frequency datum. -/
theorem waveSolution_initial_position (G H : E → ℂ) (x : E) :
    waveSolution G H (0, x) = 𝓕⁻ G x := by
  simp [waveSolution, waveValue, sineKernel]

/-- Evaluating the joint derivative in the time direction selects the velocity multiplier. -/
theorem waveSolution_time_derivative (G H : SchwartzMap E ℂ) (p : ℝ × E) :
    fderiv ℝ (waveSolution G H) p (1, 0) =
      𝓕⁻ (fun ξ ↦ waveVelocity (2 * Real.pi * ‖ξ‖) (G ξ) (H ξ) p.1) p.2 := by
  obtain ⟨hKi, hD, _⟩ := (schwartz_wave_regular G H).2 p
  rw [hD.fderiv, ContinuousLinearMap.integral_apply hKi]
  simp [waveFirstKernel, PDE.Analysis.Fourier.inverseKernelDerivative_apply,
    Real.fourierInv_eq, Circle.smul_def]

/-- The fixed-space curve has derivative given by the joint derivative. -/
theorem hasDerivAt_waveSolution_time (G H : SchwartzMap E ℂ) (t : ℝ) (x : E) :
    HasDerivAt (fun s ↦ waveSolution G H (s, x)) (fderiv ℝ (waveSolution G H) (t, x) (1, 0)) t := by
  have hu : DifferentiableAt ℝ (waveSolution G H) (t, x) :=
    ((contDiff_two_schwartz_wave G H).differentiable (by norm_num)).differentiableAt
  have hp : HasDerivAt (fun s : ℝ ↦ (s, x)) ((1 : ℝ), (0 : E)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  exact hu.hasFDerivAt.comp_hasDerivAt t hp

/-- Complex Schwartz initial data are transformed before applying the cosine/sinc formula. -/
def cauchySolution (g h : SchwartzMap E ℂ) : ℝ × E → ℂ :=
  waveSolution (𝓕 g : SchwartzMap E ℂ) (𝓕 h : SchwartzMap E ℂ)

/-- Fourier transforms of Schwartz initial data retain the decay needed for joint C². -/
theorem contDiff_two_cauchySolution (g h : SchwartzMap E ℂ) :
    ContDiff ℝ 2 (cauchySolution g h) :=
  contDiff_two_schwartz_wave (𝓕 g) (𝓕 h)

/-- Fourier inversion recovers the assigned displacement at time zero. -/
theorem cauchySolution_initial_position (g h : SchwartzMap E ℂ) (x : E) :
    cauchySolution g h (0, x) = g x := by
  rw [cauchySolution, waveSolution_initial_position]
  exact g.integrable.fourierInv_fourier_eq (𝓕 g).integrable g.continuous.continuousAt

/-- The time-direction derivative recovers the assigned velocity at time zero. -/
theorem cauchySolution_initial_velocity (g h : SchwartzMap E ℂ) (x : E) :
    fderiv ℝ (cauchySolution g h) (0, x) (1, 0) = h x := by
  rw [cauchySolution, waveSolution_time_derivative]
  simp only [waveVelocity, mul_zero, Real.sin_zero, Real.cos_zero, zero_smul, one_smul, zero_add]
  exact h.integrable.fourierInv_fourier_eq (𝓕 h).integrable h.continuous.continuousAt

/-- This uses Lean's derivative of the time curve, rather than an auxiliary velocity definition. -/
theorem deriv_cauchySolution_time (g h : SchwartzMap E ℂ) (p : ℝ × E) :
    deriv (fun s ↦ cauchySolution g h (s, p.2)) p.1 = fderiv ℝ (cauchySolution g h) p (1, 0) :=
  (hasDerivAt_waveSolution_time (𝓕 g) (𝓕 h) p.1 p.2).deriv

/-- The field approaches the assigned displacement jointly in time and space. -/
theorem tendsto_cauchySolution_initial_position (g h : SchwartzMap E ℂ) (x : E) :
    Filter.Tendsto (cauchySolution g h) (𝓝 (0, x)) (𝓝 (g x)) := by
  simpa only [ContinuousAt, cauchySolution_initial_position] using
    (contDiff_two_cauchySolution g h).continuous.continuousAt (x := (0, x))

/-- The time derivative approaches the assigned velocity jointly in time and space. -/
theorem tendsto_deriv_cauchySolution_initial_velocity (g h : SchwartzMap E ℂ) (x : E) :
    Filter.Tendsto (fun p : ℝ × E ↦ deriv (fun s ↦ cauchySolution g h (s, p.2)) p.1)
      (𝓝 (0, x)) (𝓝 (h x)) := by
  have hvelocity : Continuous (fun p : ℝ × E ↦ fderiv ℝ (cauchySolution g h) p (1, 0)) :=
    (ContinuousLinearMap.apply ℝ ℂ ((1 : ℝ), (0 : E))).continuous.comp
      ((contDiff_two_cauchySolution g h).continuous_fderiv (by norm_num))
  simpa only [ContinuousAt, deriv_cauchySolution_time, cauchySolution_initial_velocity] using
    hvelocity.continuousAt (x := (0, x))

end Schwartz

section WaveTrace

/-- Evaluation of a bilinear map on two copies of a fixed vector. -/
def diagonalEval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (q : E) :
    (E →L[ℝ] E →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.apply ℝ ℂ q).comp
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℂ) q)

/-- The time-time Hessian entry minus the spatial diagonal sum. -/
def waveTrace (n : ℕ) :
    ((ℝ × ℝ^n) →L[ℝ] (ℝ × ℝ^n) →L[ℝ] ℂ) →L[ℝ] ℂ :=
  diagonalEval (E := ℝ × ℝ^n) (1, 0) -
    ∑ i : Fin n, diagonalEval (E := ℝ × ℝ^n) (0, EuclideanSpace.single i 1)

/-- The wave trace evaluates a Hessian in the canonical time and spatial directions. -/
theorem waveTrace_apply {n : ℕ} (L : (ℝ × ℝ^n) →L[ℝ] (ℝ × ℝ^n) →L[ℝ] ℂ) :
    waveTrace n L = L (1, 0) (1, 0) -
      ∑ i : Fin n, L (0, EuclideanSpace.single i 1) (0, EuclideanSpace.single i 1) := by
  simp [waveTrace, diagonalEval]

/-- The time-time derivative of the integrand is its acceleration multiplier. -/
theorem waveSecondKernel_time {n : ℕ} (G H : ℝ^n → ℂ) (p : ℝ × ℝ^n) (ξ : ℝ^n) :
    waveSecondKernel G H p ξ (1, 0) (1, 0) = (Real.fourierChar (inner ℝ ξ p.2) : ℂ) *
      waveAcceleration (2 * Real.pi * ‖ξ‖) (G ξ) (H ξ) p.1 := by
  simp [waveSecondKernel, PDE.Analysis.Fourier.inverseKernelDerivative_apply,
    derivativeDatum, ContinuousLinearMap.smulRight_apply, smul_eq_mul]

/-- Each spatial diagonal derivative contributes minus its squared angular frequency. -/
theorem waveSecondKernel_space {n : ℕ} (G H : ℝ^n → ℂ) (p : ℝ × ℝ^n) (ξ : ℝ^n) (i : Fin n) :
    waveSecondKernel G H p ξ (0, EuclideanSpace.single i 1) (0, EuclideanSpace.single i 1) =
      (Real.fourierChar (inner ℝ ξ p.2) : ℂ) * ((-((2 * Real.pi) ^ 2 * (ξ i) ^ 2) : ℝ) •
      waveValue (2 * Real.pi * ‖ξ‖) (G ξ) (H ξ) p.1) := by
  have hi : inner ℝ ξ (EuclideanSpace.single i 1) = ξ i := by
    simpa using EuclideanSpace.inner_single_right i (1 : ℝ) ξ
  simp [waveSecondKernel, PDE.Analysis.Fourier.inverseKernelDerivative_apply,
    derivativeDatum, ContinuousLinearMap.smulRight_apply, hi, Complex.real_smul, smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]

/-- The oscillator equation makes each frequency integrand have zero wave trace. -/
theorem waveTrace_secondKernel {n : ℕ} (G H : ℝ^n → ℂ) (p : ℝ × ℝ^n)
    (ξ : ℝ^n) : waveTrace n (waveSecondKernel G H p ξ) = 0 := by
  have hs : (∑ i : Fin n, -((2 * Real.pi) ^ 2 * (ξ i) ^ 2)) =
      -(2 * Real.pi * ‖ξ‖) ^ 2 := by
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq]
    ring
  rw [waveTrace_apply, waveSecondKernel_time]
  simp_rw [waveSecondKernel_space, ← Finset.mul_sum, ← Finset.sum_smul]
  rw [hs, waveAcceleration_eq, sub_self]

/-- The constructed arbitrary-dimensional integral satisfies the Hessian wave residual. -/
theorem waveSolution_waveTrace {n : ℕ} (G H : SchwartzMap (ℝ^n) ℂ)
    (p : ℝ × ℝ^n) : waveTrace n (fderiv ℝ (fderiv ℝ (waveSolution G H)) p) = 0 := by
  obtain ⟨hKi, hD⟩ := ((schwartz_wave_regular G H).2 p).2.2
  rw [hD.fderiv, ← (waveTrace n).integral_comp_comm hKi]
  simp only [waveTrace_secondKernel, integral_zero]

/-- The physical-space Schwartz Cauchy construction has zero Hessian wave residual. -/
theorem cauchySolution_waveTrace {n : ℕ} (g h : SchwartzMap (ℝ^n) ℂ)
    (p : ℝ × ℝ^n) : waveTrace n (fderiv ℝ (fderiv ℝ (cauchySolution g h)) p) = 0 :=
  waveSolution_waveTrace (𝓕 g) (𝓕 h) p

end WaveTrace

end WaveEquation.Fourier
