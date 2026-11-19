/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Fourier.Convolution
public import PDE.Analysis.Fourier.HilbertTransform
public import PDE.Analysis.Fourier.HilbertTransform.Regularity
public import PDE.Analysis.Fourier.L2Compatibility
import CAS.ExactTactic

/-!
# From real principal values to the spectral Hilbert transform

The multiplier `hilbertAbelSymbol ε ξ` is `-i sign(ξ) exp(-2π ε |ξ|)`.
Its inverse Fourier kernel is the conjugate Poisson kernel
`t / (π (ε² + t²))`, and without the sign the inverse Fourier kernel of
`exp(-2π ε |ξ|)` is the Poisson kernel `ε / (π (ε² + t²))` (`fourierInv_exp_neg_abs`).
Positive regularization parameters make the Fourier integrals absolutely convergent.

Local constant subtraction and dominated convergence identify the Abel limit
with the convergent principal value. Fubini's theorem identifies each damped
integral with its multiplier formula. Integrable Fourier transforms allow
removal of the damping, and testing against smooth compactly supported
functions connects the inverse Fourier integral to Mathlib's `L²` transform.

`hilbertPV_eq_hilbertTransform_ae_schwartz` and
`hilbertPV_eq_hilbertTransform_ae_of_contDiff_compactSupport` prove the resulting
almost-everywhere identification with the concrete spectral operator.
The latter class also has principal values at every point.
-/

@[expose] public section

namespace PDE.Analysis

open Filter FourierTransform MeasureTheory Set
open scoped ContDiff SchwartzMap Topology

noncomputable section

/-- The exponentially damped multiplier of the Hilbert transform. -/
def hilbertAbelSymbol (ε ξ : ℝ) : ℂ :=
  hilbertSymbol ξ * (Real.exp (-(2 * Real.pi * ε) * |ξ|) : ℂ)

/-- The real conjugate Poisson kernel with height `ε`. -/
def hilbertAbelKernel (ε t : ℝ) : ℝ :=
  Real.pi⁻¹ * (t / (ε ^ 2 + t ^ 2))

/-- The Abel-regularized Hilbert integral. -/
def hilbertAbelIntegral (f : ℝ → ℝ) (x ε : ℝ) : ℝ :=
  ∫ t, hilbertAbelKernel ε t * f (x - t)

/-- A two-sided decaying exponential is integrable. -/
theorem integrable_hilbertAbelWeight {a : ℝ} (ha : 0 < a) :
    Integrable (fun ξ : ℝ ↦ Real.exp (-a * |ξ|)) := by
  have hpos : IntegrableOn (fun ξ : ℝ ↦ Real.exp (-a * |ξ|)) (Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) 0).congr_fun
      (hs := measurableSet_Ioi)
    intro ξ hξ
    simp only [abs_of_pos hξ]
  have hneg : IntegrableOn (fun ξ : ℝ ↦ Real.exp (-a * |ξ|)) (Iic 0) := by
    apply (integrableOn_exp_mul_Iic ha 0).congr_fun (hs := measurableSet_Iic)
    intro ξ hξ
    simp only [abs_of_nonpos hξ, neg_mul_neg]
  simpa only [Ioi_union_Iic, integrableOn_univ] using hpos.union hneg

/-- Exponential damping makes the Hilbert symbol absolutely integrable. -/
theorem integrable_hilbertAbelSymbol {ε : ℝ} (hε : 0 < ε) :
    Integrable (hilbertAbelSymbol ε) := by
  have ha : 0 < 2 * Real.pi * ε := mul_pos (mul_pos (by norm_num) Real.pi_pos) hε
  apply (integrable_hilbertAbelWeight ha).mono'
  · exact measurable_hilbertSymbol.aestronglyMeasurable.mul
      (by fun_prop)
  · filter_upwards with ξ
    rw [hilbertAbelSymbol, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_nonneg _) (norm_hilbertSymbol_le_one ξ)

/-- On the positive half-line, the inverse-Fourier integrand is one decaying exponential. -/
theorem hilbertAbelInverseIntegrand_pos (ε t : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    Complex.exp ((2 * Real.pi * (ξ * t) : ℝ) * Complex.I) * hilbertAbelSymbol ε ξ =
      -Complex.I * Complex.exp
        ((-(2 * Real.pi * ε : ℝ) + (2 * Real.pi * t : ℝ) * Complex.I) * ξ) := by
  rw [hilbertAbelSymbol, hilbertSymbol_of_pos hξ, abs_of_pos hξ, Complex.ofReal_exp]
  rw [show Complex.exp ((2 * Real.pi * (ξ * t) : ℝ) * Complex.I) *
      (-Complex.I * Complex.exp ((-(2 * Real.pi * ε) * ξ : ℝ))) =
      -Complex.I * (Complex.exp ((2 * Real.pi * (ξ * t) : ℝ) * Complex.I) *
        Complex.exp ((-(2 * Real.pi * ε) * ξ : ℝ))) by cas, ← Complex.exp_add]
  congr 2
  push_cast
  cas

/-- On the negative half-line, the inverse-Fourier integrand is one decaying exponential. -/
theorem hilbertAbelInverseIntegrand_neg (ε t : ℝ) {ξ : ℝ} (hξ : ξ < 0) :
    Complex.exp ((2 * Real.pi * (ξ * t) : ℝ) * Complex.I) * hilbertAbelSymbol ε ξ =
      Complex.I * Complex.exp
        (((2 * Real.pi * ε : ℝ) + (2 * Real.pi * t : ℝ) * Complex.I) * ξ) := by
  rw [hilbertAbelSymbol, hilbertSymbol_of_neg hξ, abs_of_neg hξ, neg_mul_neg,
    Complex.ofReal_exp]
  rw [show Complex.exp ((2 * Real.pi * (ξ * t) : ℝ) * Complex.I) *
      (Complex.I * Complex.exp ((2 * Real.pi * ε * ξ : ℝ))) =
      Complex.I * (Complex.exp ((2 * Real.pi * (ξ * t) : ℝ) * Complex.I) *
        Complex.exp ((2 * Real.pi * ε * ξ : ℝ))) by cas, ← Complex.exp_add]
  congr 2
  push_cast
  cas

/-- The two half-line exponential integrals combine to a real rational kernel. -/
theorem hilbertAbel_halfLine_sum (a b : ℝ) :
    Complex.I / (-(a : ℂ) + (b : ℂ) * Complex.I) +
      Complex.I / ((a : ℂ) + (b : ℂ) * Complex.I) =
        (2 * b / (a ^ 2 + b ^ 2) : ℝ) := by
  apply Complex.ext
  · simp only [Complex.add_re, Complex.div_re, Complex.I_re, Complex.I_im,
      Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.normSq_apply]
    cas
  · simp only [Complex.add_im, Complex.div_im, Complex.I_re, Complex.I_im,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_im, Complex.normSq_apply]
    cas

/-- The inverse Fourier transform of the Abel-damped Hilbert symbol is the
conjugate Poisson kernel. Both half-line integrals are absolutely convergent. -/
theorem fourierInv_hilbertAbelSymbol {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    𝓕⁻ (hilbertAbelSymbol ε) t = (hilbertAbelKernel ε t : ℂ) := by
  have ha : 0 < 2 * Real.pi * ε := mul_pos (mul_pos (by norm_num) Real.pi_pos) hε
  have hp : (-(2 * Real.pi * ε : ℝ) + (2 * Real.pi * t : ℝ) * Complex.I).re < 0 := by
    simpa using neg_lt_zero.mpr ha
  have hn : 0 < ((2 * Real.pi * ε : ℝ) + (2 * Real.pi * t : ℝ) * Complex.I).re := by
    simpa using ha
  have hint : Integrable (fun ξ : ℝ ↦
      Complex.exp ((2 * Real.pi * (ξ * t) : ℝ) * Complex.I) * hilbertAbelSymbol ε ξ) := by
    apply (integrable_hilbertAbelSymbol hε).mono
    · exact (by fun_prop : AEStronglyMeasurable
        (fun ξ : ℝ ↦ Complex.exp ((2 * Real.pi * (ξ * t) : ℝ) * Complex.I)) volume).mul
          (integrable_hilbertAbelSymbol hε).aestronglyMeasurable
    · filter_upwards with ξ
      simp [Complex.norm_exp]
  rw [Real.fourierInv_eq']
  simp only [Real.inner_apply, smul_eq_mul]
  rw [← integral_add_compl measurableSet_Ioi hint, compl_Ioi,
    integral_Iic_eq_integral_Iio]
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun ξ hξ ↦ hilbertAbelInverseIntegrand_pos ε t hξ),
    setIntegral_congr_fun measurableSet_Iio
      (fun ξ hξ ↦ hilbertAbelInverseIntegrand_neg ε t hξ)]
  rw [integral_const_mul, integral_const_mul, ← integral_Iic_eq_integral_Iio,
    integral_exp_mul_complex_Ioi hp, integral_exp_mul_complex_Iic hn]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, ← mul_div_assoc, neg_mul_neg,
    mul_one]
  rw [hilbertAbel_halfLine_sum]
  congr 1
  unfold hilbertAbelKernel
  cas using Real.pi_ne_zero

/-- On the positive half-line the inverse Fourier integrand of `exp (-2π ε |ξ|)` is one
decaying exponential. -/
private theorem poissonInverseIntegrand_pos (ε t : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    Complex.exp ((2 * Real.pi * (ξ * t) : ℝ) * Complex.I) *
        (Real.exp (-(2 * Real.pi * ε) * |ξ|) : ℂ) =
      Complex.exp ((-(2 * Real.pi * ε : ℝ) + (2 * Real.pi * t : ℝ) * Complex.I) * ξ) := by
  rw [abs_of_pos hξ, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- On the negative half-line the inverse Fourier integrand of `exp (-2π ε |ξ|)` is one
decaying exponential. -/
private theorem poissonInverseIntegrand_neg (ε t : ℝ) {ξ : ℝ} (hξ : ξ < 0) :
    Complex.exp ((2 * Real.pi * (ξ * t) : ℝ) * Complex.I) *
        (Real.exp (-(2 * Real.pi * ε) * |ξ|) : ℂ) =
      Complex.exp (((2 * Real.pi * ε : ℝ) + (2 * Real.pi * t : ℝ) * Complex.I) * ξ) := by
  rw [abs_of_neg hξ, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The two half-line integrals of `exp (-2π ε |ξ|)` combine to a real rational function. -/
private theorem poisson_halfLine_sum (a b : ℝ) :
    -1 / (-(a : ℂ) + (b : ℂ) * Complex.I) + 1 / ((a : ℂ) + (b : ℂ) * Complex.I) =
      (2 * a / (a ^ 2 + b ^ 2) : ℝ) := by
  apply Complex.ext
  · simp only [Complex.add_re, Complex.div_re, Complex.I_re, Complex.I_im, Complex.neg_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.one_re, Complex.normSq_apply,
      Complex.add_im, Complex.neg_im, Complex.mul_im, Complex.one_im]
    cas
  · simp only [Complex.add_im, Complex.div_im, Complex.I_re, Complex.I_im, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.one_im, Complex.normSq_apply,
      Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.one_re]
    cas

/-- The inverse Fourier transform of the Abel weight `exp (-2π ε |ξ|)` is the Poisson kernel
`ε / (π (ε² + t²))`. As for `fourierInv_hilbertAbelSymbol`, both half-line integrals converge
absolutely. -/
theorem fourierInv_exp_neg_abs {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    𝓕⁻ (fun ξ : ℝ ↦ (Real.exp (-(2 * Real.pi * ε) * |ξ|) : ℂ)) t =
      ((Real.pi⁻¹ * (ε / (ε ^ 2 + t ^ 2)) : ℝ) : ℂ) := by
  have ha : 0 < 2 * Real.pi * ε := by positivity
  have hp : (-(2 * Real.pi * ε : ℝ) + (2 * Real.pi * t : ℝ) * Complex.I).re < 0 := by
    simpa using neg_lt_zero.mpr ha
  have hn : 0 < ((2 * Real.pi * ε : ℝ) + (2 * Real.pi * t : ℝ) * Complex.I).re := by
    simpa using ha
  have hint : Integrable (fun ξ : ℝ ↦ Complex.exp ((2 * Real.pi * (ξ * t) : ℝ) * Complex.I) *
      (Real.exp (-(2 * Real.pi * ε) * |ξ|) : ℂ)) := by
    refine (integrable_hilbertAbelWeight ha).mono' (by fun_prop : Continuous _).aestronglyMeasurable
      (Eventually.of_forall fun ξ ↦ ?_)
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  rw [Real.fourierInv_eq']
  simp only [Real.inner_apply, smul_eq_mul]
  rw [← integral_add_compl measurableSet_Ioi hint, compl_Ioi, integral_Iic_eq_integral_Iio,
    setIntegral_congr_fun measurableSet_Ioi (fun ξ hξ ↦ poissonInverseIntegrand_pos ε t hξ),
    setIntegral_congr_fun measurableSet_Iio (fun ξ hξ ↦ poissonInverseIntegrand_neg ε t hξ),
    ← integral_Iic_eq_integral_Iio, integral_exp_mul_complex_Ioi hp,
    integral_exp_mul_complex_Iic hn]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [poisson_halfLine_sum]
  congr 1
  have hεt : ε ^ 2 + t ^ 2 ≠ 0 := by positivity
  cas using [Real.pi_ne_zero, hεt]

/-- At positive height the conjugate Poisson kernel is bounded. -/
theorem abs_hilbertAbelKernel_le {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    |hilbertAbelKernel ε t| ≤ Real.pi⁻¹ / ε := by
  have hd : 0 < ε ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hε) (sq_nonneg t)
  have ht : ε * |t| ≤ ε ^ 2 + t ^ 2 := by
    nlinarith [sq_nonneg (ε - |t|), sq_abs t]
  rw [hilbertAbelKernel, abs_mul, abs_of_pos (inv_pos.mpr Real.pi_pos), abs_div,
    abs_of_pos hd, div_eq_mul_inv (Real.pi⁻¹)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr Real.pi_pos.le)
  rw [div_le_iff₀ hd, inv_mul_eq_div, le_div_iff₀ hε]
  simpa only [mul_comm] using ht

/-- The Abel integral of an `L¹` input is an absolutely convergent integral. -/
theorem integrable_hilbertAbelIntegrand {f : ℝ → ℝ} (hf : Integrable f)
    (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun t ↦ hilbertAbelKernel ε t * f (x - t)) := by
  apply (hf.comp_sub_left x).bdd_mul
    (show Measurable (hilbertAbelKernel ε) by
      unfold hilbertAbelKernel; fun_prop).aestronglyMeasurable
  exact Eventually.of_forall (fun t ↦ abs_hilbertAbelKernel_le hε t)

/-- The even cancellation weight lies between zero and one. -/
theorem hilbertAbelWeight_mem_Icc (ε t : ℝ) :
    t ^ 2 / (ε ^ 2 + t ^ 2) ∈ Icc (0 : ℝ) 1 :=
  ⟨div_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _)),
    div_le_one_of_le₀ (le_add_of_nonneg_left (sq_nonneg _))
      (add_nonneg (sq_nonneg _) (sq_nonneg _))⟩

/-- Multiplication by the even cancellation weight preserves integrability. -/
theorem integrable_mul_hilbertAbelWeight {g : ℝ → ℝ} (hg : Integrable g) (ε : ℝ) :
    Integrable (fun t ↦ g t * (t ^ 2 / (ε ^ 2 + t ^ 2))) := by
  apply hg.mul_bdd (c := 1)
    (show Measurable (fun t : ℝ ↦ t ^ 2 / (ε ^ 2 + t ^ 2)) by fun_prop).aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (hilbertAbelWeight_mem_Icc ε t).1]
  exact (hilbertAbelWeight_mem_Icc ε t).2

/-- The local constant removed in the PV construction also cancels in the Abel integral. -/
theorem integral_hilbertAbelLocalConstant (R c ε : ℝ) :
    (∫ t, hilbertAbelKernel ε t * {s : ℝ | |s| < R}.indicator (fun _ ↦ c) t) = 0 := by
  apply integral_eq_zero_of_odd
  intro t
  by_cases ht : |t| < R <;> simp [hilbertAbelKernel, indicator, ht, neg_div, mul_neg, neg_mul]

/-- Abel regularization is an even bounded weighting of the absolutely integrable
kernel obtained by local constant subtraction. -/
theorem hilbertAbelIntegral_eq_regularized {f : ℝ → ℝ} {x R : ℝ}
    (hg : Integrable (hilbertRegularizedKernel f x R)) {ε : ℝ} (hε : 0 < ε) :
    hilbertAbelIntegral f x ε = Real.pi⁻¹ *
      ∫ t, hilbertRegularizedKernel f x R t * (t ^ 2 / (ε ^ 2 + t ^ 2)) := by
  have hc : Integrable (fun t ↦ hilbertAbelKernel ε t *
      {s : ℝ | |s| < R}.indicator (fun _ ↦ f x) t) := by
    apply (integrable_hilbertLocalConstant R (f x)).bdd_mul
      (show Measurable (hilbertAbelKernel ε) by
        unfold hilbertAbelKernel; fun_prop).aestronglyMeasurable
    exact Eventually.of_forall (fun t ↦ abs_hilbertAbelKernel_le hε t)
  have heq : (fun t ↦ hilbertAbelKernel ε t * f (x - t)) =
      (fun t ↦ Real.pi⁻¹ *
        (hilbertRegularizedKernel f x R t * (t ^ 2 / (ε ^ 2 + t ^ 2))) +
          hilbertAbelKernel ε t * {s : ℝ | |s| < R}.indicator (fun _ ↦ f x) t) := by
    funext t
    unfold hilbertAbelKernel hilbertRegularizedKernel
    by_cases ht : t = 0
    · simp [ht]
    · cas using ht
  rw [hilbertAbelIntegral, heq,
    integral_add ((integrable_mul_hilbertAbelWeight hg ε).const_mul _) hc,
    integral_hilbertAbelLocalConstant, add_zero, integral_const_mul]

/-- The Abel integrals converge to the convergent Hilbert principal value whenever
local constant subtraction gives an integrable kernel. -/
theorem tendsto_hilbertAbelIntegral_of_regularized {f : ℝ → ℝ} {x R : ℝ}
    (hg : Integrable (hilbertRegularizedKernel f x R)) :
    Tendsto (hilbertAbelIntegral f x) (𝓝[>] 0) (𝓝 (hilbertPV f x)) := by
  rw [(hasHilbertPV_of_regularized hg).hilbertPV_eq]
  have hlim : Tendsto (fun ε : ℝ ↦
      ∫ t, hilbertRegularizedKernel f x R t * (t ^ 2 / (ε ^ 2 + t ^ 2)))
      (𝓝[>] 0) (𝓝 (∫ t, hilbertRegularizedKernel f x R t)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun t ↦ ‖hilbertRegularizedKernel f x R t‖)
    · exact Eventually.of_forall (fun ε ↦
        (integrable_mul_hilbertAbelWeight hg ε).aestronglyMeasurable)
    · apply Eventually.of_forall
      intro ε
      filter_upwards with t
      rw [norm_mul, Real.norm_eq_abs (t ^ 2 / _),
        abs_of_nonneg (hilbertAbelWeight_mem_Icc ε t).1]
      exact mul_le_of_le_one_right (norm_nonneg _) (hilbertAbelWeight_mem_Icc ε t).2
    · exact hg.norm
    · filter_upwards [(volume : Measure ℝ).ae_ne 0] with t ht
      have hc : ContinuousAt (fun ε : ℝ ↦ t ^ 2 / (ε ^ 2 + t ^ 2)) 0 := by
        fun_prop (disch := simpa using pow_ne_zero 2 ht)
      simpa [ht] using
        (hc.tendsto.mono_left nhdsWithin_le_nhds).const_mul (hilbertRegularizedKernel f x R t)
  apply (hlim.const_mul Real.pi⁻¹).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hilbertAbelIntegral_eq_regularized hg hε).symm

/-- Differentiability at the evaluation point and `L¹` tails ensure that the Abel
integrals converge to the Hilbert principal value. -/
theorem tendsto_hilbertAbelIntegral_of_differentiableAt {f : ℝ → ℝ} (hf : Integrable f)
    {x : ℝ} (hdiff : DifferentiableAt ℝ f x) :
    Tendsto (hilbertAbelIntegral f x) (𝓝[>] 0) (𝓝 (hilbertPV f x)) := by
  obtain ⟨R, _, hg⟩ := exists_integrable_hilbertRegularizedKernel_of_differentiableAt hf hdiff
  exact tendsto_hilbertAbelIntegral_of_regularized hg

/-- The Fourier integral may be transferred between two integrable factors. -/
theorem integral_fourier_mul_eq {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∫ x, 𝓕 f x * g x) = ∫ x, f x * 𝓕 g x := by
  have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by ext; rfl
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ ℝ) Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf hg
  simpa only [hflip, Real.fourier_eq, VectorFourier.fourierIntegral,
    innerₗ_apply_apply, smul_eq_mul] using h

/-- The inverse Fourier integral may be transferred between two integrable factors. -/
theorem integral_fourierInv_mul_eq {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∫ x, 𝓕⁻ f x * g x) = ∫ x, f x * 𝓕⁻ g x := by
  have hflip : (-innerₗ ℝ).flip = -innerₗ ℝ := by ext; rfl
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := -innerₗ ℝ) Real.continuous_fourierChar (innerSL ℝ).continuous₂.neg hf hg
  simpa only [hflip, Real.fourierInv_eq, VectorFourier.fourierIntegral,
    LinearMap.neg_apply, innerₗ_apply_apply, neg_neg, smul_eq_mul] using h

/-- Modulating a frequency kernel translates its inverse Fourier integral. -/
theorem fourier_modulation_eq_fourierInv_sub (m : ℝ → ℂ) (x y : ℝ) :
    𝓕 (fun ξ ↦ Complex.exp ((2 * Real.pi * (ξ * x) : ℝ) * Complex.I) * m ξ) y =
      𝓕⁻ m (x - y) := by
  rw [Real.fourier_eq', Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [Real.inner_apply, smul_eq_mul]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  cas

/-- Fubini's theorem identifies an inverse multiplier integral with its kernel
integral. Only the multiplier and input need be integrable; the inverse kernel need not be. -/
theorem fourierInv_mul_fourier_eq_integral {m f : ℝ → ℂ}
    (hm : Integrable m) (hf : Integrable f) (x : ℝ) :
    𝓕⁻ (fun ξ ↦ m ξ * 𝓕 f ξ) x = ∫ y, 𝓕⁻ m (x - y) * f y := by
  let g : ℝ → ℂ := fun ξ ↦
    Complex.exp ((2 * Real.pi * (ξ * x) : ℝ) * Complex.I) * m ξ
  have hg : Integrable g := by
    apply hm.bdd_mul (c := 1) (by fun_prop)
    filter_upwards with ξ
    simp [Complex.norm_exp]
  calc
    _ = ∫ ξ, 𝓕 f ξ * g ξ := by
      rw [Real.fourierInv_eq']
      apply integral_congr_ae
      filter_upwards with ξ
      simp only [Real.inner_apply, smul_eq_mul, g]
      cas
    _ = ∫ y, f y * 𝓕 g y := integral_fourier_mul_eq hf hg
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      rw [fourier_modulation_eq_fourierInv_sub]
      exact mul_comm _ _

/-- The damped spectral integral is exactly the absolutely convergent real Abel integral. -/
theorem fourierInv_hilbertAbelSymbol_mul_fourier {f : ℝ → ℝ} (hf : Integrable f)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    𝓕⁻ (fun ξ ↦ hilbertAbelSymbol ε ξ * 𝓕 (fun y ↦ (f y : ℂ)) ξ) x =
      (hilbertAbelIntegral f x ε : ℂ) := by
  rw [fourierInv_mul_fourier_eq_integral (f := fun y ↦ (f y : ℂ))
    (integrable_hilbertAbelSymbol hε) hf.ofReal x]
  simp_rw [fourierInv_hilbertAbelSymbol hε, ← Complex.ofReal_mul]
  rw [integral_complex_ofReal]
  congr 1
  unfold hilbertAbelIntegral
  convert integral_sub_left_eq_self
    (fun t ↦ hilbertAbelKernel ε t * f (x - t)) volume x using 1
  simp

/-- Nonnegative Abel damping does not increase the Hilbert multiplier norm. -/
theorem norm_hilbertAbelSymbol_le_one {ε : ℝ} (hε : 0 ≤ ε) (ξ : ℝ) :
    ‖hilbertAbelSymbol ε ξ‖ ≤ 1 := by
  rw [hilbertAbelSymbol, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-(2 * Real.pi * ε) * |ξ|) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hε))
      (abs_nonneg _)
  exact (mul_le_of_le_one_left (Real.exp_nonneg _) (norm_hilbertSymbol_le_one ξ)).trans he

/-- Removing Abel damping converges pointwise in frequency, including at frequency zero. -/
theorem tendsto_hilbertAbelSymbol (ξ : ℝ) :
    Tendsto (fun ε ↦ hilbertAbelSymbol ε ξ) (𝓝[>] 0) (𝓝 (hilbertSymbol ξ)) := by
  have hc : Continuous (fun ε : ℝ ↦ hilbertAbelSymbol ε ξ) := by
    unfold hilbertAbelSymbol
    fun_prop
  simpa [hilbertAbelSymbol] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-- With an integrable Fourier-side input, the damped inverse integrals converge
pointwise to the inverse integral of the undamped Hilbert multiplier. -/
theorem tendsto_fourierInv_hilbertAbelSymbol_mul {g : ℝ → ℂ} (hg : Integrable g)
    (x : ℝ) :
    Tendsto (fun ε ↦ 𝓕⁻ (fun ξ ↦ hilbertAbelSymbol ε ξ * g ξ) x) (𝓝[>] 0)
      (𝓝 (𝓕⁻ (fun ξ ↦ hilbertSymbol ξ * g ξ) x)) := by
  simp only [Real.fourierInv_eq', Real.inner_apply, smul_eq_mul]
  apply tendsto_integral_filter_of_dominated_convergence (fun ξ ↦ ‖g ξ‖)
  · apply Eventually.of_forall
    intro ε
    exact (by fun_prop : AEStronglyMeasurable
      (fun ξ : ℝ ↦ Complex.exp ((2 * Real.pi * (ξ * x) : ℝ) * Complex.I)) volume).mul
        ((measurable_hilbertSymbol.aestronglyMeasurable.mul (by fun_prop)).mul
          hg.aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards with ξ
    simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self,
      Real.exp_zero, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_hilbertAbelSymbol_le_one hε.le ξ)
  · exact hg.norm
  · filter_upwards with ξ
    exact ((tendsto_hilbertAbelSymbol ξ).mul_const (g ξ)).const_mul _

/-- For an integrable real input with integrable Fourier transform, differentiability
at `x` identifies its convergent principal value with the undamped Fourier integral. -/
theorem hilbertPV_eq_fourierInv_of_differentiableAt {f : ℝ → ℝ} (hf : Integrable f)
    (hfourier : Integrable (𝓕 (fun y ↦ (f y : ℂ))))
    {x : ℝ} (hdiff : DifferentiableAt ℝ f x) :
    (hilbertPV f x : ℂ) =
      𝓕⁻ (fun ξ ↦ hilbertSymbol ξ * 𝓕 (fun y ↦ (f y : ℂ)) ξ) x := by
  have hpv := (Complex.continuous_ofReal.tendsto (hilbertPV f x)).comp
    (tendsto_hilbertAbelIntegral_of_differentiableAt hf hdiff)
  have hspec := tendsto_fourierInv_hilbertAbelSymbol_mul hfourier x
  apply tendsto_nhds_unique hpv
  apply hspec.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact fourierInv_hilbertAbelSymbol_mul_fourier hf hε x

/-- On an `L¹ ∩ L²` representative the inverse Fourier integral agrees almost
everywhere with the concrete `L²` inverse Fourier transform. The proof tests both
against compactly supported smooth functions and uses Mathlib's distribution compatibility. -/
theorem fourierInv_eq_L2_ae {g : ℝ → ℂ} (hg : Integrable g)
    (G : ComplexL2) (hG : g =ᵐ[volume] G) :
    𝓕⁻ g =ᵐ[volume] (𝓕⁻ G : ComplexL2) :=
  Fourier.fourierInvIntegral_eq_L2_ae hg G hG

/-- For a real Schwartz function, its principal value is almost everywhere
the concrete spectral `L²` Hilbert transform of its complexification. -/
theorem hilbertPV_eq_hilbertTransform_ae_schwartz (f : 𝓢(ℝ, ℝ)) :
    (fun x ↦ (hilbertPV f x : ℂ)) =ᵐ[volume]
      hilbertTransform ((f.postcompCLM Complex.ofRealCLM).toLp 2) := by
  let g : 𝓢(ℝ, ℂ) := f.postcompCLM Complex.ofRealCLM
  have hg : (g : ℝ → ℂ) = fun x ↦ (f x : ℂ) := by
    funext x
    simp [g]
  have hfourier : Integrable (𝓕 (fun x ↦ (f x : ℂ))) := by
    rw [← hg, ← SchwartzMap.fourier_coe]
    exact (𝓕 g).integrable
  have hsymbol : Integrable (fun ξ ↦ hilbertSymbol ξ * 𝓕 (fun x ↦ (f x : ℂ)) ξ) :=
    hfourier.bdd_mul measurable_hilbertSymbol.aestronglyMeasurable
      (Eventually.of_forall norm_hilbertSymbol_le_one)
  have hrep : (fun ξ ↦ hilbertSymbol ξ * 𝓕 (fun x ↦ (f x : ℂ)) ξ) =ᵐ[volume]
      hilbertMultiplier (𝓕 (g.toLp 2)) := by
    rw [SchwartzMap.toLp_fourier_eq]
    filter_upwards [coe_hilbertMultiplier ((𝓕 g).toLp 2), (𝓕 g).coeFn_toLp 2] with ξ hξ hgξ
    rw [hξ, hgξ, ← hg, SchwartzMap.fourier_coe]
  have hbridge := fourierInv_eq_L2_ae hsymbol _ hrep
  filter_upwards [hbridge] with x hx
  rw [hilbertPV_eq_fourierInv_of_differentiableAt f.integrable hfourier
    ((f.smooth ⊤).differentiable (by simp)).differentiableAt]
  exact hx.trans (congrArg (fun F : ComplexL2 ↦ F x) (hilbertTransform_apply (g.toLp 2))).symm

/-- The Schwartz bridge is independent of the chosen `L²` representative of the input.
Only the input representative is specified; the output equality is proved. -/
theorem hilbertPV_eq_hilbertTransform_ae_schwartz_of_ae (f : 𝓢(ℝ, ℝ))
    (F : ComplexL2) (hF : (fun x ↦ (f x : ℂ)) =ᵐ[volume] F) :
    (fun x ↦ (hilbertPV f x : ℂ)) =ᵐ[volume] hilbertTransform F := by
  have hrep : (f.postcompCLM Complex.ofRealCLM).toLp 2 = F := by
    apply Lp.ext
    exact ((f.postcompCLM Complex.ofRealCLM).coeFn_toLp 2).trans hF
  simpa only [hrep] using hilbertPV_eq_hilbertTransform_ae_schwartz f

/-- Every smooth compactly supported real function has a convergent Hilbert principal
value at every point. -/
theorem hasHilbertPV_of_contDiff_compactSupport {f : ℝ → ℝ}
    (hsmooth : ContDiff ℝ ∞ f) (hsupp : HasCompactSupport f) (x : ℝ) :
    HasHilbertPV f x (hilbertPV f x) :=
  hasHilbertPV_of_differentiableAt (hsupp.toSchwartzMap hsmooth).integrable
    (hsmooth.differentiable (by simp)).differentiableAt

/-- For a smooth compactly supported real input, its convergent principal value agrees
almost everywhere with the concrete spectral Hilbert transform of any `L²` representative. -/
theorem hilbertPV_eq_hilbertTransform_ae_of_contDiff_compactSupport {f : ℝ → ℝ}
    (hsmooth : ContDiff ℝ ∞ f) (hsupp : HasCompactSupport f)
    (F : ComplexL2) (hF : (fun x ↦ (f x : ℂ)) =ᵐ[volume] F) :
    (fun x ↦ (hilbertPV f x : ℂ)) =ᵐ[volume] hilbertTransform F :=
  hilbertPV_eq_hilbertTransform_ae_schwartz_of_ae (hsupp.toSchwartzMap hsmooth) F hF

end

end PDE.Analysis
