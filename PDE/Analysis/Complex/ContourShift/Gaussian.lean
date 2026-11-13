/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Complex.ContourShift.Horizontal
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Gaussian contour shifts for functions of exponential growth

A Gaussian weight makes horizontal line integrals of an entire vector-valued
function integrable when that function has at most exponential growth. The
vertical sides of the Cauchy rectangles then vanish at infinity.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Complex
open scoped Topology

namespace PDE.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem linear_abs_le_quadratic {b : ℝ} (hb : 0 < b) (a x : ℝ) :
    a * |x| ≤ b / 2 * x ^ 2 + a ^ 2 / (2 * b) := by
  have h := two_mul_le_add_mul_sq (a := |x|) (b := a) hb
  rw [sq_abs] at h
  ring_nf at h ⊢
  linarith

/-- Pointwise Gaussian domination on a horizontal line. -/
theorem norm_gaussian_smul_le_of_exp_growth
    {f : ℂ → E} {b a C : ℝ} (hb : 0 < b) (hC : 0 ≤ C)
    (hg : ∀ z, ‖f z‖ ≤ C * Real.exp (a * (|z.re| + |z.im|))) (x y : ℝ) :
    ‖Complex.exp (-(b : ℂ) * (x + y * I) ^ 2) • f (x + y * I)‖ ≤
      (C * Real.exp (b * y ^ 2 + a * |y| + a ^ 2 / (2 * b))) *
        Real.exp (-(b / 2) * x ^ 2) := by
  rw [norm_smul, GaussianFourier.norm_cexp_neg_mul_sq_add_mul_I]
  simp only [ofReal_re, ofReal_im, mul_zero, zero_mul, sub_zero]
  have hg' := hg (x + y * I)
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im,
    sub_zero, add_zero, add_im, mul_im, mul_one, zero_add] at hg'
  calc
    _ ≤ Real.exp (-(b * x ^ 2 - b * y ^ 2)) *
        (C * Real.exp (a * (|x| + |y|))) :=
      mul_le_mul_of_nonneg_left hg' (Real.exp_pos _).le
    _ = C * Real.exp (-(b * x ^ 2 - b * y ^ 2) + a * (|x| + |y|)) := by
      rw [Real.exp_add]
      ring
    _ ≤ C * Real.exp ((b * y ^ 2 + a * |y| + a ^ 2 / (2 * b)) +
        (-(b / 2) * x ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.exp_le_exp.mpr
      nlinarith [linear_abs_le_quadratic hb a x]
    _ = _ := by rw [Real.exp_add]; ring

/-- Exponential growth is dominated by the Gaussian on every horizontal line. -/
theorem integrable_gaussian_smul_of_exp_growth
    {f : ℂ → E} (hf : Continuous f) {b a C : ℝ} (hb : 0 < b) (hC : 0 ≤ C)
    (hg : ∀ z, ‖f z‖ ≤ C * Real.exp (a * (|z.re| + |z.im|))) (y : ℝ) :
    Integrable (fun x : ℝ ↦
      Complex.exp (-(b : ℂ) * (x + y * I) ^ 2) • f (x + y * I)) := by
  apply ((integrable_exp_neg_mul_sq (half_pos hb)).const_mul
    (C * Real.exp (b * y ^ 2 + a * |y| + a ^ 2 / (2 * b)))).mono'
  · exact (by fun_prop : Continuous (fun x : ℝ ↦
      Complex.exp (-(b : ℂ) * (x + y * I) ^ 2) • f (x + y * I))).aestronglyMeasurable
  · exact ae_of_all _ (fun x ↦ norm_gaussian_smul_le_of_exp_growth hb hC hg x y)

/-- The integral along a vertical segment retains Gaussian decay in its real
coordinate, uniformly over the segment. -/
theorem norm_vertical_integral_gaussian_smul_le
    {f : ℂ → E} {b a C : ℝ} (hb : 0 < b) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hg : ∀ z, ‖f z‖ ≤ C * Real.exp (a * (|z.re| + |z.im|))) (c T : ℝ) :
    ‖∫ y : ℝ in (0 : ℝ)..c,
      Complex.exp (-(b : ℂ) * (T + y * I) ^ 2) • f (T + y * I)‖ ≤
      (C * Real.exp (b * c ^ 2 + a * |c| + a ^ 2 / (2 * b)) *
        Real.exp (-(b / 2) * T ^ 2)) * |c| := by
  have hbound (y : ℝ) (hy : y ∈ Set.uIoc (0 : ℝ) c) :
      ‖Complex.exp (-(b : ℂ) * (T + y * I) ^ 2) • f (T + y * I)‖ ≤
        C * Real.exp (b * c ^ 2 + a * |c| + a ^ 2 / (2 * b)) *
          Real.exp (-(b / 2) * T ^ 2) := by
    have habs : |y| ≤ |c| := by
      simpa using Set.abs_sub_left_of_mem_uIcc (Set.uIoc_subset_uIcc hy)
    apply (norm_gaussian_smul_le_of_exp_growth hb hC hg T y).trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.exp_le_exp.mpr
    have hs := mul_le_mul_of_nonneg_left (sq_le_sq.mpr habs) hb.le
    have hl := mul_le_mul_of_nonneg_left habs ha
    linarith
  simpa only [sub_zero] using intervalIntegral.norm_integral_le_of_norm_le_const hbound

/-- Gaussian weighting makes the vertical boundary error vanish, derived
solely from the exponential growth bound. -/
theorem tendsto_vertical_error_gaussian_smul
    {f : ℂ → E} {b a C : ℝ} (hb : 0 < b) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hg : ∀ z, ‖f z‖ ≤ C * Real.exp (a * (|z.re| + |z.im|))) (c : ℝ) :
    Tendsto (fun T : ℝ ↦
      I • (∫ y : ℝ in (0 : ℝ)..c,
        Complex.exp (-(b : ℂ) * (T + y * I) ^ 2) • f (T + y * I)) -
      I • (∫ y : ℝ in (0 : ℝ)..c,
        Complex.exp (-(b : ℂ) * (-T + y * I) ^ 2) • f (-T + y * I)))
      atTop (𝓝 0) := by
  let K := C * Real.exp (b * c ^ 2 + a * |c| + a ^ 2 / (2 * b))
  have hgauss : Tendsto (fun T : ℝ ↦ Real.exp (-(b / 2) * T ^ 2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (neg_lt_zero.mpr (half_pos hb)))
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hmajorant : Tendsto (fun T : ℝ ↦ 2 * (K *
      Real.exp (-(b / 2) * T ^ 2) * |c|)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using ((hgauss.const_mul K).mul_const |c|).const_mul 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmajorant
    (fun _ ↦ norm_nonneg _)
  intro T
  calc
    _ ≤ ‖I • (∫ y : ℝ in (0 : ℝ)..c,
          Complex.exp (-(b : ℂ) * (T + y * I) ^ 2) • f (T + y * I))‖ +
        ‖I • (∫ y : ℝ in (0 : ℝ)..c,
          Complex.exp (-(b : ℂ) * (-T + y * I) ^ 2) • f (-T + y * I))‖ :=
      norm_sub_le _ _
    _ ≤ K * Real.exp (-(b / 2) * T ^ 2) * |c| +
        K * Real.exp (-(b / 2) * T ^ 2) * |c| := by
      simp only [norm_smul, norm_I, one_mul]
      apply add_le_add (norm_vertical_integral_gaussian_smul_le hb ha hC hg c T)
      simpa only [ofReal_neg, neg_sq] using
        norm_vertical_integral_gaussian_smul_le hb ha hC hg c (-T)
    _ = _ := by ring

/-- A Gaussian-weighted entire function of exponential growth has the same
integral on every horizontal line. All integrability and vertical decay
conditions are proved from the growth bound. -/
theorem integral_gaussian_smul_horizontal_shift
    {f : ℂ → E} (hf : Differentiable ℂ f)
    {b a C : ℝ} (hb : 0 < b) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hg : ∀ z, ‖f z‖ ≤ C * Real.exp (a * (|z.re| + |z.im|))) (c : ℝ) :
    (∫ x : ℝ, Complex.exp (-(b : ℂ) * (x + c * I) ^ 2) • f (x + c * I)) =
      ∫ x : ℝ, Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2) • f x := by
  apply integral_horizontal_shift_of_tendsto
    (f := fun z ↦ Complex.exp (-(b : ℂ) * z ^ 2) • f z) (by fun_prop) c
  · simpa only [ofReal_zero, zero_mul, add_zero] using
      integrable_gaussian_smul_of_exp_growth hf.continuous hb hC hg 0
  · exact integrable_gaussian_smul_of_exp_growth hf.continuous hb hC hg c
  · exact tendsto_vertical_error_gaussian_smul hb ha hC hg c

end PDE.Analysis
