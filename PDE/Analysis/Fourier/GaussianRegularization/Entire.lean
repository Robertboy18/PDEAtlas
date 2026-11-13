/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Complex.ContourShift.Gaussian

/-!
# Gaussian Fourier integrals of entire functions

Completing the square by a justified contour shift exposes Gaussian decay of
Fourier integrals with an entire vector-valued amplitude of exponential growth.
The phase parameter is arbitrary; the Fourier convention is obtained by
substituting `2 * π * y`.
-/

@[expose] public noncomputable section

open MeasureTheory Complex

namespace PDE.Analysis.Fourier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem phase_smul_exp_growth
    {f : ℂ → E} {a C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ z, ‖f z‖ ≤ C * Real.exp (a * (|z.re| + |z.im|))) (k : ℝ) (z : ℂ) :
    ‖Complex.exp ((k : ℂ) * I * z) • f z‖ ≤
      C * Real.exp ((a + |k|) * (|z.re| + |z.im|)) := by
  have hn : ‖Complex.exp ((k : ℂ) * I * z)‖ = Real.exp (-k * z.im) := by
    simp [Complex.norm_exp, mul_re, mul_im]
  have hl : -k * z.im ≤ |k| * |z.im| := by
    simpa only [abs_mul, abs_neg] using le_abs_self (-k * z.im)
  rw [norm_smul, hn]
  calc
    _ ≤ Real.exp (-k * z.im) * (C * Real.exp (a * (|z.re| + |z.im|))) :=
      mul_le_mul_of_nonneg_left (hg z) (Real.exp_pos _).le
    _ = C * Real.exp (-k * z.im + a * (|z.re| + |z.im|)) := by
      rw [Real.exp_add]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (abs_nonneg k) (abs_nonneg z.re)]

/-- Completing the square in a Gaussian Fourier integral is valid for an
entire amplitude of exponential growth. The contour shift is proved from that
growth bound; it is not an additional hypothesis. -/
theorem integral_gaussian_phase_smul_eq_shift
    {f : ℂ → E} (hf : Differentiable ℂ f)
    {b a C : ℝ} (hb : 0 < b) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hg : ∀ z, ‖f z‖ ≤ C * Real.exp (a * (|z.re| + |z.im|))) (k : ℝ) :
    (∫ x : ℝ, Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2 + (k : ℂ) * I * x) • f x) =
      Complex.exp (-(k ^ 2 / (4 * b) : ℝ) : ℂ) •
        ∫ x : ℝ, Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2) •
          f (x + (k / (2 * b) : ℝ) * I) := by
  have hshift := integral_gaussian_smul_horizontal_shift
    (f := fun z ↦ Complex.exp ((k : ℂ) * I * z) • f z)
    (by fun_prop) hb (add_nonneg ha (abs_nonneg k)) hC
    (phase_smul_exp_growth hC hg k) (k / (2 * b))
  have heq (x : ℝ) :
      -(b : ℂ) * (x + (k / (2 * b) : ℝ) * I) ^ 2 +
          (k : ℂ) * I * (x + (k / (2 * b) : ℝ) * I) =
        (-(k ^ 2 / (4 * b) : ℝ) : ℂ) + -(b : ℂ) * (x : ℂ) ^ 2 := by
    have hb' : (b : ℂ) ≠ 0 := ofReal_ne_zero.mpr hb.ne'
    push_cast
    field_simp
    ring_nf
    simp only [I_sq]
    ring
  calc
    _ = ∫ x : ℝ, Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2) •
        (Complex.exp ((k : ℂ) * I * x) • f x) := by
      simp only [Complex.exp_add, smul_smul]
    _ = ∫ x : ℝ, Complex.exp (-(b : ℂ) * (x + (k / (2 * b) : ℝ) * I) ^ 2) •
        (Complex.exp ((k : ℂ) * I * (x + (k / (2 * b) : ℝ) * I)) •
          f (x + (k / (2 * b) : ℝ) * I)) := hshift.symm
    _ = ∫ x : ℝ, Complex.exp (-(k ^ 2 / (4 * b) : ℝ) : ℂ) •
        (Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2) •
          f (x + (k / (2 * b) : ℝ) * I)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [smul_smul, ← Complex.exp_add, heq]
    _ = _ := integral_smul _ _

private theorem norm_gaussian_real_smul_shift_le
    {f : ℂ → E} {b a C : ℝ} (hb : 0 < b) (hC : 0 ≤ C)
    (hg : ∀ z, ‖f z‖ ≤ C * Real.exp (a * (|z.re| + |z.im|))) (x c : ℝ) :
    ‖Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2) • f (x + c * I)‖ ≤
      (C * Real.exp (a * |c| + a ^ 2 / (2 * b))) *
        Real.exp (-(b / 2) * x ^ 2) := by
  apply (mul_le_mul_iff_right₀ (Real.exp_pos (b * c ^ 2))).mp
  calc
    _ = ‖Complex.exp (-(b : ℂ) * (x + c * I) ^ 2) • f (x + c * I)‖ := by
      have hr : ‖Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2)‖ =
          Real.exp (-b * x ^ 2) := by
        simp only [Complex.norm_exp, neg_mul, ← ofReal_pow, ← ofReal_mul,
          ← ofReal_neg, ofReal_re]
      rw [norm_smul, norm_smul, hr, GaussianFourier.norm_cexp_neg_mul_sq_add_mul_I]
      simp only [ofReal_re, ofReal_im, mul_zero, zero_mul, sub_zero]
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ (C * Real.exp (b * c ^ 2 + a * |c| + a ^ 2 / (2 * b))) *
        Real.exp (-(b / 2) * x ^ 2) :=
      norm_gaussian_smul_le_of_exp_growth hb hC hg x c
    _ = _ := by
      rw [show b * c ^ 2 + a * |c| + a ^ 2 / (2 * b) =
        b * c ^ 2 + (a * |c| + a ^ 2 / (2 * b)) by ring, Real.exp_add]
      ring

/-- An explicit Gaussian decay estimate for a Fourier integral with an entire
amplitude of exponential growth. This is a bound on the kernel amplitude,
independent of any solution class for a differential equation. -/
theorem norm_integral_gaussian_phase_smul_le
    {f : ℂ → E} (hf : Differentiable ℂ f)
    {b a C : ℝ} (hb : 0 < b) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hg : ∀ z, ‖f z‖ ≤ C * Real.exp (a * (|z.re| + |z.im|))) (k : ℝ) :
    ‖∫ x : ℝ, Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2 + (k : ℂ) * I * x) • f x‖ ≤
      C * √(Real.pi / (b / 2)) *
        Real.exp (-(k ^ 2 / (4 * b)) + a * |k / (2 * b)| + a ^ 2 / (2 * b)) := by
  let c := k / (2 * b)
  have hinner :
      ‖∫ x : ℝ, Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2) • f (x + c * I)‖ ≤
        (C * Real.exp (a * |c| + a ^ 2 / (2 * b))) *
          √(Real.pi / (b / 2)) := by
    calc
      _ ≤ ∫ x : ℝ, (C * Real.exp (a * |c| + a ^ 2 / (2 * b))) *
          Real.exp (-(b / 2) * x ^ 2) :=
        norm_integral_le_of_norm_le ((integrable_exp_neg_mul_sq (half_pos hb)).const_mul _)
          (ae_of_all _ (fun x ↦ norm_gaussian_real_smul_shift_le hb hC hg x c))
      _ = _ := by rw [integral_const_mul, integral_gaussian]
  rw [integral_gaussian_phase_smul_eq_shift hf hb ha hC hg k, norm_smul,
    Complex.norm_exp, neg_re, ofReal_re]
  calc
    _ ≤ Real.exp (-(k ^ 2 / (4 * b))) *
        ((C * Real.exp (a * |c| + a ^ 2 / (2 * b))) *
          √(Real.pi / (b / 2))) :=
      mul_le_mul_of_nonneg_left hinner (Real.exp_pos _).le
    _ = _ := by
      simp only [Real.exp_add]
      dsimp only [c]
      ring

end PDE.Analysis.Fourier
