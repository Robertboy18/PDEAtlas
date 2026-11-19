/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Basic.Real.Sign

/-!
# Gaussian boundary values and Fresnel integrals

The oscillatory Gaussian on the real axis is interpreted by positive Gaussian
damping. Its boundary value contains the phase factor determined by the sign of
the quadratic coefficient. `tendsto_integral_damped_fresnel` is the one-dimensional
integral in step 1 of Evans's proof of Lemma 2 of §4.5.3(b), at `y = 0`, in the limit
`δ → 0` taken in step 2, and `fresnel_coefficient` evaluates `(π / (-i b))^(1/2)` as Evans
evaluates `(-iλ)^(1/2)` after (44). The Gaussian integral is Mathlib's
`integral_gaussian_complex`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.5.3(b), Lemma 2, (41), p. 221, and steps 1 and 2
  of its proof, (42)-(44), pp. 221-222. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Complex
open scoped Topology

namespace PDE.Analysis.StationaryPhase

/-- The square root on the positive imaginary axis has argument `π / 4`. -/
theorem cpow_half_mul_I {r : ℝ} (hr : 0 < r) :
    ((r : ℂ) * I) ^ (1 / 2 : ℂ) =
      (Real.sqrt r : ℂ) * Complex.exp (Real.pi / 4 * I) := by
  rw [Complex.cpow_def_of_ne_zero
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') I_ne_zero),
    Complex.log_ofReal_mul hr I_ne_zero, Complex.log_I, add_mul, Complex.exp_add]
  congr 1
  · rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hr.le]
    norm_num
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
      Complex.ofReal_log hr.le]
  · congr 1
    ring

/-- The square root on the negative imaginary axis has argument `-π / 4`. -/
theorem cpow_half_mul_neg_I {r : ℝ} (hr : 0 < r) :
    ((r : ℂ) * -I) ^ (1 / 2 : ℂ) =
      (Real.sqrt r : ℂ) * Complex.exp (-(Real.pi / 4) * I) := by
  rw [Complex.cpow_def_of_ne_zero
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') (neg_ne_zero.mpr I_ne_zero)),
    Complex.log_ofReal_mul hr (neg_ne_zero.mpr I_ne_zero), Complex.log_neg_I,
    add_mul, Complex.exp_add]
  congr 1
  · rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hr.le]
    norm_num
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
      Complex.ofReal_log hr.le]
  · congr 1
    ring

/-- The boundary value of the Gaussian coefficient, with its sign-dependent phase. -/
theorem fresnel_coefficient {b : ℝ} (hb : b ≠ 0) :
    ((Real.pi : ℂ) / (-(b : ℂ) * I)) ^ (1 / 2 : ℂ) =
      (Real.sqrt (Real.pi / |b|) : ℂ) *
        Complex.exp (Real.pi / 4 * (Real.sign b : ℂ) * I) := by
  rcases lt_or_gt_of_ne hb with hb | hb
  · have heq : (Real.pi : ℂ) / (-(b : ℂ) * I) =
        ((Real.pi / -b : ℝ) : ℂ) * -I := by
      push_cast
      field_simp
      simp [I_sq, div_eq_mul_inv]
    rw [heq, cpow_half_mul_neg_I (div_pos Real.pi_pos (neg_pos.mpr hb)),
      abs_of_neg hb, Real.sign_of_neg hb]
    congr 2
    push_cast
    ring
  · have heq : (Real.pi : ℂ) / (-(b : ℂ) * I) =
        ((Real.pi / b : ℝ) : ℂ) * I := by
      push_cast
      field_simp
      simp [I_sq, div_eq_mul_inv]
    rw [heq, cpow_half_mul_I (div_pos Real.pi_pos hb),
      abs_of_pos hb, Real.sign_of_pos hb]
    simp

/-- Abel-regularized Fresnel integral for a nonzero real quadratic coefficient. -/
theorem tendsto_integral_damped_fresnel {b : ℝ} (hb : b ≠ 0) :
    Tendsto (fun ε : ℝ ↦ ∫ x : ℝ,
      Complex.exp (-((ε : ℂ) - b * I) * (x : ℂ) ^ 2))
      (𝓝[>] 0)
      (𝓝 ((Real.sqrt (Real.pi / |b|) : ℂ) *
        Complex.exp (Real.pi / 4 * (Real.sign b : ℂ) * I))) := by
  have hne : -(b : ℂ) * I ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hb)) I_ne_zero
  have hslit : (Real.pi : ℂ) / (-(b : ℂ) * I) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    right
    simp [Complex.div_im, Complex.normSq_mul, hb, Real.pi_ne_zero]
  have ht : Tendsto (fun ε : ℝ ↦ (ε : ℂ) - b * I) (𝓝[>] 0)
      (𝓝 (-(b : ℂ) * I)) := by
    simpa using
      (Complex.continuous_ofReal.tendsto 0 |>.mono_left nhdsWithin_le_nhds).sub_const
        ((b : ℂ) * I)
  have hlim := (tendsto_const_nhds.div ht hne).cpow
    (tendsto_const_nhds (x := (1 / 2 : ℂ))) hslit
  rw [fresnel_coefficient hb] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (integral_gaussian_complex (by simpa using hε)).symm

end PDE.Analysis.StationaryPhase
