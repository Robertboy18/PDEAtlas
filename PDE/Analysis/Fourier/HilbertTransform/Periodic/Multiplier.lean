/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.Periodic.LogSinePotential
public import Mathlib.Analysis.Fourier.AddCircle
import PDE.Analysis.Calculus.Periodic
import PDE.Analysis.Fourier.PeriodicConvolution
import CAS.CEGA
import CAS.ExactTactic
import CAS.IntegrationTactic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Log
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# The periodic Hilbert transform as a Fourier multiplier

The log-sine potential `u (x) = (1 / π) ∫₀ᴸ f (y) log |sin (π (x - y) / L)| dy` of a function `f`
of period `L > 0` (`logSinePotential`) is the convolution over a period of `f` with the kernel
`(1 / π) log |sin (π z / L)|`. The Fourier coefficients of the kernel are computed here, so the
potential is a Fourier multiplier: on `[0, L]` the `n`-th coefficient of `u` is the `n`-th
coefficient of `f` times `-L / (2 π |n|)` for `n ≠ 0`, and times `-L log 2 / π` for `n = 0`
(`fourierCoeffOn_logSinePotential`, for every continuous `f` of period `L`). For `f` of class
`C¹` the derivative `u'` is the potential of `f'` (`hasDerivAt_logSinePotential`), so the
coefficients of `u'` are `-i sgn n` times those of `f` (`fourierCoeffOn_logSinePotential_deriv`).
The Fourier multiplier `-i sgn n` is the periodic Hilbert transform `H`, so this says `u' = H f`,
in the sense of Fourier coefficients. It is the Biot–Savart law (1.1) of Choi, Hou, Kiselev, Luo,
Šverák and Yao for their velocity (4.1). By Parseval's identity `H` does not increase the `L²`
norm over a period (`integral_sq_logSinePotential_deriv_le`), and the `L²` norm of `u` over a
period is at most `L log 2 / π` times that of `f` (`integral_sq_logSinePotential_le`).

The periodic Hilbert transform is not defined as an operator here, and the principal value
formula `(1 / L) p.v. ∫₀ᴸ f (y) cot (π (x - y) / L) dy` is not proved: the statements are about
the Fourier coefficients of `logSinePotential L (deriv f)`.

## Main results

* `integral_cos_mul_log_sin`: `∫₀^π cos (2 n s) log (sin s) ds = -π / (2 n)` for every natural
  number `n ≥ 1`. For `n = 0` the value `-π log 2` is Mathlib's `integral_log_sin_zero_pi`.
* `fourierCoeffOn_log_abs_sin`: for every `L > 0`, the Fourier coefficients on `[0, L]` of
  `log |sin (π z / L)|` are `-log 2` for `n = 0` and `-1 / (2 |n|)` for `n ≠ 0`.
  `integral_cos_mul_log_abs_sin` and `integral_sin_mul_log_abs_sin` are its cosine and sine
  parts.
* `fourierCoeffOn_logSinePotential`: the log-sine potential as a Fourier multiplier.
* `fourierCoeffOn_logSinePotential_deriv`: the derivative of the log-sine potential has the
  Fourier multiplier `-i sgn n` of the periodic Hilbert transform.
* `integral_sq_logSinePotential_le`, `integral_sq_logSinePotential_deriv_le`: the potential and
  its derivative are bounded in `L²` of a period by `f`.

## How it works

By the convolution form `u (x) = (1 / π) ∫₀ᴸ f (x - z) log |sin (π z / L)| dz`
(`logSinePotential_eq_integral_sub`) and `fourierCoeffOn_convolution`, the coefficients of `u`
are `L / π` times the products of the coefficients of `f` and of the kernel
`log |sin (π z / L)|`. The sine coefficients of the kernel vanish, by the reflection `z ↦ L - z`,
and its cosine coefficients are `(L / π) ∫₀^π cos (2 n s) log (sin s) ds`. For `n ≥ 1` an
integration by parts turns this integral into `-(1 / (2 n)) ∫₀^π cot s sin (2 n s) ds`, and
`cot s sin (2 n s)` is the trigonometric polynomial `2 cos s ∑_{i < n} cos ((2 i + 1) s)` by
Mathlib's `Real.sin_mul_sum_cos`, with integral `π` (`integral_cos_mul_sum_cos`). `cas` computes
the derivative of `log (sin s) sin (2 n s) / (2 n)` and the integral of `cos (2 j s)`. For the
derivative of the potential, the coefficients of `f'` are `2 π i n / L` times those of `f`, by
Mathlib's `fourierCoeffOn_of_hasDerivAt`. The `L²` bounds are
`integral_sq_le_of_norm_fourierCoeffOn_le` with the bounds `L log 2 / π` and `1` of the two
multipliers; the first uses `1 / 2 ≤ log 2`, which `cega` checks.

## References

* K. Choi, T. Y. Hou, A. Kiselev, G. Luo, V. Šverák, and Y. Yao, "On the finite-time blowup of a
  one-dimensional model for the three-dimensional axisymmetric Euler equations", *Comm. Pure
  Appl. Math.* 70 (2017), no. 11, 2218-2243; numbering of arXiv:1407.4776v2, (1.1) and the
  beginning of Section 4 with (4.1). <https://doi.org/10.1002/cpa.21697>
  <https://arxiv.org/abs/1407.4776v2>
-/

@[expose] public noncomputable section

open Set Real MeasureTheory Function

namespace PDE.Analysis

variable {L : ℝ} {f : ℝ → ℝ}

/-! ### The Fourier coefficients of the kernel -/

/-- `∫₀^π cos s ∑_{i < n} cos ((2 i + 1) s) ds = π / 2` for a natural number `n ≥ 1`. On
`(0, π)` the integrand is `cot s sin (2 n s) / 2`, by `Real.sin_mul_sum_cos`. -/
theorem integral_cos_mul_sum_cos {n : ℕ} (hn : n ≠ 0) :
    ∫ s in (0 : ℝ)..π, cos s * ∑ i ∈ Finset.range n, cos (2 * s * i + s) = π / 2 := by
  have hcos : ∀ j : ℕ, ∫ s in (0 : ℝ)..π, cos (2 * j * s) = if j = 0 then π else 0 := by
    intro j
    rcases eq_or_ne j 0 with rfl | hj
    · simp
    · have hj' : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj
      have h0 : sin (2 * (j : ℝ) * π) = 0 := by
        have h := Real.sin_nat_mul_pi (2 * j)
        push_cast at h
        exact h
      have h : ∫ s in (0 : ℝ)..π, cos (2 * j * s) = sin (2 * j * π) / (2 * j) := by
        cas using [hj']
      rw [ite_eq_right hj, h, h0, zero_div]
  have hcc : ∀ j : ℕ, IntervalIntegrable (fun s : ℝ ↦ cos (2 * j * s)) volume 0 π :=
    fun j ↦ Continuous.intervalIntegrable (by fun_prop) _ _
  have hterm : ∀ i : ℕ, ∫ s in (0 : ℝ)..π, cos s * cos (2 * s * i + s) =
      if i = 0 then π / 2 else 0 := by
    intro i
    have h : ∀ s : ℝ, cos s * cos (2 * s * i + s) =
        (cos (2 * (i + 1 : ℕ) * s) + cos (2 * i * s)) / 2 := by
      intro s
      rw [Real.cos_add_cos,
        (show (2 * ((i + 1 : ℕ) : ℝ) * s + 2 * i * s) / 2 = 2 * s * i + s by push_cast; cas),
        (show (2 * ((i + 1 : ℕ) : ℝ) * s - 2 * i * s) / 2 = s by push_cast; cas)]
      cas
    simp_rw [h]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hcc (i + 1)) (hcc i),
      hcos, hcos, ite_eq_right (Nat.add_one_ne_zero i)]
    split_ifs <;> cas
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [hterm]
    rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.mpr (Nat.pos_of_ne_zero hn))]
  · intro i _
    exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- For a natural number `n ≥ 1`, `∫₀^π cos (2 n s) log (sin s) ds = -π / (2 n)`. For `n = 0`
the integral is `-π log 2`, by `integral_log_sin_zero_pi`. -/
theorem integral_cos_mul_log_sin {n : ℕ} (hn : n ≠ 0) :
    ∫ s in (0 : ℝ)..π, cos (2 * n * s) * log (sin s) = -(π / (2 * n)) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hsin : ∀ s : ℝ,
      sin (2 * n * s) = 2 * sin s * ∑ i ∈ Finset.range n, cos (2 * s * i + s) := by
    intro s
    have h := Real.sin_mul_sum_cos n (2 * s) s
    rw [show 2 * s / 2 = s by cas, show (n : ℝ) * (2 * s) / 2 = n * s by cas,
      show ((n : ℝ) - 1) * (2 * s) / 2 + s = n * s by cas] at h
    rw [show 2 * (n : ℝ) * s = 2 * (n * s) by cas, Real.sin_two_mul]
    cas using [h]
  have hsum : Continuous fun s : ℝ ↦ ∑ i ∈ Finset.range n, cos (2 * s * i + s) := by fun_prop
  have hcont : Continuous fun s : ℝ ↦ log (sin s) * sin (2 * n * s) / (2 * n) := by
    have h : (fun s : ℝ ↦ log (sin s) * sin (2 * n * s) / (2 * n)) = fun s ↦
        sin s * log (sin s) * (∑ i ∈ Finset.range n, cos (2 * s * i + s)) / n := by
      funext s
      rw [hsin]
      cas
    rw [h]
    exact ((Real.continuous_mul_log.comp Real.continuous_sin).mul hsum).div_const _
  have hderiv : ∀ s ∈ Ioo 0 π, HasDerivAt (fun s : ℝ ↦ log (sin s) * sin (2 * n * s) / (2 * n))
      (cos s * (∑ i ∈ Finset.range n, cos (2 * s * i + s)) / n + cos (2 * n * s) * log (sin s))
      s := by
    intro s hs
    have hs0 : sin s ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hs.1 hs.2).ne'
    have h : HasDerivAt (fun s : ℝ ↦ log (sin s) * sin (2 * n * s) / (2 * n))
        (cos s / sin s * sin (2 * n * s) / (2 * n) + log (sin s) * cos (2 * n * s)) s := by
      cas using [hs0, hn']
    refine h.congr_deriv ?_
    rw [hsin]
    cas using [hs0, hn']
  have hint1 : IntervalIntegrable
      (fun s : ℝ ↦ cos s * (∑ i ∈ Finset.range n, cos (2 * s * i + s)) / n) volume 0 π :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hint2 : IntervalIntegrable (fun s : ℝ ↦ cos (2 * n * s) * log (sin s)) volume 0 π :=
    intervalIntegrable_log_sin.continuousOn_mul (Continuous.continuousOn (by fun_prop))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le pi_pos.le hcont.continuousOn
    hderiv (hint1.add hint2)
  rw [intervalIntegral.integral_add hint1 hint2, intervalIntegral.integral_div,
    integral_cos_mul_sum_cos hn] at h
  simp only [Real.sin_pi, Real.sin_zero, Real.log_zero, zero_mul, zero_div, sub_zero] at h
  rw [← div_div]
  cas using [h]

/-- The cosine coefficients over a period of the kernel `log |sin (π z / L)|`, for `L > 0`:
`∫₀ᴸ cos (2 π n z / L) log |sin (π z / L)| dz` is `-L log 2` for `n = 0` and `-L / (2 |n|)` for
an integer `n ≠ 0`. -/
theorem integral_cos_mul_log_abs_sin (hL : 0 < L) (n : ℤ) :
    ∫ z in (0 : ℝ)..L, cos (2 * π * n * z / L) * log |sin (π * z / L)| =
      L * (if n = 0 then -log 2 else -(1 / (2 * |(n : ℝ)|))) := by
  have hcosabs : ∀ y : ℝ, cos (|(n : ℝ)| * y) = cos (n * y) := by
    intro y
    rcases abs_cases (n : ℝ) with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
    · rw [h, neg_mul, Real.cos_neg]
  calc ∫ z in (0 : ℝ)..L, cos (2 * π * n * z / L) * log |sin (π * z / L)|
      = ∫ z in (0 : ℝ)..L, (fun s ↦ cos (2 * |(n : ℝ)| * s) * log (sin s)) (π / L * z) := by
        refine intervalIntegral.integral_congr fun z _ ↦ ?_
        change cos (2 * π * n * z / L) * log |sin (π * z / L)| =
          cos (2 * |(n : ℝ)| * (π / L * z)) * log (sin (π / L * z))
        rw [Real.log_abs, show π * z / L = π / L * z by cas,
          show 2 * |(n : ℝ)| * (π / L * z) = |(n : ℝ)| * (2 * (π / L * z)) by cas, hcosabs,
          show 2 * π * (n : ℝ) * z / L = n * (2 * (π / L * z)) by cas]
    _ = (π / L)⁻¹ • ∫ s in π / L * 0..π / L * L, cos (2 * |(n : ℝ)| * s) * log (sin s) :=
        intervalIntegral.integral_comp_mul_left
          (fun s ↦ cos (2 * |(n : ℝ)| * s) * log (sin s)) (div_pos pi_pos hL).ne'
    _ = L * (if n = 0 then -log 2 else -(1 / (2 * |(n : ℝ)|))) := by
        rw [mul_zero, div_mul_cancel₀ _ hL.ne', smul_eq_mul, inv_div]
        split_ifs with h
        · have h0 : ∀ s : ℝ, cos (2 * |(n : ℝ)| * s) * log (sin s) = log (sin s) := by
            intro s
            rw [h]
            simp
          simp_rw [h0, integral_log_sin_zero_pi]
          cas
        · have hm : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
          have hm0 : ((n.natAbs : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Int.natAbs_ne_zero.mpr h)
          rw [← hm, integral_cos_mul_log_sin (Int.natAbs_ne_zero.mpr h)]
          cas using [hm0]

/-- The sine coefficients over a period of the kernel `log |sin (π z / L)|` vanish, for
`L > 0` and every integer `n`. -/
theorem integral_sin_mul_log_abs_sin (hL : 0 < L) (n : ℤ) :
    ∫ z in (0 : ℝ)..L, sin (2 * π * n * z / L) * log |sin (π * z / L)| = 0 := by
  have hL0 : L ≠ 0 := hL.ne'
  have h1 := intervalIntegral.integral_comp_sub_left (a := 0) (b := L)
    (fun z ↦ sin (2 * π * n * z / L) * log |sin (π * z / L)|) L
  have h2 : ∀ z : ℝ, sin (2 * π * n * (L - z) / L) * log |sin (π * (L - z) / L)| =
      -(sin (2 * π * n * z / L) * log |sin (π * z / L)|) := by
    intro z
    rw [show 2 * π * (n : ℝ) * (L - z) / L = n * (2 * π) - 2 * π * n * z / L by cas using [hL0],
      Real.sin_int_mul_two_pi_sub, show π * (L - z) / L = π - π * z / L by cas using [hL0],
      Real.sin_pi_sub, neg_mul]
  have h3 : ∫ z in (0 : ℝ)..L, sin (2 * π * n * (L - z) / L) * log |sin (π * (L - z) / L)| =
      ∫ z in (0 : ℝ)..L, sin (2 * π * n * z / L) * log |sin (π * z / L)| := by
    rw [sub_self, sub_zero] at h1
    exact h1
  simp_rw [h2] at h3
  rw [intervalIntegral.integral_neg] at h3
  cas using [h3]

/-- **The Fourier coefficients of the log-sine kernel.** For `L > 0`, the Fourier coefficients
on a period `[0, L]` of the kernel `log |sin (π z / L)|` are `-log 2` for `n = 0` and
`-1 / (2 |n|)` for `n ≠ 0`. -/
theorem fourierCoeffOn_log_abs_sin (hL : 0 < L) (n : ℤ) :
    fourierCoeffOn hL (fun z ↦ ((log |sin (π * z / L)| : ℝ) : ℂ)) n =
      ((if n = 0 then -log 2 else -(1 / (2 * |(n : ℝ)|)) : ℝ) : ℂ) := by
  have hk := intervalIntegrable_log_abs_sin_zero L 0 L
  have hcR : IntervalIntegrable
      (fun z ↦ cos (2 * π * n * z / L) * log |sin (π * z / L)|) volume 0 L :=
    hk.continuousOn_mul (Continuous.continuousOn (by fun_prop))
  have hsR : IntervalIntegrable
      (fun z ↦ sin (2 * π * n * z / L) * log |sin (π * z / L)|) volume 0 L :=
    hk.continuousOn_mul (Continuous.continuousOn (by fun_prop))
  have hcC : IntervalIntegrable
      (fun z ↦ ((cos (2 * π * n * z / L) * log |sin (π * z / L)| : ℝ) : ℂ)) volume 0 L :=
    hcR.ofReal
  have hsC : IntervalIntegrable
      (fun z ↦ ((sin (2 * π * n * z / L) * log |sin (π * z / L)| : ℝ) : ℂ)) volume 0 L :=
    hsR.ofReal
  have hpt : ∀ z : ℝ, fourier (-n) (z : AddCircle (L - 0)) • ((log |sin (π * z / L)| : ℝ) : ℂ) =
      ((cos (2 * π * n * z / L) * log |sin (π * z / L)| : ℝ) : ℂ) -
        ((sin (2 * π * n * z / L) * log |sin (π * z / L)| : ℝ) : ℂ) * Complex.I := by
    intro z
    rw [fourier_coe_apply, smul_eq_mul,
      show 2 * (π : ℂ) * Complex.I * ((-n : ℤ) : ℂ) * (z : ℂ) / ((L - 0 : ℝ) : ℂ) =
        ((-(2 * π * n * z / L) : ℝ) : ℂ) * Complex.I by push_cast; cas,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
      Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_neg]
    cas
  rw [fourierCoeffOn_eq_integral]
  simp only [hpt]
  rw [intervalIntegral.integral_sub hcC (hsC.mul_const Complex.I),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal, integral_cos_mul_log_abs_sin hL,
    integral_sin_mul_log_abs_sin hL]
  simp only [sub_zero, Complex.ofReal_zero, zero_mul, Complex.real_smul]
  rw [← Complex.ofReal_mul, one_div, inv_mul_cancel_left₀ hL.ne']

/-! ### The potential and its derivative -/

/-- **The log-sine potential as a Fourier multiplier.** For a continuous function `f` of period
`L > 0`, the `n`-th Fourier coefficient on `[0, L]` of the potential `logSinePotential L f` is
the `n`-th coefficient of `f` times `-L log 2 / π` for `n = 0` and times `-L / (2 π |n|)` for
`n ≠ 0`. -/
theorem fourierCoeffOn_logSinePotential (hL : 0 < L) (hf : Continuous f) (hper : f.Periodic L)
    (n : ℤ) :
    fourierCoeffOn hL (fun x ↦ (logSinePotential L f x : ℂ)) n =
      ((if n = 0 then -(L * log 2 / π) else -(L / (2 * π * |(n : ℝ)|)) : ℝ) : ℂ) *
        fourierCoeffOn hL (fun x ↦ (f x : ℂ)) n := by
  have hfC : Continuous fun x ↦ (f x : ℂ) := Complex.continuous_ofReal.comp hf
  have hperC : (fun x ↦ (f x : ℂ)).Periodic (L - 0) := fun x ↦ by
    change ((f (x + (L - 0)) : ℝ) : ℂ) = f x
    rw [sub_zero, hper x]
  have hkC : IntervalIntegrable (fun z ↦ ((log |sin (π * z / L)| : ℝ) : ℂ)) volume 0 L :=
    (intervalIntegrable_log_abs_sin_zero L 0 L).ofReal
  have hconv := fourierCoeffOn_convolution hL hfC hperC hkC n
  have hpot : (fun x ↦ (logSinePotential L f x : ℂ)) = fun x ↦ (π : ℂ)⁻¹ *
      ∫ z in (0 : ℝ)..L, (f (x - z) : ℂ) * ((log |sin (π * z / L)| : ℝ) : ℂ) := by
    funext x
    rw [logSinePotential_eq_integral_sub hper x, Complex.ofReal_mul, Complex.ofReal_inv,
      ← intervalIntegral.integral_ofReal]
    simp only [Complex.ofReal_mul]
  rw [hpot, fourierCoeffOn.const_mul, hconv, fourierCoeffOn_log_abs_sin hL n]
  split_ifs <;> push_cast <;> cas

/-- **The derivative of the log-sine potential is the periodic Hilbert transform.** For a
function `f` of class `C¹` and of period `L > 0`, the `n`-th Fourier coefficient on `[0, L]` of
`logSinePotential L (deriv f)`, which is the derivative of the potential `logSinePotential L f`
by `hasDerivAt_logSinePotential`, is `-i sgn n` times the `n`-th coefficient of `f`. With the
potential as velocity and `f` as vorticity this is the Biot–Savart law (1.1) of Choi, Hou,
Kiselev, Luo, Šverák and Yao. -/
theorem fourierCoeffOn_logSinePotential_deriv (hL : 0 < L) (hf : ContDiff ℝ 1 f)
    (hper : f.Periodic L) (n : ℤ) :
    fourierCoeffOn hL (fun x ↦ (logSinePotential L (deriv f) x : ℂ)) n =
      -Complex.I * (n.sign : ℂ) * fourierCoeffOn hL (fun x ↦ (f x : ℂ)) n := by
  have hf' : Continuous (deriv f) := hf.continuous_deriv_one
  have hper' : (deriv f).Periodic L := hper.deriv
  have hfL : f L = f 0 := by simpa using hper 0
  rw [fourierCoeffOn_logSinePotential hL hf' hper']
  rcases eq_or_ne n 0 with rfl | hn
  · have h0 : fourierCoeffOn hL (fun x ↦ ((deriv f x : ℝ) : ℂ)) 0 = 0 := by
      have hi : ∫ x in (0 : ℝ)..L, deriv f x = 0 := by
        rw [intervalIntegral.integral_deriv_eq_sub (fun x _ ↦ hf.differentiable one_ne_zero x)
          (hf'.intervalIntegrable 0 L), hfL, sub_self]
      rw [fourierCoeffOn_eq_integral]
      simp only [neg_zero, fourier_zero, one_smul, intervalIntegral.integral_ofReal, hi,
        Complex.ofReal_zero, smul_zero]
    simp [h0]
  · have hderiv : ∀ x, x ∈ Set.uIcc 0 L →
        HasDerivAt (fun x ↦ (f x : ℂ)) ((deriv f x : ℝ) : ℂ) x :=
      fun x _ ↦ (hf.differentiable one_ne_zero x).hasDerivAt.ofReal_comp
    have hd := fourierCoeffOn_of_hasDerivAt hL hn hderiv (hf'.intervalIntegrable 0 L).ofReal
    have hnC : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
    have hπC : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
    rw [ite_eq_right hn, hd, hfL, sub_self, mul_zero, zero_sub]
    rcases hn.lt_or_gt with h | h
    · rw [Int.sign_eq_neg_one_of_neg h, abs_of_neg (show (n : ℝ) < 0 from Int.cast_lt_zero.mpr h)]
      push_cast
      cas using [hnC, hπC]
    · rw [Int.sign_eq_one_of_pos h, abs_of_pos (show (0 : ℝ) < n from Int.cast_pos.mpr h)]
      push_cast
      cas using [hnC, hπC]

/-- **The log-sine potential is bounded on `L²` of a period.** The potential
`u = logSinePotential L f` of a continuous function `f` of period `L > 0` satisfies
`∫₀ᴸ u² ≤ (L log 2 / π)² ∫₀ᴸ f²`. -/
theorem integral_sq_logSinePotential_le (hL : 0 < L) (hf : Continuous f) (hper : f.Periodic L) :
    ∫ x in (0 : ℝ)..L, logSinePotential L f x ^ 2 ≤
      (L * log 2 / π) ^ 2 * ∫ x in (0 : ℝ)..L, f x ^ 2 := by
  refine integral_sq_le_of_norm_fourierCoeffOn_le hL (continuous_logSinePotential hL hf hper) hf
    fun n ↦ ?_
  rw [fourierCoeffOn_logSinePotential hL hf hper n, norm_mul, Complex.norm_real,
    Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have hlog : 1 / 2 ≤ log 2 := by cega
  split_ifs with h
  · exact (abs_neg _).trans_le (abs_of_nonneg (by positivity)).le
  · have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs h
    rw [abs_neg, abs_of_nonneg (by positivity)]
    calc L / (2 * π * |(n : ℝ)|) ≤ L / (2 * π * 1) := by gcongr
      _ = L * (1 / 2) / π := by cas
      _ ≤ L * log 2 / π := by gcongr

/-- **The periodic Hilbert transform does not increase the `L²` norm over a period.** For a
function `f` of class `C¹` and of period `L > 0`, `∫₀ᴸ (u')² ≤ ∫₀ᴸ f²`, where
`u' = logSinePotential L (deriv f)` is the derivative of the log-sine potential of `f`. -/
theorem integral_sq_logSinePotential_deriv_le (hL : 0 < L) (hf : ContDiff ℝ 1 f)
    (hper : f.Periodic L) :
    ∫ x in (0 : ℝ)..L, logSinePotential L (deriv f) x ^ 2 ≤ ∫ x in (0 : ℝ)..L, f x ^ 2 := by
  have h : ∫ x in (0 : ℝ)..L, logSinePotential L (deriv f) x ^ 2 ≤
      1 ^ 2 * ∫ x in (0 : ℝ)..L, f x ^ 2 := by
    refine integral_sq_le_of_norm_fourierCoeffOn_le hL
      (continuous_logSinePotential hL hf.continuous_deriv_one hper.deriv) hf.continuous
      fun n ↦ ?_
    rw [fourierCoeffOn_logSinePotential_deriv hL hf hper n, norm_mul, norm_mul, norm_neg,
      Complex.norm_I, one_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rcases lt_trichotomy n 0 with h | rfl | h
    · rw [Int.sign_eq_neg_one_of_neg h]
      simp
    · simp
    · rw [Int.sign_eq_one_of_pos h]
      simp
  rwa [one_pow, one_mul] at h

end PDE.Analysis
