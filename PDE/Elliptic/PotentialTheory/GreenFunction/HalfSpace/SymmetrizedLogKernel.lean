/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.BiotSavartKernel
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Real.Pi.Bounds
import PDE.Analysis.Complex.PlanarRealPart

/-!
# The symmetrized fundamental solution in holomorphic form

For a density odd in both coordinates, the stream function is
`∫_{ℝ²₊₊} Φₛ(x, y) ω(y) dy` with the four-image kernel `Φₛ = symmetrizedKernel Φ`,
`Φ(v) = -(2π)⁻¹ log |v|`. With `z = x₀ + i x₁` and `w = y₀ + i y₁` the images are
`z - w`, `z + w̄`, `z - w̄`, `z + w`, so

`Φₛ(x, y) = -(2π)⁻¹ (log |z² - w²| - log |z² - w̄²|) = Re H(z, w)`,
`H(z, w) = -(2π)⁻¹ (log(1 - z²/w²) - log(1 - z²/w̄²))`

for `|z| < |w|`. `H` is holomorphic in `z` there, with

`H' = π⁻¹ (z/(w² - z²) - z/(w̄² - z²))`,
`H'' = π⁻¹ ((w² + z²)/(w² - z²)² - (w̄² + z²)/(w̄² - z²)²)`,

and its derivatives are the symmetrized velocity and velocity-gradient kernels:
`Re(H' eⱼ) = gⱼₛ(x, y)` and `Re(H'' eᵢ eⱼ) = π⁻¹ kᵢⱼₛ(x, y)` with `e₀ = 1`, `e₁ = i`.

The kernel decays like `|w|⁻²` in `w`, which is what makes the stream function of a vorticity
decaying like `|y|^(-β)`, `β > 0`, converge when the four images are grouped in one integrand.

## Main definitions

* `symmetrizedLogKernel`: the holomorphic kernel `H(z, w)`.
* `symmetrizedLogKernelDeriv`, `symmetrizedLogKernelSecondDeriv`: its derivatives `H'` and `H''`
  in `z`.

## Main results

* `hasDerivAt_symmetrizedLogKernel`, `hasDerivAt_symmetrizedLogKernelDeriv`: `H` and `H'` are
  holomorphic in `z` for `|z| < |w|`, with derivatives `H'` and `H''`.
* `re_symmetrizedLogKernel`: `Re H(𝔠 x, 𝔠 y) = Φₛ(x, y)` for `|x| < |y|`.
* `re_symmetrizedLogKernelDeriv_mul`: `Re(H'(𝔠 x, 𝔠 y) eⱼ) = gⱼₛ(x, y)` for `|x| < |y|`.
* `re_symmetrizedLogKernelSecondDeriv_mul_mul`: `Re(H''(𝔠 x, 𝔠 y) eᵢ eⱼ) = π⁻¹ kᵢⱼₛ(x, y)` for
  `|x| < |y|`.
* `norm_symmetrizedLogKernel_le`, `norm_symmetrizedLogKernelDeriv_le`,
  `norm_symmetrizedLogKernelSecondDeriv_le`: for `2|z| ≤ |w|`, `|H| ≤ (3/(2π)) |z|²/|w|²`,
  `|H'| ≤ (8/(3π)) |z|/|w|²` and `|H''| ≤ 2/|w|²`.
* `norm_symmetrizedLogKernelSecondDeriv_sub_le`: `|H''(z, w) - H''(0, w)| ≤ (104/(9π)) |z|²/|w|⁴`
  for `2|z| ≤ |w|`.
* `symmetrizedKernel_zero_one_origin`, `symmetrizedKernel_zero_zero_origin`: `K₁ₛ(0, y) = 4 K₁(y)`
  and `K₂ₛ(0, y) = 0`.
-/

@[expose] public section

noncomputable section

open Set Complex PotentialTheory PotentialTheory.Planar
open scoped ComplexConjugate

namespace GreenFunction

local notation "𝔠" => (Complex.orthonormalBasisOneI.repr.symm : ℝ^2 → ℂ)

/-- The symmetrized logarithmic kernel in holomorphic form,
`H(z, w) = -(2π)⁻¹ (log(1 - z²/w²) - log(1 - z²/w̄²))`. For `|z| < |w|` its real part at
`z = 𝔠 x`, `w = 𝔠 y` is `symmetrizedKernel (fundamentalSolution 2) x y`. -/
def symmetrizedLogKernel (z w : ℂ) : ℂ :=
  ((-(1 / (2 * Real.pi)) : ℝ) : ℂ) *
    (Complex.log (1 - z ^ 2 / w ^ 2) - Complex.log (1 - z ^ 2 / conj w ^ 2))

/-- The derivative `∂_z H(z, w) = π⁻¹ (z/(w² - z²) - z/(w̄² - z²))`. -/
def symmetrizedLogKernelDeriv (z w : ℂ) : ℂ :=
  ((1 / Real.pi : ℝ) : ℂ) * (z / (w ^ 2 - z ^ 2) - z / (conj w ^ 2 - z ^ 2))

/-- The second derivative `∂_z² H(z, w) = π⁻¹ ((w² + z²)/(w² - z²)² - (w̄² + z²)/(w̄² - z²)²)`. -/
def symmetrizedLogKernelSecondDeriv (z w : ℂ) : ℂ :=
  ((1 / Real.pi : ℝ) : ℂ) *
    ((w ^ 2 + z ^ 2) / (w ^ 2 - z ^ 2) ^ 2 - (conj w ^ 2 + z ^ 2) / (conj w ^ 2 - z ^ 2) ^ 2)

section Algebra

variable {z w : ℂ}

/-- `|z| < |w|` forces `w ≠ 0`. -/
private theorem ne_zero_of_norm_lt (h : ‖z‖ < ‖w‖) : w ≠ 0 := by
  rintro rfl
  simp at h
  linarith [norm_nonneg z]

/-- `|z| < |w|` forces `z - w ≠ 0`. -/
private theorem sub_ne_zero_of_norm_lt (h : ‖z‖ < ‖w‖) : z - w ≠ 0 := by
  intro h'
  rw [sub_eq_zero.mp h'] at h
  exact lt_irrefl _ h

/-- `|z| < |w|` forces `z + w ≠ 0`. -/
private theorem add_ne_zero_of_norm_lt (h : ‖z‖ < ‖w‖) : z + w ≠ 0 := by
  intro h'
  rw [eq_neg_of_add_eq_zero_left h', norm_neg] at h
  exact lt_irrefl _ h

/-- `|z| < |w|` forces `w² - z² ≠ 0`. -/
theorem sq_sub_sq_ne_zero_of_norm_lt (h : ‖z‖ < ‖w‖) : w ^ 2 - z ^ 2 ≠ 0 := by
  rw [sq_sub_sq]
  exact mul_ne_zero (by rw [add_comm]; exact add_ne_zero_of_norm_lt h)
    (by rw [← neg_sub, neg_ne_zero]; exact sub_ne_zero_of_norm_lt h)

/-- `|w|² - |z|² ≤ |w² - z²|`. -/
private theorem norm_sq_sub_sq_le (z w : ℂ) : ‖w‖ ^ 2 - ‖z‖ ^ 2 ≤ ‖w ^ 2 - z ^ 2‖ := by
  have := norm_sub_norm_le (w ^ 2) (z ^ 2)
  simpa [norm_pow] using this

/-- `|z²/w²| = |z|²/|w|²`. -/
private theorem norm_sq_div_sq (z w : ℂ) : ‖z ^ 2 / w ^ 2‖ = ‖z‖ ^ 2 / ‖w‖ ^ 2 := by
  rw [norm_div, norm_pow, norm_pow]

/-- For `|u| < 1`, `1 - u` lies in the slit plane, where `Complex.log` is holomorphic. -/
private theorem one_sub_mem_slitPlane {u : ℂ} (hu : ‖u‖ < 1) : 1 - u ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  left
  have := Complex.re_le_norm u
  simp only [sub_re, one_re]
  linarith

/-- `|z| < |w|` gives `|z²/w²| < 1`. -/
private theorem norm_sq_div_sq_lt (h : ‖z‖ < ‖w‖) : ‖z ^ 2 / w ^ 2‖ < 1 := by
  have hw : 0 < ‖w‖ := lt_of_le_of_lt (norm_nonneg z) h
  rw [norm_sq_div_sq, div_lt_one (by positivity)]
  exact pow_lt_pow_left₀ h (norm_nonneg z) (by norm_num)

/-- For `|z| < |w|`, `z ↦ log(1 - z²/w²)` has derivative `-2z/(w² - z²)`. -/
private theorem hasDerivAt_log_one_sub (w : ℂ) {z : ℂ} (h : ‖z‖ < ‖w‖) :
    HasDerivAt (fun z ↦ Complex.log (1 - z ^ 2 / w ^ 2)) (-(2 * z) / (w ^ 2 - z ^ 2)) z := by
  have hw := ne_zero_of_norm_lt h
  have hd : HasDerivAt (fun z : ℂ ↦ 1 - z ^ 2 / w ^ 2) (-(2 * z / w ^ 2)) z := by
    have := ((hasDerivAt_id z).pow 2).div_const (w ^ 2)
    simpa using (this.const_sub 1)
  convert hd.clog (one_sub_mem_slitPlane (norm_sq_div_sq_lt h)) using 1
  have hz := sq_sub_sq_ne_zero_of_norm_lt h
  field_simp

/-- `H` is holomorphic in `z` for `|z| < |w|`, with derivative `symmetrizedLogKernelDeriv`. -/
theorem hasDerivAt_symmetrizedLogKernel (h : ‖z‖ < ‖w‖) :
    HasDerivAt (fun z ↦ symmetrizedLogKernel z w) (symmetrizedLogKernelDeriv z w) z := by
  have h' : ‖z‖ < ‖conj w‖ := by rwa [norm_conj]
  have hd := ((hasDerivAt_log_one_sub w h).sub (hasDerivAt_log_one_sub (conj w) h')).const_mul
    ((-(1 / (2 * Real.pi)) : ℝ) : ℂ)
  refine hd.congr_deriv ?_
  have h1 := sq_sub_sq_ne_zero_of_norm_lt h
  have h2 := sq_sub_sq_ne_zero_of_norm_lt h'
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [symmetrizedLogKernelDeriv]
  push_cast
  field_simp
  ring

/-- `H'` is holomorphic in `z` for `|z| < |w|`, with derivative
`symmetrizedLogKernelSecondDeriv`. -/
theorem hasDerivAt_symmetrizedLogKernelDeriv (h : ‖z‖ < ‖w‖) :
    HasDerivAt (fun z ↦ symmetrizedLogKernelDeriv z w) (symmetrizedLogKernelSecondDeriv z w) z := by
  have h' : ‖z‖ < ‖conj w‖ := by rwa [norm_conj]
  have h1 := sq_sub_sq_ne_zero_of_norm_lt h
  have h2 := sq_sub_sq_ne_zero_of_norm_lt h'
  have hq (a : ℂ) (ha : a ^ 2 - z ^ 2 ≠ 0) :
      HasDerivAt (fun z : ℂ ↦ z / (a ^ 2 - z ^ 2)) ((a ^ 2 + z ^ 2) / (a ^ 2 - z ^ 2) ^ 2) z := by
    have hden : HasDerivAt (fun z : ℂ ↦ a ^ 2 - z ^ 2) (-(2 * z)) z := by
      simpa using ((hasDerivAt_id z).pow 2).const_sub (a ^ 2)
    refine ((hasDerivAt_id' z).div hden ha).congr_deriv ?_
    field_simp
    ring
  have hd := ((hq w h1).sub (hq (conj w) h2)).const_mul ((1 / Real.pi : ℝ) : ℂ)
  exact hd

/-- `|H(z, w)| ≤ (3/(2π)) |z|²/|w|²` for `2|z| ≤ |w|`, `w ≠ 0`. -/
theorem norm_symmetrizedLogKernel_le (hw : w ≠ 0) (h : 2 * ‖z‖ ≤ ‖w‖) :
    ‖symmetrizedLogKernel z w‖ ≤ 3 / (2 * Real.pi) * (‖z‖ ^ 2 / ‖w‖ ^ 2) := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hq : ‖z‖ ^ 2 / ‖w‖ ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg z]
  have hlog (a : ℂ) (ha : ‖a‖ = ‖w‖) :
      ‖Complex.log (1 - z ^ 2 / a ^ 2)‖ ≤ 3 / 2 * (‖z‖ ^ 2 / ‖w‖ ^ 2) := by
    have hu : ‖-(z ^ 2 / a ^ 2)‖ ≤ 1 / 2 := by
      rw [norm_neg, norm_sq_div_sq, ha]; linarith
    have := norm_log_one_add_half_le_self hu
    rw [norm_neg, norm_sq_div_sq, ha, ← sub_eq_add_neg] at this
    exact this
  have hπ : 0 < Real.pi := Real.pi_pos
  unfold symmetrizedLogKernel
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
  calc 1 / (2 * Real.pi) * ‖Complex.log (1 - z ^ 2 / w ^ 2) - Complex.log (1 - z ^ 2 / conj w ^ 2)‖
      ≤ 1 / (2 * Real.pi) * (3 / 2 * (‖z‖ ^ 2 / ‖w‖ ^ 2) + 3 / 2 * (‖z‖ ^ 2 / ‖w‖ ^ 2)) := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add (hlog w rfl) (hlog (conj w) (norm_conj w)))
    _ = 3 / (2 * Real.pi) * (‖z‖ ^ 2 / ‖w‖ ^ 2) := by ring

/-- For `2|z| ≤ |w|` and `|a| = |w|`, `(3/4) |w|² ≤ |a² - z²|`. -/
private theorem three_quarters_le (h : 2 * ‖z‖ ≤ ‖w‖) (a : ℂ) (ha : ‖a‖ = ‖w‖) :
    3 / 4 * ‖w‖ ^ 2 ≤ ‖a ^ 2 - z ^ 2‖ := by
  have := norm_sq_sub_sq_le z a
  rw [ha] at this
  nlinarith [norm_nonneg z]

/-- `|H'(z, w)| ≤ (8/(3π)) |z|/|w|²` for `2|z| ≤ |w|`, `w ≠ 0`. -/
theorem norm_symmetrizedLogKernelDeriv_le (hw : w ≠ 0) (h : 2 * ‖z‖ ≤ ‖w‖) :
    ‖symmetrizedLogKernelDeriv z w‖ ≤ 8 / (3 * Real.pi) * (‖z‖ / ‖w‖ ^ 2) := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hπ : 0 < Real.pi := Real.pi_pos
  have hterm (a : ℂ) (ha : ‖a‖ = ‖w‖) : ‖z / (a ^ 2 - z ^ 2)‖ ≤ 4 / 3 * (‖z‖ / ‖w‖ ^ 2) := by
    have hden := three_quarters_le h a ha
    rw [norm_div]
    rw [div_le_iff₀ (by nlinarith [norm_nonneg z] : (0 : ℝ) < ‖a ^ 2 - z ^ 2‖)]
    calc ‖z‖ = 4 / 3 * (‖z‖ / ‖w‖ ^ 2) * (3 / 4 * ‖w‖ ^ 2) := by field_simp
      _ ≤ 4 / 3 * (‖z‖ / ‖w‖ ^ 2) * ‖a ^ 2 - z ^ 2‖ := by gcongr
  unfold symmetrizedLogKernelDeriv
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc 1 / Real.pi * ‖z / (w ^ 2 - z ^ 2) - z / (conj w ^ 2 - z ^ 2)‖
      ≤ 1 / Real.pi * (4 / 3 * (‖z‖ / ‖w‖ ^ 2) + 4 / 3 * (‖z‖ / ‖w‖ ^ 2)) := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add (hterm w rfl) (hterm (conj w) (norm_conj w)))
    _ = 8 / (3 * Real.pi) * (‖z‖ / ‖w‖ ^ 2) := by ring

/-- `|H''(z, w)| ≤ 2/|w|²` for `2|z| ≤ |w|`, `w ≠ 0`. -/
theorem norm_symmetrizedLogKernelSecondDeriv_le (hw : w ≠ 0) (h : 2 * ‖z‖ ≤ ‖w‖) :
    ‖symmetrizedLogKernelSecondDeriv z w‖ ≤ 2 / ‖w‖ ^ 2 := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hπ : 3 < Real.pi := Real.pi_gt_three
  have hterm (a : ℂ) (ha : ‖a‖ = ‖w‖) :
      ‖(a ^ 2 + z ^ 2) / (a ^ 2 - z ^ 2) ^ 2‖ ≤ 20 / 9 / ‖w‖ ^ 2 := by
    have hden := three_quarters_le h a ha
    have hnum : ‖a ^ 2 + z ^ 2‖ ≤ 5 / 4 * ‖w‖ ^ 2 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_pow, norm_pow, ha]
      nlinarith [norm_nonneg z]
    rw [norm_div, norm_pow]
    have hd0 : 0 < ‖a ^ 2 - z ^ 2‖ := by nlinarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc ‖a ^ 2 + z ^ 2‖ * ‖w‖ ^ 2 ≤ 5 / 4 * ‖w‖ ^ 2 * ‖w‖ ^ 2 := by gcongr
      _ = 20 / 9 * (3 / 4 * ‖w‖ ^ 2) ^ 2 := by ring
      _ ≤ 20 / 9 * ‖a ^ 2 - z ^ 2‖ ^ 2 := by gcongr
  unfold symmetrizedLogKernelSecondDeriv
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc 1 / Real.pi * ‖(w ^ 2 + z ^ 2) / (w ^ 2 - z ^ 2) ^ 2 -
        (conj w ^ 2 + z ^ 2) / (conj w ^ 2 - z ^ 2) ^ 2‖
      ≤ 1 / Real.pi * (20 / 9 / ‖w‖ ^ 2 + 20 / 9 / ‖w‖ ^ 2) := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add (hterm w rfl) (hterm (conj w) (norm_conj w)))
    _ ≤ 2 / ‖w‖ ^ 2 := by
        rw [show 1 / Real.pi * (20 / 9 / ‖w‖ ^ 2 + 20 / 9 / ‖w‖ ^ 2) =
          40 / (9 * Real.pi) * (1 / ‖w‖ ^ 2) by ring, show 2 / ‖w‖ ^ 2 = 2 * (1 / ‖w‖ ^ 2) by ring]
        gcongr
        rw [div_le_iff₀ (by positivity)]
        linarith

/-- **The Hessian remainder**: `|H''(z, w) - H''(0, w)| ≤ (104/(9π)) |z|²/|w|⁴` for `2|z| ≤ |w|`,
`w ≠ 0`; it expresses the quadratic vanishing of the velocity gradient of a far density. -/
theorem norm_symmetrizedLogKernelSecondDeriv_sub_le (hw : w ≠ 0) (h : 2 * ‖z‖ ≤ ‖w‖) :
    ‖symmetrizedLogKernelSecondDeriv z w - symmetrizedLogKernelSecondDeriv 0 w‖ ≤
      104 / (9 * Real.pi) * (‖z‖ ^ 2 / ‖w‖ ^ 4) := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hπ : 0 < Real.pi := Real.pi_pos
  have hterm (a : ℂ) (ha : ‖a‖ = ‖w‖) :
      ‖(a ^ 2 + z ^ 2) / (a ^ 2 - z ^ 2) ^ 2 - (a ^ 2 + 0 ^ 2) / (a ^ 2 - 0 ^ 2) ^ 2‖ ≤
        52 / 9 * (‖z‖ ^ 2 / ‖w‖ ^ 4) := by
    have ha0 : a ≠ 0 := by rw [← norm_ne_zero_iff, ha]; exact hwpos.ne'
    have hlt : ‖z‖ < ‖a‖ := by rw [ha]; nlinarith [norm_nonneg z]
    have hd := sq_sub_sq_ne_zero_of_norm_lt hlt
    have hden := three_quarters_le h a ha
    have hnum : ‖3 * a ^ 2 - z ^ 2‖ ≤ 13 / 4 * ‖w‖ ^ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_pow, norm_pow, ha, show ‖(3 : ℂ)‖ = 3 by norm_num]
      nlinarith [norm_nonneg z]
    rw [show (a ^ 2 + z ^ 2) / (a ^ 2 - z ^ 2) ^ 2 - (a ^ 2 + 0 ^ 2) / (a ^ 2 - 0 ^ 2) ^ 2 =
        z ^ 2 * (3 * a ^ 2 - z ^ 2) / (a ^ 2 * (a ^ 2 - z ^ 2) ^ 2) by field_simp; ring]
    rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, ha]
    have hd0 : 0 < ‖a ^ 2 - z ^ 2‖ := by nlinarith
    rw [div_le_iff₀ (by positivity)]
    calc ‖z‖ ^ 2 * ‖3 * a ^ 2 - z ^ 2‖ ≤ ‖z‖ ^ 2 * (13 / 4 * ‖w‖ ^ 2) := by gcongr
      _ = 52 / 9 * (‖z‖ ^ 2 / ‖w‖ ^ 4) * (‖w‖ ^ 2 * (3 / 4 * ‖w‖ ^ 2) ^ 2) := by
          field_simp; ring
      _ ≤ 52 / 9 * (‖z‖ ^ 2 / ‖w‖ ^ 4) * (‖w‖ ^ 2 * ‖a ^ 2 - z ^ 2‖ ^ 2) := by gcongr
  unfold symmetrizedLogKernelSecondDeriv
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
    show (w ^ 2 + z ^ 2) / (w ^ 2 - z ^ 2) ^ 2 - (conj w ^ 2 + z ^ 2) / (conj w ^ 2 - z ^ 2) ^ 2 -
      ((w ^ 2 + 0 ^ 2) / (w ^ 2 - 0 ^ 2) ^ 2 - (conj w ^ 2 + 0 ^ 2) / (conj w ^ 2 - 0 ^ 2) ^ 2) =
      ((w ^ 2 + z ^ 2) / (w ^ 2 - z ^ 2) ^ 2 - (w ^ 2 + 0 ^ 2) / (w ^ 2 - 0 ^ 2) ^ 2) -
      ((conj w ^ 2 + z ^ 2) / (conj w ^ 2 - z ^ 2) ^ 2 -
        (conj w ^ 2 + 0 ^ 2) / (conj w ^ 2 - 0 ^ 2) ^ 2) by ring]
  calc 1 / Real.pi * ‖((w ^ 2 + z ^ 2) / (w ^ 2 - z ^ 2) ^ 2 -
          (w ^ 2 + 0 ^ 2) / (w ^ 2 - 0 ^ 2) ^ 2) -
        ((conj w ^ 2 + z ^ 2) / (conj w ^ 2 - z ^ 2) ^ 2 -
          (conj w ^ 2 + 0 ^ 2) / (conj w ^ 2 - 0 ^ 2) ^ 2)‖
      ≤ 1 / Real.pi * (52 / 9 * (‖z‖ ^ 2 / ‖w‖ ^ 4) + 52 / 9 * (‖z‖ ^ 2 / ‖w‖ ^ 4)) := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add (hterm w rfl) (hterm (conj w) (norm_conj w)))
    _ = 104 / (9 * Real.pi) * (‖z‖ ^ 2 / ‖w‖ ^ 4) := by ring

/-- At the origin the symmetrized Hessian kernel `K₂ₛ(0, y)` vanishes. -/
theorem symmetrizedKernel_zero_zero_origin (y : ℝ^2) :
    symmetrizedKernel (hessianKernel 0 0) 0 y = 0 := by
  unfold symmetrizedKernel
  simp only [zero_sub, zero_add, hessianKernel_neg, hessianKernel_zero_zero_coordinateReflection]
  ring

end Algebra

section RealPart

/-- The gradient kernel in complex form: `gⱼ(v) = -(2π)⁻¹ Re(eⱼ / v)`. -/
theorem gradientKernel_eq_re (j : Fin 2) (v : ℝ^2) :
    gradientKernel j v =
      -(1 / (2 * Real.pi)) * (𝔠 (EuclideanSpace.single j 1) / 𝔠 v).re := by
  have e0 := PDE.Analysis.orthonormalBasisOneI_repr_symm_single_zero
  have e1 := PDE.Analysis.orthonormalBasisOneI_repr_symm_single_one
  rw [gradientKernel_eq_div]
  have hn : Complex.normSq (𝔠 v) = ‖v‖ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, LinearIsometryEquiv.norm_map]
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, e0, div_eq_mul_inv, one_mul,
      inv_re, hn, orthonormalBasisOneI_repr_symm_re]
    ring
  · simp only [Fin.mk_one, Fin.isValue, e1, div_eq_mul_inv, mul_re,
      I_re, zero_mul, I_im, one_mul, zero_sub, inv_im, hn, orthonormalBasisOneI_repr_symm_im]
    ring

/-- The planar Hessian kernels in complex form: `kᵢⱼ(v) = Re(eᵢ eⱼ / (2 v²))`. -/
theorem hessianKernel_eq_re (i j : Fin 2) (v : ℝ^2) :
    hessianKernel i j v = (𝔠 (EuclideanSpace.single i 1) * 𝔠 (EuclideanSpace.single j 1) /
      (2 * 𝔠 v ^ 2)).re := by
  have e0 := PDE.Analysis.orthonormalBasisOneI_repr_symm_single_zero
  have e1 := PDE.Analysis.orthonormalBasisOneI_repr_symm_single_one
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, e0, one_mul,
      hessianKernel_zero_zero_eq_re]
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, e0,
      e1, one_mul, hessianKernel_zero_one_eq_neg_im, div_eq_mul_inv,
      mul_re, I_re, zero_mul, I_im, one_mul, zero_sub]
  · simp only [Fin.mk_one, Fin.zero_eta, Fin.isValue, e0,
      e1, mul_one, hessianKernel_one_zero,
      hessianKernel_zero_one_eq_neg_im, div_eq_mul_inv, mul_re, I_re, zero_mul, I_im, one_mul,
      zero_sub]
  · simp only [Fin.mk_one, Fin.isValue, e1, I_mul_I,
      hessianKernel_one_one, hessianKernel_zero_zero_eq_re, neg_div, neg_re]

variable {x y : ℝ^2}

/-- **The kernel identity**: `Re H(𝔠 x, 𝔠 y) = Φₛ(x, y)` for `|x| < |y|`. -/
theorem re_symmetrizedLogKernel (h : ‖x‖ < ‖y‖) :
    (symmetrizedLogKernel (𝔠 x) (𝔠 y)).re =
      symmetrizedKernel (fundamentalSolution 2) x y := by
  have hzw : ‖𝔠 x‖ < ‖𝔠 y‖ := by simpa only [LinearIsometryEquiv.norm_map] using h
  set z := 𝔠 x
  set w := 𝔠 y
  have hzw' : ‖z‖ < ‖conj w‖ := by rwa [norm_conj]
  have hw := ne_zero_of_norm_lt hzw
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have e1 : (1 - z ^ 2 / w ^ 2) = (w - z) * (w + z) / w ^ 2 := by field_simp; ring
  have e2 : (1 - z ^ 2 / conj w ^ 2) = (conj w - z) * (conj w + z) / conj w ^ 2 := by
    have : conj w ≠ 0 := by rwa [map_ne_zero]
    field_simp; ring
  have n1 : ‖w - z‖ ≠ 0 := by
    rw [norm_ne_zero_iff, ← neg_sub, neg_ne_zero]; exact sub_ne_zero_of_norm_lt hzw
  have n2 : ‖w + z‖ ≠ 0 := by
    rw [norm_ne_zero_iff, add_comm]; exact add_ne_zero_of_norm_lt hzw
  have n3 : ‖conj w - z‖ ≠ 0 := by
    rw [norm_ne_zero_iff, ← neg_sub, neg_ne_zero]; exact sub_ne_zero_of_norm_lt hzw'
  have n4 : ‖conj w + z‖ ≠ 0 := by
    rw [norm_ne_zero_iff, add_comm]; exact add_ne_zero_of_norm_lt hzw'
  have hw2 : ‖w‖ ^ 2 ≠ 0 := by positivity
  unfold symmetrizedLogKernel symmetrizedKernel
  rw [re_ofReal_mul, sub_re, log_re, log_re, e1, e2, norm_div, norm_div, norm_mul, norm_mul,
    norm_pow, norm_pow, norm_conj, Real.log_div (mul_ne_zero n1 n2) hw2,
    Real.log_div (mul_ne_zero n3 n4) hw2, Real.log_mul n1 n2, Real.log_mul n3 n4]
  simp only [fundamentalSolution_two,
    ← LinearIsometryEquiv.norm_map Complex.orthonormalBasisOneI.repr.symm, map_sub, map_add,
    orthonormalBasisOneI_repr_symm_coordinateReflection_zero,
    orthonormalBasisOneI_repr_symm_coordinateReflection_one]
  rw [show z - -conj w = conj w + z by ring, show z - conj w = -(conj w - z) by ring,
    show z - w = -(w - z) by ring, show z + w = w + z by ring, norm_neg, norm_neg]
  ring

/-- **The velocity kernels**: `Re(H'(𝔠 x, 𝔠 y) eⱼ) = gⱼₛ(x, y)` for `|x| < |y|`. -/
theorem re_symmetrizedLogKernelDeriv_mul (j : Fin 2) (h : ‖x‖ < ‖y‖) :
    (symmetrizedLogKernelDeriv (𝔠 x) (𝔠 y) * 𝔠 (EuclideanSpace.single j 1)).re =
      symmetrizedKernel (gradientKernel j) x y := by
  have hzw : ‖𝔠 x‖ < ‖𝔠 y‖ := by simpa only [LinearIsometryEquiv.norm_map] using h
  set z := 𝔠 x
  set w := 𝔠 y
  set e := 𝔠 (EuclideanSpace.single j 1)
  have hzw' : ‖z‖ < ‖conj w‖ := by rwa [norm_conj]
  have a1 := sub_ne_zero_of_norm_lt hzw
  have a2 := add_ne_zero_of_norm_lt hzw
  have a3 := sub_ne_zero_of_norm_lt hzw'
  have a4 := add_ne_zero_of_norm_lt hzw'
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold symmetrizedKernel
  simp only [gradientKernel_eq_re, map_sub, map_add,
    orthonormalBasisOneI_repr_symm_coordinateReflection_zero,
    orthonormalBasisOneI_repr_symm_coordinateReflection_one]
  rw [show z - -conj w = z + conj w by ring]
  have key : symmetrizedLogKernelDeriv z w * e =
      ((-(1 / (2 * Real.pi)) : ℝ) : ℂ) *
        (e / (z - w) - e / (z + conj w) - e / (z - conj w) + e / (z + w)) := by
    unfold symmetrizedLogKernelDeriv
    have b1 : w ^ 2 - z ^ 2 ≠ 0 := sq_sub_sq_ne_zero_of_norm_lt hzw
    have b2 : conj w ^ 2 - z ^ 2 ≠ 0 := sq_sub_sq_ne_zero_of_norm_lt hzw'
    push_cast
    field_simp
    ring
  rw [key, re_ofReal_mul]
  simp only [add_re, sub_re]
  ring

/-- **The velocity-gradient kernels**: `Re(H''(𝔠 x, 𝔠 y) eᵢ eⱼ) = π⁻¹ kᵢⱼₛ(x, y)` for
`|x| < |y|`. -/
theorem re_symmetrizedLogKernelSecondDeriv_mul_mul (i j : Fin 2) (h : ‖x‖ < ‖y‖) :
    (symmetrizedLogKernelSecondDeriv (𝔠 x) (𝔠 y) * 𝔠 (EuclideanSpace.single i 1) *
        𝔠 (EuclideanSpace.single j 1)).re =
      1 / Real.pi * symmetrizedKernel (hessianKernel i j) x y := by
  have hzw : ‖𝔠 x‖ < ‖𝔠 y‖ := by simpa only [LinearIsometryEquiv.norm_map] using h
  set z := 𝔠 x
  set w := 𝔠 y
  set e := 𝔠 (EuclideanSpace.single i 1) * 𝔠 (EuclideanSpace.single j 1)
  have hzw' : ‖z‖ < ‖conj w‖ := by rwa [norm_conj]
  have a1 := sub_ne_zero_of_norm_lt hzw
  have a2 := add_ne_zero_of_norm_lt hzw
  have a3 := sub_ne_zero_of_norm_lt hzw'
  have a4 := add_ne_zero_of_norm_lt hzw'
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold symmetrizedKernel
  simp only [hessianKernel_eq_re, map_sub, map_add,
    orthonormalBasisOneI_repr_symm_coordinateReflection_zero,
    orthonormalBasisOneI_repr_symm_coordinateReflection_one]
  rw [show z - -conj w = z + conj w by ring]
  have key : symmetrizedLogKernelSecondDeriv z w * 𝔠 (EuclideanSpace.single i 1) *
        𝔠 (EuclideanSpace.single j 1) =
      ((1 / Real.pi : ℝ) : ℂ) *
        (e / (2 * (z - w) ^ 2) - e / (2 * (z + conj w) ^ 2) - e / (2 * (z - conj w) ^ 2) +
          e / (2 * (z + w) ^ 2)) := by
    unfold symmetrizedLogKernelSecondDeriv
    have b1 : w ^ 2 - z ^ 2 ≠ 0 := sq_sub_sq_ne_zero_of_norm_lt hzw
    have b2 : conj w ^ 2 - z ^ 2 ≠ 0 := sq_sub_sq_ne_zero_of_norm_lt hzw'
    simp only [e]
    push_cast
    field_simp
    ring
  rw [key, re_ofReal_mul]
  simp only [add_re, sub_re]
  ring

/-- The symmetrized strain kernel at the origin: `K₁ₛ(0, y) = 4 K₁(y)`. -/
theorem symmetrizedKernel_zero_one_origin (y : ℝ^2) :
    symmetrizedKernel (hessianKernel 0 1) 0 y = 4 * hessianKernel 0 1 y := by
  unfold symmetrizedKernel
  simp only [zero_sub, zero_add, hessianKernel_neg, hessianKernel_zero_one_coordinateReflection]
  ring

end RealPart

end GreenFunction
