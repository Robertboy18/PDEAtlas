/-
Authors: Levent Alpöge, Tristan Buckmaster

The lemmas of this file come from modules of the Lean package of the paper
"Finite-time blow-up for the Navier–Stokes equations"
(https://github.com/tristanbuckmaster/navier-stokes, folder lean/, commit ad53419),
where they were steps of longer proofs. They were included in BlowupZoo
(https://github.com/lean-dojo/BlowupZoo, folder AtlasCandidates/) with the permission of the
authors (20 November 2026) and moved here from there; the file NOTICE of this repository records it.
-/
module

public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

set_option linter.style.header false

/-!
# The complex exponential and phases

The lemmas compute the modulus of `Complex.exp` of an imaginary number, multiply and conjugate
phases, use the periodicity of the exponential and bound the difference of two phases. The proofs
use `Complex.exp_add`, `Complex.norm_exp` and the lemmas of Mathlib on the trigonometric functions.

## Main results

* `PDE.Analysis.exp_neg_index_eq_conj_exp`: Write `θ κ = 2 * π * κ.1 * τ + κ.2 * φ` for `κ : ℤ × ℤ`
  and real `τ`, `φ`. Then `Complex.exp ((θ (-α) : ℂ) * I) = conj (Complex.exp ((θ α : ℂ) * I))`.
* `PDE.Analysis.exp_neg_mul_exp_index_sub`: Write `θ κ = 2 * π * κ.1 * τ + κ.2 * φ` for `κ : ℤ × ℤ`
  and real `τ`, `φ`. Then `Complex.exp (-((θ ι : ℂ) * I)) * Complex.exp ((θ α : ℂ) * I) =
  Complex.exp (-((θ (ι - α) : ℂ) * I))`.
* `PDE.Analysis.abs_sin_sub_self_le_cube`: For every real `t`, `|Real.sin t - t| ≤ 2 * |t| ^ 3`. For
  `|t| ≤ 1` this follows from the Taylor bound `Real.sin_bound`, and for `|t| > 1` from
  `|Real.sin t| ≤ 1` and `|t| ≤ |t| ^ 3`.
* `PDE.Analysis.abs_sin_sub_self_le_two_mul`: For every real `t`, `|Real.sin t - t| ≤ 2 * |t|`.
* `PDE.Analysis.coe_fourierChar_mul_coe_fourierChar`: For reals `a`, `b`:
  `(𝐞 a : ℂ) * (𝐞 b : ℂ) = (𝐞 (a + b) : ℂ)`, where `𝐞` is `Real.fourierChar` and its values on the
  circle are read as complex numbers.
* `PDE.Analysis.conj_exp_neg_int_mul_mul_I`: For `k : ℤ` and `θ : ℝ`, the complex conjugate of
  `Complex.exp (-(k * θ * I))` is `Complex.exp (k * θ * I)`, with `k` and `θ` coerced to `ℂ`.
* `PDE.Analysis.exp_add_int_mul_add_mul_I`: For real `U`, `V`, `θ` and an integer `a`, `Complex.exp
  (((U + (a : ℝ) * θ + V : ℝ) : ℂ) * Complex.I) = Complex.exp (((U + V : ℝ) : ℂ) * Complex.I) *
  Complex.exp ((θ : ℂ) * Complex.I) ^ a`.
* `PDE.Analysis.exp_arg_exp_mul_mul_I`: For a nonzero complex `z` and real `φ`, `Complex.exp
  ((Complex.arg (Complex.exp ((φ : ℂ) * Complex.I) * z) : ℂ) * Complex.I) = Complex.exp ((φ : ℂ) *
  Complex.I) * Complex.exp ((Complex.arg z : ℂ) * Complex.I)`.

There are 36 further lemmas of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open Real
open scoped FourierTransform

namespace PDE.Analysis

/-- For every real `t`, `|Real.sin t - t| ≤ 2 * |t| ^ 3`. For `|t| ≤ 1` this follows from the Taylor
bound `Real.sin_bound`, and for `|t| > 1` from `|Real.sin t| ≤ 1` and `|t| ≤ |t| ^ 3`. -/
theorem abs_sin_sub_self_le_cube (t : ℝ) : |Real.sin t - t| ≤ 2 * |t| ^ 3 := by
  rcases le_or_gt |t| 1 with ht | ht
  · have hb := Real.sin_bound ht
    have h5 : |t| ^ 5 ≤ |t| ^ 3 := pow_le_pow_of_le_one (abs_nonneg t) ht (by norm_num)
    have ht3 : |-(t ^ 3 / 6)| = |t| ^ 3 / 6 := by rw [abs_neg, abs_div, abs_pow]; norm_num
    calc |Real.sin t - t| = |(Real.sin t - (t - t ^ 3 / 6)) + (-(t ^ 3 / 6))| := by
          congr 1; ring
      _ ≤ |Real.sin t - (t - t ^ 3 / 6)| + |-(t ^ 3 / 6)| := abs_add_le _ _
      _ ≤ |t| ^ 5 / 100 + |t| ^ 3 / 6 := by rw [ht3]; linarith
      _ ≤ 2 * |t| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg t) 3]
  · have hs := Real.abs_sin_le_one t
    have h3 : |t| ≤ |t| ^ 3 := le_self_pow₀ ht.le (by norm_num)
    have htri : |Real.sin t - t| ≤ |Real.sin t| + |t| := by
      have := abs_add_le (Real.sin t) (-t)
      rwa [abs_neg, ← sub_eq_add_neg] at this
    linarith

/-- For every real `t`, `|Real.sin t - t| ≤ 2 * |t|`. It follows from `|Real.sin t| ≤ |t|` and the
triangle inequality. -/
theorem abs_sin_sub_self_le_two_mul (t : ℝ) : |Real.sin t - t| ≤ 2 * |t| := by
  have hs : |Real.sin t| ≤ |t| := by
    simpa using Real.abs_sin_sub_sin_le t 0
  have htri : |Real.sin t - t| ≤ |Real.sin t| + |t| := by
    have := abs_add_le (Real.sin t) (-t)
    rwa [abs_neg, ← sub_eq_add_neg] at this
  linarith

/-- For reals `a`, `b`: `(𝐞 a : ℂ) * (𝐞 b : ℂ) = (𝐞 (a + b) : ℂ)`, where `𝐞` is `Real.fourierChar`
and its values on the circle are read as complex numbers. -/
theorem coe_fourierChar_mul_coe_fourierChar (a b : ℝ) : (𝐞 a : ℂ) * (𝐞 b : ℂ) = 𝐞 (a + b) := by
  rw [AddChar.map_add_eq_mul, Circle.coe_mul]

/-- For `k : ℤ` and `θ : ℝ`, the complex conjugate of `Complex.exp (-(k * θ * I))` is
`Complex.exp (k * θ * I)`, with `k` and `θ` coerced to `ℂ`. -/
theorem conj_exp_neg_int_mul_mul_I (k : ℤ) (θ : ℝ) :
    starRingEnd ℂ (Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I))) =
      Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal, Complex.conj_I]

/-- For real `U`, `V`, `θ` and an integer `a`,
`Complex.exp (((U + (a : ℝ) * θ + V : ℝ) : ℂ) * Complex.I) = Complex.exp (((U + V : ℝ) : ℂ) *
Complex.I) * Complex.exp ((θ : ℂ) * Complex.I) ^ a`. -/
theorem exp_add_int_mul_add_mul_I (U V θ : ℝ) (a : ℤ) :
    Complex.exp (((U + (a : ℝ) * θ + V : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((U + V : ℝ) : ℂ) * Complex.I) * Complex.exp ((θ : ℂ) * Complex.I) ^ a := by
  rw [← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- For a nonzero complex `z` and real `φ`,
`Complex.exp ((Complex.arg (Complex.exp ((φ : ℂ) * Complex.I) * z) : ℂ) * Complex.I) = Complex.exp
((φ : ℂ) * Complex.I) * Complex.exp ((Complex.arg z : ℂ) *
Complex.I)`. The proof multiplies both sides by `‖z‖` and uses `‖w‖ * exp (arg w * I) = w`. -/
theorem exp_arg_exp_mul_mul_I (z : ℂ) (hz : z ≠ 0) (φ : ℝ) :
    Complex.exp ((Complex.arg (Complex.exp ((φ : ℂ) * Complex.I) * z) : ℂ) * Complex.I) =
      Complex.exp ((φ : ℂ) * Complex.I) * Complex.exp ((Complex.arg z : ℂ) * Complex.I) := by
  have h1 := Complex.norm_mul_exp_arg_mul_I (Complex.exp ((φ : ℂ) * Complex.I) * z)
  have h2 := Complex.norm_mul_exp_arg_mul_I z
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul] at h1
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
  apply mul_left_cancel₀ hn
  rw [h1]
  nth_rewrite 1 [← h2]
  ring

/-- If a real `θ` equals `n * (2 * π)` for an integer `n`, then
`Complex.exp ((θ : ℂ) * Complex.I) = 1`. -/
theorem exp_mul_I_eq_one_of_period (θ : ℝ) (n : ℤ) (h : θ = n * (2 * Real.pi)) :
    Complex.exp (((θ : ℝ) : ℂ) * Complex.I) = 1 := by
  rw [h]
  push_cast
  convert Complex.exp_int_mul_two_pi_mul_I n using 2
  ring

/-- For an integer `M` and a nonzero complex number `w`,
`Complex.exp (((M : ℝ) * Complex.arg w : ℝ) * I) = (w / ‖w‖) ^ M`, with `‖w‖` coerced to `ℂ`. The
proof uses `Complex.exp (Complex.arg w * I) = w / ‖w‖` and the rule for the exponential of an
integer multiple. -/
theorem exp_mul_arg_eq_div_norm_zpow (M : ℤ) (w : ℂ) (hw : w ≠ 0) :
    Complex.exp ((((M : ℝ) * Complex.arg w : ℝ) : ℂ) * Complex.I) = (w / (‖w‖ : ℂ)) ^ M := by
  have h1 : (((M : ℝ) * Complex.arg w : ℝ) : ℂ) * Complex.I = (M : ℂ) *
      ((Complex.arg w : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h1, Complex.exp_int_mul]
  have hn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hw)
  have h2 : Complex.exp ((Complex.arg w : ℂ) * Complex.I) = w / (‖w‖ : ℂ) := by
    rw [eq_div_iff hn, mul_comm]
    exact Complex.norm_mul_exp_arg_mul_I w
  rw [h2]

/-- For an integer `M` and a nonzero complex number `w`,
`Complex.exp (((M : ℝ) * Complex.arg w : ℝ) * I) = ((‖w‖ : ℂ)⁻¹ * w) ^ M`. -/
theorem exp_mul_arg_eq_inv_mul_zpow (M : ℤ) {w : ℂ} (hw : w ≠ 0) :
    Complex.exp ((((M : ℝ) * Complex.arg w : ℝ) : ℂ) * Complex.I) = ((‖w‖ : ℂ)⁻¹ * w) ^ M := by
  have hn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hw
  have h1 : Complex.exp ((Complex.arg w : ℂ) * Complex.I) = (‖w‖ : ℂ)⁻¹ * w := by
    rw [eq_inv_mul_iff_mul_eq₀ hn, Complex.norm_mul_exp_arg_mul_I]
  rw [← h1, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

/-- For integers `m`, `n`, a real `σ` and complex `c`, `d`,
`exp (2 * π * m * σ * I) * c * conj (exp (2 * π * n * σ * I) * d) = c * conj d * exp (2 * π * (m - n
: ℤ) * σ * I)`, where `exp` is `Complex.exp`. The conjugate of `exp (2 * π * n * σ * I)` is `exp
(-(2 * π * n * σ * I))`, and the two exponentials combine by the addition formula. -/
theorem exp_mul_mul_conj_exp_mul_eq (m n : ℤ) (σ : ℝ) (c d : ℂ) :
    Complex.exp (2 * (Real.pi : ℂ) * (m : ℂ) * (σ : ℂ) * Complex.I) * c *
        (starRingEnd ℂ) (Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (σ : ℂ) * Complex.I) * d) =
      c * (starRingEnd ℂ) d *
        Complex.exp (2 * (Real.pi : ℂ) * (((m - n : ℤ)) : ℂ) * (σ : ℂ) * Complex.I) := by
  rw [map_mul, ← Complex.exp_conj]
  have hconj : (starRingEnd ℂ) (2 * (Real.pi : ℂ) * (n : ℂ) * (σ : ℂ) * Complex.I) =
      -(2 * (Real.pi : ℂ) * (n : ℂ) * (σ : ℂ) * Complex.I) := by
    simp [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  rw [hconj]
  have hsplit : Complex.exp (2 * (Real.pi : ℂ) * (((m - n : ℤ)) : ℂ) * (σ : ℂ) * Complex.I) =
      Complex.exp (2 * (Real.pi : ℂ) * (m : ℂ) * (σ : ℂ) * Complex.I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (σ : ℂ) * Complex.I)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hsplit]
  ring

/-- For an integer `k ≠ 0` and a natural number `N > 0` with `|k| < N`,
`Complex.exp (2 * π * I * k / N) ≠ 1`. If it were `1`, then `k = n * N` for some integer `n ≠ 0`,
which gives `N ≤ |k|`. -/
theorem exp_ne_one_of_lt {k : ℤ} {N : ℕ} (hN : 0 < N) (hk : k ≠ 0) (hkN : |k| < N) :
    Complex.exp (2 * Real.pi * Complex.I * k / N) ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have e1 : (k : ℂ) = n * N := by
    field_simp at hn
    linear_combination hn
  have e2 : k = n * N := by exact_mod_cast e1
  have hn0 : n ≠ 0 := by rintro rfl; simp only [zero_mul] at e2; exact hk e2
  have : (N : ℤ) ≤ |k| := by
    rw [e2, abs_mul]
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
    have hN0 : (0 : ℤ) ≤ |(N : ℤ)| := abs_nonneg _
    rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ N)]
    nlinarith
  linarith

/-- For real `n`, `τ` and an integer `k`,
`Complex.exp (-(((2 * π * n * τ + k * (2 * π) : ℝ) : ℂ) * I)) = Complex.exp (-(((2 * π * n * τ + k *
0 : ℝ) : ℂ) * I))`: the integer multiple `k * (2 * π)` of the period in the angle can be dropped. -/
theorem exp_neg_add_int_mul_two_pi (n : ℝ) (k : ℤ) (τ : ℝ) :
    Complex.exp (-(((2 * Real.pi * n * τ + k * (2 * Real.pi) : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (-(((2 * Real.pi * n * τ + k * 0 : ℝ) : ℂ) * Complex.I)) := by
  have : (-(((2 * Real.pi * n * τ + k * (2 * Real.pi) : ℝ) : ℂ) * Complex.I)) =
      (-(((2 * Real.pi * n * τ + k * 0 : ℝ) : ℂ) * Complex.I)) + ((-k : ℤ) : ℂ) *
          (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Write `θ κ = 2 * π * κ.1 * τ + κ.2 * φ` for `κ : ℤ × ℤ` and real `τ`, `φ`. Then
`Complex.exp ((θ (-α) : ℂ) * I) = conj (Complex.exp ((θ α : ℂ) * I))`. -/
theorem exp_neg_index_eq_conj_exp (α : ℤ × ℤ) (τ φ : ℝ) :
    Complex.exp (((2 * Real.pi * (-α).1 * τ + (-α).2 * φ : ℝ) : ℂ) * Complex.I)
      = (starRingEnd ℂ) (Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I)) :=
          by
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
  push_cast
  ring

/-- For an integer `k` and real `θ`,
`Complex.exp (-(((k : ℝ) * (θ + 2 * π) : ℝ) : ℂ) * Complex.I) = Complex.exp (-(((k : ℝ) * θ : ℝ) :
ℂ) * Complex.I)`: the function `θ ↦ exp (-(k * θ) * I)` has period `2 * π`. -/
theorem exp_neg_int_mul_add_two_pi (k : ℤ) (θ : ℝ) :
    Complex.exp (-(((k : ℝ) * (θ + 2 * Real.pi) : ℝ) : ℂ) * Complex.I)
      = Complex.exp (-(((k : ℝ) * θ : ℝ) : ℂ) * Complex.I) := by
  have e : -(((k : ℝ) * (θ + 2 * Real.pi) : ℝ) : ℂ) * Complex.I
      = -(((k : ℝ) * θ : ℝ) : ℂ) * Complex.I + ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- For real `x`, `Complex.exp (-((x : ℂ) * Complex.I)) = (Real.cos x : ℂ) - Complex.I * (Real.sin x
: ℂ)`. -/
theorem exp_neg_mul_I (x : ℝ) :
    Complex.exp (-((x : ℂ) * Complex.I)) = (Real.cos x : ℂ) - Complex.I * (Real.sin x : ℂ) := by
  rw [← neg_mul, ← Complex.ofReal_neg, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

/-- For `k : ℤ` and `θ : ℝ`, `Complex.exp (-(k * θ * I)) * Complex.exp (k * θ * I) = 1`, with `k`
and `θ` coerced to `ℂ`. -/
theorem exp_neg_mul_exp (k : ℤ) (θ : ℝ) :
    Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)) * Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I) =
        1 := by
  rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

/-- Write `θ κ = 2 * π * κ.1 * τ + κ.2 * φ` for `κ : ℤ × ℤ` and real `τ`, `φ`. Then
`Complex.exp (-((θ ι : ℂ) * I)) * Complex.exp ((θ α : ℂ) * I) = Complex.exp (-((θ (ι - α) : ℂ) *
I))`. -/
theorem exp_neg_mul_exp_index_sub (ι α : ℤ × ℤ) (τ φ : ℝ) :
    Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I))
      * Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I)
      = Complex.exp (-(((2 * Real.pi * (ι - α).1 * τ + (ι - α).2 * φ : ℝ) : ℂ) * Complex.I)) := by
  rw [← Complex.exp_add]
  congr 1
  simp only [Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
  push_cast
  ring

/-- Write `θ κ = 2 * π * κ.1 * τ + κ.2 * φ` for `κ : ℤ × ℤ` and real `τ`, `φ`. Then
`Complex.exp (-((θ ι : ℂ) * I)) * Complex.exp (-((θ α : ℂ) * I)) = Complex.exp (-((θ (ι + α) : ℂ) *
I))`. -/
theorem exp_neg_mul_exp_neg_index_add (ι α : ℤ × ℤ) (τ φ : ℝ) :
    Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I))
      * Complex.exp (-(((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I))
      = Complex.exp (-(((2 * Real.pi * (ι + α).1 * τ + (ι + α).2 * φ : ℝ) : ℂ) * Complex.I)) := by
  rw [← Complex.exp_add]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]
  push_cast
  ring

/-- For integer pairs `ξ`, `ν`, a complex `w` and real `τ`, `φ`, write
`e ι = Complex.exp ((2 * π * ι.1 * τ + ι.2 * φ) * Complex.I)`, the real phase being cast to `ℂ`.
Then `Complex.exp (-((2 * π * ξ.1 * τ + ξ.2 * φ) * Complex.I)) * ((e ν * w).re : ℂ) =
(w / 2) * e (ν - ξ) + (conj w / 2) * e (-ν -
ξ)`. The proof writes the real part as half the sum of the number and its conjugate and combines the
exponentials. -/
theorem exp_neg_mul_ofReal_re_exp_mul (ξ ν : ℤ × ℤ) (w : ℂ) (τ φ : ℝ) :
    Complex.exp (-(((2 * Real.pi * (ξ.1 : ℝ) * τ + (ξ.2 : ℝ) * φ : ℝ) : ℂ) * Complex.I)) *
        (((Complex.exp (((2 * Real.pi * (ν.1 : ℝ) * τ + (ν.2 : ℝ) * φ : ℝ) : ℂ) * Complex.I) * w).re
          : ℝ) : ℂ) =
      (w / 2) * Complex.exp (((2 * Real.pi * ((ν.1 - ξ.1 : ℤ) : ℝ) * τ +
          ((ν.2 - ξ.2 : ℤ) : ℝ) * φ : ℝ) : ℂ) * Complex.I) +
        (starRingEnd ℂ w / 2) * Complex.exp (((2 * Real.pi * ((-ν.1 - ξ.1 : ℤ) : ℝ) * τ +
          ((-ν.2 - ξ.2 : ℤ) : ℝ) * φ : ℝ) : ℂ) * Complex.I) := by
  set θ : ℝ := 2 * Real.pi * (ν.1 : ℝ) * τ + (ν.2 : ℝ) * φ with hθ
  set θ₀ : ℝ := 2 * Real.pi * (ξ.1 : ℝ) * τ + (ξ.2 : ℝ) * φ with hθ₀
  have h1 : Complex.exp (((2 * Real.pi * ((ν.1 - ξ.1 : ℤ) : ℝ) * τ +
      ((ν.2 - ξ.2 : ℤ) : ℝ) * φ : ℝ) : ℂ) * Complex.I) =
        Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp (-((θ₀ : ℂ) * Complex.I)) := by
    rw [← Complex.exp_add, hθ, hθ₀]
    congr 1
    push_cast
    ring
  have h2 : Complex.exp (((2 * Real.pi * ((-ν.1 - ξ.1 : ℤ) : ℝ) * τ +
      ((-ν.2 - ξ.2 : ℤ) : ℝ) * φ : ℝ) : ℂ) * Complex.I) =
        Complex.exp (-((θ : ℂ) * Complex.I)) * Complex.exp (-((θ₀ : ℂ) * Complex.I)) := by
    rw [← Complex.exp_add, hθ, hθ₀]
    congr 1
    push_cast
    ring
  have h3 : starRingEnd ℂ (Complex.exp ((θ : ℂ) * Complex.I)) =
      Complex.exp (-((θ : ℂ) * Complex.I)) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring_nf
  rw [Complex.re_eq_add_conj, map_mul, h3, h1, h2]
  ring

/-- For an integer pair `ι` and real `τ`, `ψ`,
`Complex.exp (-((2 * π * ι.1 * (τ + 1) + ι.2 * ψ) * Complex.I)) = Complex.exp (-((2 * π * ι.1 * τ +
ι.2 * ψ) * Complex.I))`, where each real phase is cast to `ℂ`: the exponential has period `1` in
`τ`. -/
theorem exp_neg_pair_phase_add_one (ι : ℤ × ℤ) (τ ψ : ℝ) :
    Complex.exp (-(((2 * Real.pi * ι.1 * (τ + 1) + ι.2 * ψ : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * ψ : ℝ) : ℂ) * Complex.I)) := by
  have h : -(((2 * Real.pi * ι.1 * (τ + 1) + ι.2 * ψ : ℝ) : ℂ) * Complex.I) =
      -(((2 * Real.pi * ι.1 * τ + ι.2 * ψ : ℝ) : ℂ) * Complex.I)
        + ((-ι.1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- For an integer pair `ι` and real `τ`, `ψ`,
`Complex.exp (-((2 * π * ι.1 * τ + ι.2 * (ψ + 2 * π)) * Complex.I)) = Complex.exp (-((2 * π * ι.1 *
τ + ι.2 * ψ) * Complex.I))`, where each real phase is cast to `ℂ`: the exponential has period `2 *
π` in `ψ`. -/
theorem exp_neg_pair_phase_add_two_pi (ι : ℤ × ℤ) (τ ψ : ℝ) :
    Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * (ψ + 2 * Real.pi) : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * ψ : ℝ) : ℂ) * Complex.I)) := by
  have h : -(((2 * Real.pi * ι.1 * τ + ι.2 * (ψ + 2 * Real.pi) : ℝ) : ℂ) * Complex.I) =
      -(((2 * Real.pi * ι.1 * τ + ι.2 * ψ : ℝ) : ℂ) * Complex.I)
        + ((-ι.2 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- For an integer pair `ι` and real `τ`, `ψ`, `s`, `φ`,
`Complex.exp (-((2 * π * ι.1 * τ + ι.2 * ψ) * Complex.I)) = Complex.exp
((2 * π * ι.1 * s + ι.2 * φ) * Complex.I) * Complex.exp (-((2 * π * ι.1 * (τ + s) + ι.2 * (ψ + φ)) *
Complex.I))`, where each real phase is cast to `ℂ`. -/
theorem exp_neg_pair_phase_shift (ι : ℤ × ℤ) (τ ψ s φ : ℝ) :
    Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * ψ : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (((2 * Real.pi * ι.1 * s + ι.2 * φ : ℝ) : ℂ) * Complex.I) *
        Complex.exp (-(((2 * Real.pi * ι.1 * (τ + s) + ι.2 * (ψ + φ) : ℝ) : ℂ) * Complex.I)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- For an integer `n` and a real `c`,
`Complex.exp (-(((2 * π * n * 1 + c : ℝ) : ℂ) * I)) = Complex.exp (-(((2 * π * n * 0 + c : ℝ) : ℂ) *
I))`: the term `2 * π * n` in the angle can be dropped. -/
theorem exp_neg_two_pi_mul_int_add (n : ℤ) (c : ℝ) :
    Complex.exp (-(((2 * Real.pi * n * 1 + c : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (-(((2 * Real.pi * n * 0 + c : ℝ) : ℂ) * Complex.I)) := by
  have : (-(((2 * Real.pi * n * 1 + c : ℝ) : ℂ) * Complex.I)) =
      (-(((2 * Real.pi * n * 0 + c : ℝ) : ℂ) * Complex.I)) + ((-n : ℤ) : ℂ) *
          (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- For real `x` and `y`,
`Complex.exp (((x + y : ℝ) : ℂ) * Complex.I) = Complex.exp ((x : ℂ) * Complex.I) * Complex.exp ((y :
ℂ) * Complex.I)`. -/
theorem exp_ofReal_add_mul_I (x y : ℝ) :
    Complex.exp (((x + y : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((x : ℂ) * Complex.I) * Complex.exp ((y : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- For real `c`, `L` and an integer `n` with `c * L = 2 * π * n`, the integral
`∫ x in 0..L, exp (-(c * x * I))` is `L` if `c = 0` and `0` otherwise. For `c ≠ 0` the proof
integrates the exponential explicitly and uses `exp (-n * (2 * π * I)) = 1`. -/
theorem integral_exp_neg_mul_I_full_periods (c L : ℝ) (n : ℤ) (hL : c * L = 2 * Real.pi * n) :
    ∫ x in (0 : ℝ)..L, Complex.exp (-(((c * x : ℝ) : ℂ) * Complex.I)) = if c = 0 then (L : ℂ) else
        0 := by
  split_ifs with hc
  · subst hc
    simp
  · have hc' : (-(c : ℂ) * Complex.I) ≠ 0 := by simp [hc, Complex.I_ne_zero]
    have e : ∀ x : ℝ, Complex.exp (-(((c * x : ℝ) : ℂ) * Complex.I))
        = Complex.exp ((-(c : ℂ) * Complex.I) * x) := by
      intro x
      congr 1
      push_cast
      ring
    simp_rw [e]
    rw [integral_exp_mul_complex hc']
    have h1 : (-(c : ℂ) * Complex.I) * (L : ℂ) = ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      have : (c : ℂ) * L = 2 * Real.pi * n := by exact_mod_cast hL
      push_cast
      linear_combination (-Complex.I) * this
    rw [h1, Complex.exp_int_mul_two_pi_mul_I]
    simp

/-- For an integer `n`, the integral `∫ σ in 0..1, exp (2 * π * n * σ * I)` is `1` if `n = 0` and
`0` otherwise. For `n ≠ 0` the proof integrates the exponential explicitly and uses
`exp (n * (2 * π * I)) = 1`. -/
theorem integral_exp_two_pi_int_mul_I (n : ℤ) :
    ∫ σ in (0 : ℝ)..1, Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (σ : ℂ) * Complex.I) =
      if n = 0 then 1 else 0 := by
  split_ifs with hn
  · subst hn
    simp
  · have hc : (2 * (Real.pi : ℂ) * (n : ℂ) * Complex.I) ≠ 0 := by
      have h1 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
      have h2 : (n : ℂ) ≠ 0 := Int.cast_ne_zero.2 hn
      simp [h1, h2, Complex.I_ne_zero]
    have hrw : ∀ σ : ℝ, Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (σ : ℂ) * Complex.I) =
        Complex.exp ((2 * (Real.pi : ℂ) * (n : ℂ) * Complex.I) * (σ : ℂ)) := by
      intro σ
      ring_nf
    simp_rw [hrw]
    rw [integral_exp_mul_complex hc]
    have he : Complex.exp ((2 * (Real.pi : ℂ) * (n : ℂ) * Complex.I) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I n]
      congr 1
      push_cast
      ring
    rw [he]
    simp

/-- For real `θ`, `‖Complex.exp (θ * Complex.I) - 1 - θ * Complex.I‖ ≤ θ ^ 2`. The proof applies the
mean value inequality to `s ↦ Complex.exp (s * Complex.I) - 1 - s * Complex.I` on the closed ball of
radius `|θ|` around `0`, where the derivative `Complex.I * (Complex.exp (s * Complex.I) - 1)` has
norm at most `|θ|`. -/
theorem norm_cexp_sub_one_sub_le_sq (θ : ℝ) :
    ‖Complex.exp (θ * Complex.I) - 1 - θ * Complex.I‖ ≤ θ ^ 2 := by
  have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ ↦ Complex.exp (s * Complex.I) - 1 - s * Complex.I)
      (Complex.I * (Complex.exp (s * Complex.I) - 1)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ ↦ (s : ℂ) * Complex.I) Complex.I s := by
      simpa using (hasDerivAt_id s).ofReal_comp.mul_const Complex.I
    have h2 := (h1.cexp.sub_const 1).sub h1
    rw [show Complex.I * (Complex.exp (s * Complex.I) - 1) =
      Complex.exp (s * Complex.I) * Complex.I - Complex.I by ring]
    exact h2
  have hb : ∀ s ∈ Metric.closedBall (0 : ℝ) |θ|,
      ‖Complex.I * (Complex.exp (s * Complex.I) - 1)‖ ≤ |θ| := by
    intro s hs
    rw [norm_mul, Complex.norm_I, one_mul]
    have hs' : ‖s‖ ≤ |θ| := by simpa using hs
    refine le_trans ?_ hs'
    have := norm_exp_I_mul_ofReal_sub_one_le (x := s)
    rwa [mul_comm] at this
  have hθ : θ ∈ Metric.closedBall (0 : ℝ) |θ| := by simp
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s : ℝ ↦ Complex.exp (s * Complex.I) - 1 - s * Complex.I)
    (fun s _ ↦ (hd s).hasDerivWithinAt) hb (convex_closedBall (0 : ℝ) |θ|)
    (Metric.mem_closedBall_self (abs_nonneg θ)) hθ
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, sub_self, sub_zero] at this
  rw [Real.norm_eq_abs, ← pow_two, sq_abs] at this
  exact this

/-- For every real `x`, the complex number `exp (-x * I)` has norm one. -/
theorem norm_exp_neg_ofReal_mul_I (x : ℝ) : ‖Complex.exp (-(x : ℂ) * Complex.I)‖ = 1 := by
  rw [show -(x : ℂ) * Complex.I = ((-x : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I]

/-- For an integer `k` and real `θ`, `‖Complex.exp (-(((k : ℝ) * θ : ℝ) : ℂ) * Complex.I)‖ = 1`. -/
theorem norm_exp_neg_int_mul_mul_I (k : ℤ) (θ : ℝ) :
    ‖Complex.exp (-(((k : ℝ) * θ : ℝ) : ℂ) * Complex.I)‖ = 1 := norm_exp_neg_ofReal_mul_I _

/-- The character `Real.fourierChar`, that is `x ↦ exp (2 * π * x * I)`, is Lipschitz with constant
`2 * π`: `‖(Real.fourierChar a : ℂ) - Real.fourierChar b‖ ≤ 2 * π * |a - b|` for all real `a b`. The
proof factors out `Real.fourierChar b`, which has norm `1`, and uses `‖exp (I * t) - 1‖ ≤ ‖t‖` for
real `t`. -/
theorem norm_fourierChar_sub_le (a b : ℝ) :
    ‖(Real.fourierChar a : ℂ) - Real.fourierChar b‖ ≤ 2 * π * |a - b| := by
  rw [Real.fourierChar_apply, Real.fourierChar_apply]
  have h1 : Complex.exp (↑(2 * π * a) * Complex.I) - Complex.exp (↑(2 * π * b) * Complex.I) =
      Complex.exp (↑(2 * π * b) * Complex.I) * (Complex.exp (Complex.I * ↑(2 * π * (a - b))) -
          1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    push_cast; ring
  rw [h1, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  refine norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]

/-- For real `x`, `((Real.cos x : ℝ) : ℂ) = (Complex.exp ((x : ℂ) * Complex.I) + Complex.exp (-((x :
ℂ) * Complex.I))) / 2`. -/
theorem ofReal_cos_eq_exp_add_exp_neg (x : ℝ) :
    ((Real.cos x : ℝ) : ℂ) = (Complex.exp ((x : ℂ) * Complex.I) +
        Complex.exp (-((x : ℂ) * Complex.I))) / 2 := by
  rw [Complex.ofReal_cos, Complex.cos, neg_mul]

/-- For real `x`, `((Real.sin x : ℝ) : ℂ) = (Complex.exp (-((x : ℂ) * Complex.I)) - Complex.exp ((x
: ℂ) * Complex.I)) * Complex.I / 2`. -/
theorem ofReal_sin_eq_exp_neg_sub_exp (x : ℝ) :
    ((Real.sin x : ℝ) : ℂ) =
      (Complex.exp (-((x : ℂ) * Complex.I)) - Complex.exp ((x : ℂ) * Complex.I)) * Complex.I / 2 :=
          by
  rw [Complex.ofReal_sin, Complex.sin, neg_mul]

/-- For a real `θ` and a complex `z`, the real part of `Complex.exp (θ * I) * z`, coerced to `ℂ`,
equals `(Complex.exp (θ * I) * z + Complex.exp (-(θ * I)) * conj z) / 2`. -/
theorem re_exp_mul_eq (θ : ℝ) (z : ℂ) :
    (((Complex.exp ((θ : ℂ) * Complex.I) * z).re : ℝ) : ℂ)
      = (Complex.exp ((θ : ℂ) * Complex.I) * z + Complex.exp (-((θ : ℂ) * Complex.I)) *
          (starRingEnd ℂ) z) / 2 := by
  rw [Complex.re_eq_add_conj, map_mul, ← Complex.exp_conj]
  congr 3
  simp [Complex.conj_ofReal]

/-- For real `a`, `b` and complex `A`, `B`,
`Complex.exp ((a : ℂ) * Complex.I) * A * conj (Complex.exp ((b : ℂ) * Complex.I) * B) = A * conj B *
Complex.exp (((a - b : ℝ) : ℂ) * Complex.I)`. -/
theorem exp_mul_mul_conj_exp_mul (a b : ℝ) (A B : ℂ) :
    Complex.exp ((a : ℂ) * Complex.I) * A * starRingEnd ℂ (Complex.exp ((b : ℂ) * Complex.I) * B) =
      A * starRingEnd ℂ B * Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) := by
  rw [map_mul, ← Complex.exp_conj, sub_eq_add_neg, exp_ofReal_add_mul_I]
  have hc : starRingEnd ℂ ((b : ℂ) * Complex.I) = ((-b : ℝ) : ℂ) * Complex.I := by simp
  rw [hc]
  ring

/-- For real `a`, `b` and complex `A`, `B`,
`Complex.exp ((a : ℂ) * Complex.I) * A * (Complex.exp ((b : ℂ) * Complex.I) * B) = A * B *
Complex.exp (((a + b : ℝ) : ℂ) * Complex.I)`. -/
theorem exp_mul_mul_exp_mul (a b : ℝ) (A B : ℂ) :
    Complex.exp ((a : ℂ) * Complex.I) * A * (Complex.exp ((b : ℂ) * Complex.I) * B) =
      A * B * Complex.exp (((a + b : ℝ) : ℂ) * Complex.I) := by
  rw [exp_ofReal_add_mul_I]
  ring

/-- For an integer `k` and a natural number `N > 0` with `|k| < N`, the sum
`∑ a ∈ Finset.range N, Complex.exp (2 * π * I * k * a / N)` equals `N` if `k = 0` and `0` otherwise.
For `k ≠ 0` the terms are the powers of `ζ = Complex.exp (2 * π * I * k / N)`, and the geometric sum
vanishes because `ζ ≠ 1` and `ζ ^ N = 1`. -/
theorem sum_range_exp_two_pi_eq_ite (k : ℤ) (N : ℕ) (hN : 0 < N) (hkN : |k| < N) :
    ∑ a ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * k * a / N) = if k = 0 then
        (N : ℂ) else 0 := by
  split_ifs with hk
  · subst hk
    simp
  · have hζ := exp_ne_one_of_lt hN hk hkN
    have e : ∀ a : ℕ, Complex.exp (2 * Real.pi * Complex.I * k * a / N)
        = Complex.exp (2 * Real.pi * Complex.I * k / N) ^ a := by
      intro a
      rw [← Complex.exp_nat_mul]
      congr 1
      ring
    simp only [e]
    rw [geom_sum_eq hζ, ← Complex.exp_nat_mul]
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have : (N : ℂ) * (2 * Real.pi * Complex.I * k / N) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
      field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I, sub_self, zero_div]

/-- For `k : ℤ` and `θ : ℝ`, the complex number `Complex.exp (k * θ * I)`, with `k` and `θ` coerced
to `ℂ`, has norm `1`. -/
theorem norm_exp_int_mul_mul_I (k : ℤ) (θ : ℝ) :
    ‖Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I)‖ = 1 := by
  have e : (k : ℂ) * (θ : ℂ) = ((k * θ : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.norm_exp_ofReal_mul_I]

/-- For every real `x` and integer `n`, `exp ((x - n * (2 * π)) * I) = exp (x * I)`: the function
`x ↦ exp (x * I)` has period `2 * π`. -/
theorem exp_ofReal_sub_int_mul_two_pi_mul_I (x : ℝ) (n : ℤ) :
    Complex.exp (((x - n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) =
        Complex.exp ((x : ℂ) * Complex.I) := by
  rw [show (((x - n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = (x : ℂ) * Complex.I - n *
      (2 * Real.pi * Complex.I) by
    push_cast; ring, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]

/-- For a nonzero complex `w` and an integer `k`, `exp (I * (k * arg w)) = (w / ‖w‖) ^ k`. From the
polar form `w = ‖w‖ * exp (arg w * I)`. -/
theorem exp_I_mul_int_mul_arg (w : ℂ) (hw : w ≠ 0) (k : ℤ) :
    Complex.exp (Complex.I * ((k : ℝ) * Complex.arg w : ℝ)) = (w / (‖w‖ : ℂ)) ^ k := by
  have hn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hw
  have h1 : w / (‖w‖ : ℂ) = Complex.exp (Complex.arg w * Complex.I) := by
    rw [div_eq_iff hn, mul_comm]
    exact (Complex.norm_mul_exp_arg_mul_I w).symm
  rw [h1, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

/-- For every complex `w`, `exp (I * (1 * arg w)) * ‖w‖ = w`, where the factor `1` is the integer
one seen in `ℝ`. This is the polar form of `w`. -/
theorem exp_I_mul_one_mul_arg_mul_norm (w : ℂ) :
    Complex.exp (Complex.I * ((((1 : ℤ) : ℝ) * Complex.arg w : ℝ) : ℂ)) * (‖w‖ : ℂ) = w := by
  have e : Complex.I * ((((1 : ℤ) : ℝ) * Complex.arg w : ℝ) : ℂ) = (Complex.arg w : ℂ) *
      Complex.I := by
    push_cast
    ring
  rw [e, mul_comm]
  exact Complex.norm_mul_exp_arg_mul_I w

/-- For real `x` and `y`, `exp (I * (x + y)) = exp (I * x) * exp (I * y)` in `ℂ`. This is
`exp_ofReal_add_mul_I` with `I` as the first factor. -/
theorem exp_I_mul_ofReal_add (x y : ℝ) :
    Complex.exp (Complex.I * ((x + y : ℝ) : ℂ)) = Complex.exp (Complex.I * (x : ℂ)) *
        Complex.exp (Complex.I * (y : ℂ)) := by
  simpa only [mul_comm Complex.I] using exp_ofReal_add_mul_I x y

/-- For every complex `w`, `exp (I * (-1 * arg w)) * ‖w‖ = conj w`, where the factor `-1` is the
integer minus one seen in `ℝ`. This is the conjugate of the polar form of `w`. -/
theorem exp_I_mul_neg_one_mul_arg_mul_norm (w : ℂ) :
    Complex.exp (Complex.I * ((((-1 : ℤ) : ℝ) * Complex.arg w : ℝ) : ℂ)) * (‖w‖ : ℂ) =
        (starRingEnd ℂ) w := by
  have e : Complex.I * ((((-1 : ℤ) : ℝ) * Complex.arg w : ℝ) : ℂ) =
      (starRingEnd ℂ) ((Complex.arg w : ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [e, Complex.exp_conj, ← Complex.conj_ofReal ‖w‖, ← map_mul, mul_comm,
      Complex.norm_mul_exp_arg_mul_I]

/-- For every real `x`, the complex number `exp (-(x * I))` has norm one. This is
`norm_exp_neg_ofReal_mul_I`, where the exponent is written `-x * I`. -/
theorem norm_exp_neg_mul_I (x : ℝ) : ‖Complex.exp (-((x : ℂ) * Complex.I))‖ = 1 := by
  rw [← neg_mul]
  exact norm_exp_neg_ofReal_mul_I x

/-- For real `a` and `b`, `‖exp (a * I) - exp (b * I)‖ ≤ |a - b|`. The difference is
`exp (b * I) * (exp (I * (a - b)) - 1)`, and `‖exp (I * x) - 1‖ ≤ |x|` for real `x`. -/
theorem norm_exp_mul_I_sub_le (a b : ℝ) :
    ‖Complex.exp (↑a * Complex.I) - Complex.exp (↑b * Complex.I)‖ ≤ |a - b| := by
  have h : Complex.exp (↑a * Complex.I) - Complex.exp (↑b * Complex.I) =
      Complex.exp (↑b * Complex.I) * (Complex.exp (Complex.I * ↑(a - b)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, ← Real.norm_eq_abs]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

end PDE.Analysis
