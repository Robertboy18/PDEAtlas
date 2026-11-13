/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Spherical Bessel functions of the first kind

The spherical Bessel function of order `l` is the entire function
`j_l x = x ^ l * ∑' k, (-(x ^ 2) / 2) ^ k / (k! (2l + 2k + 1)‼)`.
The series without the factor `x ^ l` is `reducedSphericalBesselJ l`, an even entire function
with value `1 / (2l + 1)‼` at the origin; as a power series in `x ^ 2` it has infinite radius,
so `j_l` is analytic. Term by term differentiation gives `g_l' = -x g_{l+1}`, and comparing
coefficients gives the three-term relation `g_l = (2l + 3) g_{l+1} - x ^ 2 g_{l+2}`. These two
identities give the classical recurrences for `j_l` and the spherical Bessel equation
`x ^ 2 j'' + 2 x j' + (x ^ 2 - l (l + 1)) j = 0`.

## Main definitions

* `sphericalBesselTerm l k x`: the `k`-th term of the reduced series.
* `reducedSphericalBesselJ l x`: the reduced series `g_l x`, so that `j_l x = x ^ l * g_l x`.
* `reducedSphericalBesselJSq l t`: the entire function `G_l` with `g_l x = G_l (x ^ 2)`.
* `sphericalBesselJ l x`: the spherical Bessel function `j_l x`.

## Main results

* `hasDerivAt_reducedSphericalBesselJ`: `g_l' x = -x g_{l+1} x`.
* `reducedSphericalBesselJ_eq_sub`: `g_l = (2l + 3) g_{l+1} - x ^ 2 g_{l+2}`.
* `analyticOnNhd_sphericalBesselJ`, `contDiff_sphericalBesselJ`: `j_l` is analytic on `ℝ`, in
  particular smooth; its series in `x ^ 2` has infinite radius.
* `mul_sphericalBesselJ_add_sphericalBesselJ`, `sphericalBesselJ_add_two`:
  `x (j_l + j_{l+2}) = (2l + 3) j_{l+1}`.
* `hasDerivAt_sphericalBesselJ_zero`, `hasDerivAt_sphericalBesselJ_succ`,
  `deriv_sphericalBesselJ_eq`, `hasDerivAt_pow_mul_sphericalBesselJ_succ`: `j_0' = -j_1`,
  `(2l + 3) j_{l+1}' = (l + 1) j_l - (l + 2) j_{l+2}`, `j_l' = (l / x) j_l - j_{l+1}` and
  `(x ^ (l + 2) j_{l+1})' = x ^ (l + 2) j_l`.
* `sphericalBesselJ_ode`: the spherical Bessel equation.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.SpecialFunctions

open Nat Filter Set
open scoped Topology ContDiff

/-- The `k`-th term `(-(x ^ 2) / 2) ^ k / (k! (2l + 2k + 1)‼)` of the reduced series of `j_l`. -/
def sphericalBesselTerm (l k : ℕ) (x : ℝ) : ℝ :=
  (-(x ^ 2) / 2) ^ k / (k ! * (2 * l + 2 * k + 1)‼)

/-- The even entire function `g_l x = j_l x / x ^ l`, as the sum of the reduced series. -/
def reducedSphericalBesselJ (l : ℕ) (x : ℝ) : ℝ :=
  ∑' k, sphericalBesselTerm l k x

/-- The spherical Bessel function of the first kind,
`j_l x = x ^ l ∑' k, (-(x ^ 2) / 2) ^ k / (k! (2l + 2k + 1)‼)`. -/
def sphericalBesselJ (l : ℕ) (x : ℝ) : ℝ :=
  x ^ l * ∑' k, (-(x ^ 2) / 2) ^ k / (k ! * (2 * l + 2 * k + 1)‼)

/-- `j_l x = x ^ l g_l x`. -/
theorem sphericalBesselJ_eq_pow_mul (l : ℕ) (x : ℝ) :
    sphericalBesselJ l x = x ^ l * reducedSphericalBesselJ l x :=
  rfl

/-- The denominator `k! (2l + 2k + 1)‼` of the terms is positive. -/
theorem sphericalBesselTerm_denom_pos (l k : ℕ) :
    0 < ((k ! : ℕ) : ℝ) * ((2 * l + 2 * k + 1)‼ : ℕ) := by
  have h₁ := Nat.factorial_pos k
  have h₂ := Nat.doubleFactorial_pos (2 * l + 2 * k + 1)
  positivity

/-- Each term is bounded by the corresponding term of the exponential series of `x ^ 2 / 2`. -/
theorem abs_sphericalBesselTerm_le (l k : ℕ) (x : ℝ) :
    |sphericalBesselTerm l k x| ≤ (x ^ 2 / 2) ^ k / k ! := by
  have hk : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  have hd : (1 : ℝ) ≤ ((2 * l + 2 * k + 1)‼ : ℕ) := by
    exact_mod_cast Nat.doubleFactorial_pos _
  rw [sphericalBesselTerm, abs_div, abs_pow, abs_div, abs_neg, abs_of_nonneg (sq_nonneg x),
    abs_two, abs_of_pos (sphericalBesselTerm_denom_pos l k)]
  apply div_le_div_of_nonneg_left (by positivity) hk
  nlinarith

/-- The reduced series converges at every real point. -/
theorem summable_sphericalBesselTerm (l : ℕ) (x : ℝ) :
    Summable fun k ↦ sphericalBesselTerm l k x :=
  Summable.of_norm_bounded (Real.summable_pow_div_factorial (x ^ 2 / 2))
    fun k ↦ by simpa only [Real.norm_eq_abs] using abs_sphericalBesselTerm_le l k x

/-- The double factorial for consecutive term indices, with the index written as in the terms. -/
theorem doubleFactorial_succ_index (l k : ℕ) :
    (2 * l + 2 * (k + 1) + 1)‼ = (2 * l + 2 * k + 3) * (2 * l + 2 * k + 1)‼ := by
  rw [show 2 * l + 2 * (k + 1) + 1 = (2 * l + 2 * k + 1) + 2 by ring,
    Nat.doubleFactorial_add_two]

/-- Derivative of a single term of positive index. -/
theorem hasDerivAt_sphericalBesselTerm_succ (l m : ℕ) (x : ℝ) :
    HasDerivAt (sphericalBesselTerm l (m + 1)) (-x * sphericalBesselTerm (l + 1) m x) x := by
  have hbase : HasDerivAt (fun y : ℝ ↦ -(y ^ 2) / 2) (-x) x := by
    have := ((hasDerivAt_pow 2 x).neg).div_const 2
    convert this using 1
    push_cast
    ring
  have h := (hbase.pow (m + 1)).div_const
    (((m + 1) ! : ℕ) * ((2 * l + 2 * (m + 1) + 1)‼ : ℕ) : ℝ)
  have hm : (0 : ℝ) < m ! := by exact_mod_cast Nat.factorial_pos m
  have hd : (0 : ℝ) < ((2 * l + 2 * m + 1)‼ : ℕ) := by exact_mod_cast Nat.doubleFactorial_pos _
  have hval : -x * sphericalBesselTerm (l + 1) m x =
      ((m + 1 : ℕ) : ℝ) * (-(x ^ 2) / 2) ^ m * -x /
        (((m + 1) ! : ℕ) * ((2 * l + 2 * (m + 1) + 1)‼ : ℕ) : ℝ) := by
    unfold sphericalBesselTerm
    rw [show 2 * (l + 1) + 2 * m + 1 = 2 * l + 2 * m + 1 + 2 by ring,
      doubleFactorial_succ_index, Nat.doubleFactorial_add_two, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  rw [hval]
  rw [Nat.add_sub_cancel] at h
  exact h

/-- Term by term differentiation: `g_l' x = -x g_{l+1} x`. -/
theorem hasDerivAt_reducedSphericalBesselJ (l : ℕ) (x : ℝ) :
    HasDerivAt (reducedSphericalBesselJ l) (-x * reducedSphericalBesselJ (l + 1) x) x := by
  set R : ℝ := |x| + 1 with hR
  have hRpos : 0 < R := by positivity
  let g' : ℕ → ℝ → ℝ := fun k y ↦ match k with
    | 0 => 0
    | m + 1 => -y * sphericalBesselTerm (l + 1) m y
  let u : ℕ → ℝ := fun k ↦ match k with
    | 0 => 0
    | m + 1 => R * ((R ^ 2 / 2) ^ m / m !)
  have hu : Summable u := by
    rw [← summable_nat_add_iff 1]
    exact (Real.summable_pow_div_factorial (R ^ 2 / 2)).mul_left R
  have hg : ∀ k y, y ∈ Metric.ball (0 : ℝ) R →
      HasDerivAt (sphericalBesselTerm l k) (g' k y) y := by
    intro k y _
    cases k with
    | zero =>
      have h0 : sphericalBesselTerm l 0 = fun _ ↦ 1 / (((2 * l + 1)‼ : ℕ) : ℝ) := by
        funext z
        simp [sphericalBesselTerm]
      rw [h0]
      exact hasDerivAt_const y _
    | succ m => exact hasDerivAt_sphericalBesselTerm_succ l m y
  have hg' : ∀ k y, y ∈ Metric.ball (0 : ℝ) R → ‖g' k y‖ ≤ u k := by
    intro k y hy
    cases k with
    | zero => simp [g', u]
    | succ m =>
      have hy' : |y| ≤ R := by
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
        exact hy.le
      have hsq : y ^ 2 ≤ R ^ 2 := by
        rw [← sq_abs y]
        exact pow_le_pow_left₀ (abs_nonneg y) hy' 2
      have hterm := abs_sphericalBesselTerm_le (l + 1) m y
      have hmono : (y ^ 2 / 2) ^ m / m ! ≤ (R ^ 2 / 2) ^ m / m ! := by
        gcongr
      simp only [g', u, Real.norm_eq_abs, abs_mul, abs_neg]
      exact mul_le_mul hy' (hterm.trans hmono) (abs_nonneg _) hRpos.le
  have hx : x ∈ Metric.ball (0 : ℝ) R := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, hR]
    linarith
  have h := hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0 : ℝ) R).isPreconnected hg hg' (Metric.mem_ball_self hRpos)
    (summable_sphericalBesselTerm l 0) hx
  have hsum : Summable fun k ↦ g' k x :=
    Summable.of_norm_bounded hu fun k ↦ hg' k x hx
  rw [hsum.tsum_eq_zero_add] at h
  simp only [g', zero_add, tsum_mul_left] at h
  exact h

/-- `g_l` is differentiable. -/
theorem differentiable_reducedSphericalBesselJ (l : ℕ) :
    Differentiable ℝ (reducedSphericalBesselJ l) :=
  fun x ↦ (hasDerivAt_reducedSphericalBesselJ l x).differentiableAt

/-- The derivative of `g_l` as a function. -/
theorem deriv_reducedSphericalBesselJ (l : ℕ) :
    deriv (reducedSphericalBesselJ l) = fun x ↦ -x * reducedSphericalBesselJ (l + 1) x :=
  funext fun x ↦ (hasDerivAt_reducedSphericalBesselJ l x).deriv

/-- The coefficients `(-1/2) ^ k / (k! (2l + 2k + 1)‼)` of `g_l` as a power series in
`x ^ 2`. -/
def reducedSphericalBesselCoeff (l k : ℕ) : ℝ :=
  (-1 / 2) ^ k / (k ! * (2 * l + 2 * k + 1)‼)

/-- The terms of the reduced series are monomials in `x ^ 2`. -/
theorem sphericalBesselTerm_eq_coeff_mul (l k : ℕ) (x : ℝ) :
    sphericalBesselTerm l k x = reducedSphericalBesselCoeff l k * (x ^ 2) ^ k := by
  unfold sphericalBesselTerm reducedSphericalBesselCoeff
  rw [show -(x ^ 2) / 2 = (-1 / 2) * x ^ 2 by ring, mul_pow]
  ring

/-- The magnitude of the coefficients. -/
theorem norm_reducedSphericalBesselCoeff (l k : ℕ) :
    ‖reducedSphericalBesselCoeff l k‖ = (1 / 2) ^ k / (k ! * (2 * l + 2 * k + 1)‼) := by
  unfold reducedSphericalBesselCoeff
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos (sphericalBesselTerm_denom_pos l k)]
  norm_num

/-- The power series of `g_l` in `x ^ 2` has infinite radius. -/
theorem radius_ofScalars_reducedSphericalBesselCoeff (l : ℕ) :
    (FormalMultilinearSeries.ofScalars ℝ (reducedSphericalBesselCoeff l)).radius = ⊤ := by
  refine FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto ℝ _
    (Eventually.of_forall fun k ↦ ?_) ?_
  · have := sphericalBesselTerm_denom_pos l k
    unfold reducedSphericalBesselCoeff
    exact div_ne_zero (pow_ne_zero _ (by norm_num)) this.ne'
  · have hratio (n : ℕ) : ‖reducedSphericalBesselCoeff l n.succ‖ /
        ‖reducedSphericalBesselCoeff l n‖ = 1 / (2 * ((n : ℝ) + 1) * (2 * l + 2 * n + 3)) := by
      have hk : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
      have hd : (0 : ℝ) < ((2 * l + 2 * n + 1)‼ : ℕ) := by
        exact_mod_cast Nat.doubleFactorial_pos _
      rw [norm_reducedSphericalBesselCoeff, norm_reducedSphericalBesselCoeff, Nat.succ_eq_add_one,
        doubleFactorial_succ_index, Nat.factorial_succ]
      push_cast
      field_simp
      ring
    simp_rw [hratio]
    refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith

/-- The entire function `G_l` with `g_l x = G_l (x ^ 2)`. -/
def reducedSphericalBesselJSq (l : ℕ) (t : ℝ) : ℝ :=
  ∑' k, reducedSphericalBesselCoeff l k * t ^ k

/-- `g_l x = G_l (x ^ 2)`. -/
theorem reducedSphericalBesselJ_eq_sq (l : ℕ) (x : ℝ) :
    reducedSphericalBesselJ l x = reducedSphericalBesselJSq l (x ^ 2) := by
  unfold reducedSphericalBesselJ reducedSphericalBesselJSq
  simp_rw [sphericalBesselTerm_eq_coeff_mul]

/-- `G_l` is analytic on `ℝ`. -/
theorem analyticOnNhd_reducedSphericalBesselJSq (l : ℕ) :
    AnalyticOnNhd ℝ (reducedSphericalBesselJSq l) univ := by
  have h := (FormalMultilinearSeries.ofScalars ℝ
    (reducedSphericalBesselCoeff l)).hasFPowerSeriesOnBall
    (by rw [radius_ofScalars_reducedSphericalBesselCoeff]; exact WithTop.top_pos)
  rw [radius_ofScalars_reducedSphericalBesselCoeff] at h
  have h' : AnalyticOnNhd ℝ
      (FormalMultilinearSeries.ofScalars ℝ (reducedSphericalBesselCoeff l)).sum univ := by
    simpa using h.analyticOnNhd
  have heq : reducedSphericalBesselJSq l =
      FormalMultilinearSeries.ofScalarsSum (E := ℝ) (reducedSphericalBesselCoeff l) := by
    rw [FormalMultilinearSeries.ofScalarsSum_eq_tsum]
    simp only [smul_eq_mul]
    rfl
  rw [heq]
  exact h'

/-- `G_l` is smooth, and analytic. -/
theorem contDiff_reducedSphericalBesselJSq (l : ℕ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (reducedSphericalBesselJSq l) :=
  (analyticOnNhd_reducedSphericalBesselJSq l).contDiff

/-- `g_l` is analytic on `ℝ`. -/
theorem analyticOnNhd_reducedSphericalBesselJ (l : ℕ) :
    AnalyticOnNhd ℝ (reducedSphericalBesselJ l) univ := by
  rw [show reducedSphericalBesselJ l = fun x ↦ reducedSphericalBesselJSq l (x ^ 2) from
    funext (reducedSphericalBesselJ_eq_sq l)]
  exact (analyticOnNhd_reducedSphericalBesselJSq l).comp (fun x _ ↦ analyticAt_id.pow 2)
    (mapsTo_univ _ _)

/-- `g_l` is smooth, and analytic. -/
theorem contDiff_reducedSphericalBesselJ (l : ℕ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (reducedSphericalBesselJ l) :=
  (analyticOnNhd_reducedSphericalBesselJ l).contDiff

/-- The terms of consecutive orders satisfy
`t_{l,m+1} = (2l + 3) t_{l+1,m+1} - x ^ 2 t_{l+2,m}`. -/
theorem sphericalBesselTerm_succ_eq (l m : ℕ) (x : ℝ) :
    sphericalBesselTerm l (m + 1) x = (2 * l + 3) * sphericalBesselTerm (l + 1) (m + 1) x -
      x ^ 2 * sphericalBesselTerm (l + 2) m x := by
  have hm : (0 : ℝ) < m ! := by exact_mod_cast Nat.factorial_pos m
  have hd : (0 : ℝ) < ((2 * l + 2 * m + 1)‼ : ℕ) := by exact_mod_cast Nat.doubleFactorial_pos _
  unfold sphericalBesselTerm
  rw [show 2 * (l + 1) + 2 * (m + 1) + 1 = 2 * l + 2 * m + 1 + 2 + 2 by ring,
    show 2 * (l + 2) + 2 * m + 1 = 2 * l + 2 * m + 1 + 2 + 2 by ring,
    show 2 * l + 2 * (m + 1) + 1 = 2 * l + 2 * m + 1 + 2 by ring, Nat.factorial_succ]
  simp only [Nat.doubleFactorial_add_two]
  have hx : x ^ 2 = -2 * (-(x ^ 2) / 2) := by ring
  rw [hx]
  generalize -(x ^ 2) / 2 = y
  push_cast
  field_simp
  ring

/-- The first terms of consecutive orders satisfy `t_{l,0} = (2l + 3) t_{l+1,0}`. -/
theorem sphericalBesselTerm_zero_eq (l : ℕ) (x : ℝ) :
    sphericalBesselTerm l 0 x = (2 * l + 3) * sphericalBesselTerm (l + 1) 0 x := by
  have hd : (0 : ℝ) < ((2 * l + 1)‼ : ℕ) := by exact_mod_cast Nat.doubleFactorial_pos _
  unfold sphericalBesselTerm
  rw [show 2 * (l + 1) + 2 * 0 + 1 = 2 * l + 1 + 2 by ring, Nat.doubleFactorial_add_two]
  push_cast
  field_simp
  ring

/-- The reduced series without its first term. -/
theorem hasSum_sphericalBesselTerm_succ (l : ℕ) (x : ℝ) :
    HasSum (fun m ↦ sphericalBesselTerm l (m + 1) x)
      (reducedSphericalBesselJ l x - sphericalBesselTerm l 0 x) := by
  have h := (hasSum_nat_add_iff' 1).mpr (summable_sphericalBesselTerm l x).hasSum
  rw [Finset.sum_range_one] at h
  exact h

/-- The three-term relation `g_l = (2l + 3) g_{l+1} - x ^ 2 g_{l+2}`. -/
theorem reducedSphericalBesselJ_eq_sub (l : ℕ) (x : ℝ) :
    reducedSphericalBesselJ l x = (2 * l + 3) * reducedSphericalBesselJ (l + 1) x -
      x ^ 2 * reducedSphericalBesselJ (l + 2) x := by
  have hA := hasSum_sphericalBesselTerm_succ l x
  have hC : HasSum (fun m ↦ sphericalBesselTerm (l + 2) m x)
      (reducedSphericalBesselJ (l + 2) x) := (summable_sphericalBesselTerm (l + 2) x).hasSum
  have hBC := ((hasSum_sphericalBesselTerm_succ (l + 1) x).mul_left (2 * (l : ℝ) + 3)).sub
    (hC.mul_left (x ^ 2))
  have hfun : (fun m ↦ sphericalBesselTerm l (m + 1) x) = fun m ↦
      (2 * (l : ℝ) + 3) * sphericalBesselTerm (l + 1) (m + 1) x -
        x ^ 2 * sphericalBesselTerm (l + 2) m x :=
    funext fun m ↦ sphericalBesselTerm_succ_eq l m x
  rw [hfun] at hA
  have h := hA.unique hBC
  have h₀ := sphericalBesselTerm_zero_eq l x
  linear_combination h + h₀

/-- The value at the origin, `g_l 0 = 1 / (2l + 1)‼`. -/
theorem reducedSphericalBesselJ_zero (l : ℕ) :
    reducedSphericalBesselJ l 0 = 1 / ((2 * l + 1)‼ : ℝ) := by
  unfold reducedSphericalBesselJ
  rw [tsum_eq_single 0 fun k hk ↦ by simp [sphericalBesselTerm, hk]]
  simp [sphericalBesselTerm]

/-- `g_l` is even. -/
theorem reducedSphericalBesselJ_neg (l : ℕ) (x : ℝ) :
    reducedSphericalBesselJ l (-x) = reducedSphericalBesselJ l x := by
  simp only [reducedSphericalBesselJ, sphericalBesselTerm, neg_sq]

/-- `g_l` is positive at the origin. -/
theorem reducedSphericalBesselJ_zero_pos (l : ℕ) : 0 < reducedSphericalBesselJ l 0 := by
  rw [reducedSphericalBesselJ_zero]
  have := Nat.doubleFactorial_pos (2 * l + 1)
  positivity

/-- `j_l` has parity `(-1) ^ l`. -/
theorem sphericalBesselJ_neg (l : ℕ) (x : ℝ) :
    sphericalBesselJ l (-x) = (-1) ^ l * sphericalBesselJ l x := by
  rw [sphericalBesselJ_eq_pow_mul, sphericalBesselJ_eq_pow_mul, reducedSphericalBesselJ_neg,
    neg_pow]
  ring

/-- `j_0 = g_0`: the function of order zero is its reduced series. -/
theorem sphericalBesselJ_zero_left (x : ℝ) :
    sphericalBesselJ 0 x = reducedSphericalBesselJ 0 x := by
  rw [sphericalBesselJ_eq_pow_mul, pow_zero, one_mul]

/-- `j_0 0 = 1`. -/
theorem sphericalBesselJ_zero_zero : sphericalBesselJ 0 0 = 1 := by
  rw [sphericalBesselJ_zero_left, reducedSphericalBesselJ_zero]
  simp

/-- `j_l 0 = 0` for `l ≥ 1`. -/
theorem sphericalBesselJ_succ_zero (l : ℕ) : sphericalBesselJ (l + 1) 0 = 0 := by
  rw [sphericalBesselJ_eq_pow_mul]
  simp

/-- `j_l` is analytic on `ℝ`. -/
theorem analyticOnNhd_sphericalBesselJ (l : ℕ) : AnalyticOnNhd ℝ (sphericalBesselJ l) univ :=
  fun x _ ↦ (analyticAt_id.pow l).mul (analyticOnNhd_reducedSphericalBesselJ l x (mem_univ x))

/-- `j_l` is smooth, and analytic. -/
theorem contDiff_sphericalBesselJ (l : ℕ) {n : WithTop ℕ∞} : ContDiff ℝ n (sphericalBesselJ l) :=
  (analyticOnNhd_sphericalBesselJ l).contDiff

/-- `j_l` is differentiable. -/
theorem differentiable_sphericalBesselJ (l : ℕ) : Differentiable ℝ (sphericalBesselJ l) :=
  (contDiff_sphericalBesselJ l (n := 1)).differentiable one_ne_zero

/-- `j_l` is continuous. -/
theorem continuous_sphericalBesselJ (l : ℕ) : Continuous (sphericalBesselJ l) :=
  (differentiable_sphericalBesselJ l).continuous

/-- The three-term recurrence `x (j_l + j_{l+2}) = (2l + 3) j_{l+1}`, valid at every real
point. -/
theorem mul_sphericalBesselJ_add_sphericalBesselJ (l : ℕ) (x : ℝ) :
    x * (sphericalBesselJ l x + sphericalBesselJ (l + 2) x) =
      (2 * l + 3) * sphericalBesselJ (l + 1) x := by
  simp only [sphericalBesselJ_eq_pow_mul]
  rw [reducedSphericalBesselJ_eq_sub l x]
  ring

/-- The derivative of `j_l` in terms of `g_l` and `g_{l+1}`. -/
theorem hasDerivAt_sphericalBesselJ (l : ℕ) (x : ℝ) :
    HasDerivAt (sphericalBesselJ l)
      (l * x ^ (l - 1) * reducedSphericalBesselJ l x -
        x ^ (l + 1) * reducedSphericalBesselJ (l + 1) x) x := by
  have h := (hasDerivAt_pow l x).mul (hasDerivAt_reducedSphericalBesselJ l x)
  refine h.congr_deriv ?_
  ring

/-- `x j_l' = l j_l - x j_{l+1}`. -/
theorem mul_deriv_sphericalBesselJ (l : ℕ) (x : ℝ) :
    x * deriv (sphericalBesselJ l) x =
      l * sphericalBesselJ l x - x * sphericalBesselJ (l + 1) x := by
  rw [(hasDerivAt_sphericalBesselJ l x).deriv]
  simp only [sphericalBesselJ_eq_pow_mul]
  rcases l with _ | l
  · simp
  · simp only [Nat.add_sub_cancel]
    push_cast
    ring

/-- `j_0' = -j_1`. -/
theorem hasDerivAt_sphericalBesselJ_zero (x : ℝ) :
    HasDerivAt (sphericalBesselJ 0) (-sphericalBesselJ 1 x) x := by
  convert hasDerivAt_sphericalBesselJ 0 x using 1
  simp [sphericalBesselJ_eq_pow_mul]

/-- `(2l + 3) j_{l+1}' = (l + 1) j_l - (l + 2) j_{l+2}`. -/
theorem hasDerivAt_sphericalBesselJ_succ (l : ℕ) (x : ℝ) :
    HasDerivAt (sphericalBesselJ (l + 1))
      (((l + 1) * sphericalBesselJ l x - (l + 2) * sphericalBesselJ (l + 2) x) /
        (2 * l + 3)) x := by
  convert hasDerivAt_sphericalBesselJ (l + 1) x using 1
  simp only [sphericalBesselJ_eq_pow_mul, Nat.add_sub_cancel]
  rw [reducedSphericalBesselJ_eq_sub l x]
  push_cast
  field_simp
  ring

/-- The derivative of `j_0` as a function. -/
theorem deriv_sphericalBesselJ_zero :
    deriv (sphericalBesselJ 0) = fun x ↦ -sphericalBesselJ 1 x :=
  funext fun x ↦ (hasDerivAt_sphericalBesselJ_zero x).deriv

/-- The derivative of `j_{l+1}` as a function. -/
theorem deriv_sphericalBesselJ_succ (l : ℕ) :
    deriv (sphericalBesselJ (l + 1)) = fun x ↦
      ((l + 1) * sphericalBesselJ l x - (l + 2) * sphericalBesselJ (l + 2) x) / (2 * l + 3) :=
  funext fun x ↦ (hasDerivAt_sphericalBesselJ_succ l x).deriv

/-- `j_{l+2} x = (2l + 3) x⁻¹ j_{l+1} x - j_l x` for `x ≠ 0`. -/
theorem sphericalBesselJ_add_two {x : ℝ} (hx : x ≠ 0) (l : ℕ) :
    sphericalBesselJ (l + 2) x = (2 * l + 3) / x * sphericalBesselJ (l + 1) x -
      sphericalBesselJ l x := by
  have h := mul_sphericalBesselJ_add_sphericalBesselJ l x
  field_simp
  linarith

/-- `j_l' x = l x⁻¹ j_l x - j_{l+1} x` for `x ≠ 0`. -/
theorem deriv_sphericalBesselJ_eq {x : ℝ} (hx : x ≠ 0) (l : ℕ) :
    deriv (sphericalBesselJ l) x = l / x * sphericalBesselJ l x - sphericalBesselJ (l + 1) x := by
  have h := mul_deriv_sphericalBesselJ l x
  field_simp
  linarith

/-- `(x ^ (l + 2) j_{l+1})' = x ^ (l + 2) j_l`. -/
theorem hasDerivAt_pow_mul_sphericalBesselJ_succ (l : ℕ) (x : ℝ) :
    HasDerivAt (fun y ↦ y ^ (l + 2) * sphericalBesselJ (l + 1) y)
      (x ^ (l + 2) * sphericalBesselJ l x) x := by
  have hfun : (fun y ↦ y ^ (l + 2) * sphericalBesselJ (l + 1) y) =
      fun y ↦ y ^ (2 * l + 3) * reducedSphericalBesselJ (l + 1) y := by
    funext y
    rw [sphericalBesselJ_eq_pow_mul]
    ring
  rw [hfun]
  have h := (hasDerivAt_pow (2 * l + 3) x).mul (hasDerivAt_reducedSphericalBesselJ (l + 1) x)
  refine h.congr_deriv ?_
  rw [sphericalBesselJ_eq_pow_mul, reducedSphericalBesselJ_eq_sub l x,
    show 2 * l + 3 - 1 = 2 * l + 2 by omega]
  push_cast
  ring

/-- The flux `x ^ 2 j_l'` written without negative powers. -/
theorem sq_mul_deriv_sphericalBesselJ (l : ℕ) (x : ℝ) :
    x ^ 2 * deriv (sphericalBesselJ l) x =
      l * x ^ (l + 1) * reducedSphericalBesselJ l x -
        x ^ (l + 3) * reducedSphericalBesselJ (l + 1) x := by
  rw [(hasDerivAt_sphericalBesselJ l x).deriv]
  rcases l with _ | l
  · simp only [CharP.cast_eq_zero, zero_mul, zero_sub]
    ring
  · simp only [Nat.add_sub_cancel]
    ring

/-- The flux `x ^ 2 j_l'` has derivative `(l (l + 1) - x ^ 2) j_l`. -/
theorem hasDerivAt_sq_mul_deriv_sphericalBesselJ (l : ℕ) (x : ℝ) :
    HasDerivAt (fun y ↦ y ^ 2 * deriv (sphericalBesselJ l) y)
      ((l * (l + 1) - x ^ 2) * sphericalBesselJ l x) x := by
  have hfun : (fun y ↦ y ^ 2 * deriv (sphericalBesselJ l) y) = fun y ↦
      l * y ^ (l + 1) * reducedSphericalBesselJ l y -
        y ^ (l + 3) * reducedSphericalBesselJ (l + 1) y :=
    funext (sq_mul_deriv_sphericalBesselJ l)
  rw [hfun]
  have h := (((hasDerivAt_pow (l + 1) x).const_mul (l : ℝ)).mul
    (hasDerivAt_reducedSphericalBesselJ l x)).sub
    ((hasDerivAt_pow (l + 3) x).mul (hasDerivAt_reducedSphericalBesselJ (l + 1) x))
  convert h using 1
  rw [sphericalBesselJ_eq_pow_mul, reducedSphericalBesselJ_eq_sub l x]
  simp only [Nat.add_sub_cancel]
  push_cast
  ring

/-- `j_l'` has derivative `j_l''` at every point. -/
theorem hasDerivAt_deriv_sphericalBesselJ (l : ℕ) (x : ℝ) :
    HasDerivAt (deriv (sphericalBesselJ l)) (deriv (deriv (sphericalBesselJ l)) x) x := by
  have h := (contDiff_sphericalBesselJ l (n := ∞)).iterate_deriv 1
  rw [Function.iterate_one] at h
  exact (h.differentiable (by simp) x).hasDerivAt

/-- The spherical Bessel equation `x ^ 2 j_l'' + 2 x j_l' + (x ^ 2 - l (l + 1)) j_l = 0`. -/
theorem sphericalBesselJ_ode (l : ℕ) (x : ℝ) :
    x ^ 2 * deriv (deriv (sphericalBesselJ l)) x + 2 * x * deriv (sphericalBesselJ l) x +
      (x ^ 2 - l * (l + 1)) * sphericalBesselJ l x = 0 := by
  have h₁ := (hasDerivAt_pow 2 x).mul (hasDerivAt_deriv_sphericalBesselJ l x)
  have h₂ := hasDerivAt_sq_mul_deriv_sphericalBesselJ l x
  have h := h₁.unique h₂
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at h
  linarith

end PDE.Analysis.SpecialFunctions
