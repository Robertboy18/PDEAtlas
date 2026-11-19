/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import PDE.Analysis.Integration.ParametricIntervalSmooth.Local
import PDE.Analysis.Calculus.LocalExtrema

/-!
# The axial modes of the stream function in the cylinder

For the stream profile `Ψ(s, z)` in the squared radius `s = r²` (so that the angular stream
function is `r Ψ(r², z)`), one sine mode `Ψ(s) sin(μ z)` of the stream function equation of
the cylinder solves

```text
4 s Ψ'' + 8 Ψ' - μ² Ψ = -F,     Ψ(1) = 0,
```

regularly at the axis `s = 0`. The regular solutions of the homogeneous equation are the multiples
of `modeProfile (μ² s / 4)`, where `modeProfile t = ∑ tʲ / (j! (j + 1)!)` solves `t g'' + 2 g' = g`
(`modeProfile_equation`; it is `I₁(2√t)/√t` for the modified Bessel function `I₁`). The regular
solution with `Ψ(1) = 0` is `modeSolution μ F`.

## Main definitions

* `profileSeries k`: the series `∑ tʲ / (j! (j + k + 1)!)`, the `k`th derivative of
  `modeProfile`.
* `modeProfile`: the regular solution of `t g'' + 2 g' = g` with `g(0) = 1`.
* `homogeneousMode μ`: `s ↦ modeProfile (μ² s / 4)`, a regular solution of
  `4 s f'' + 8 f' = μ² f`.
* `modeAverage`, `modeQuotient`, `particularMode`: the averaged source
  `B(σ) = ∫₀¹ τ f(στ) F(στ) dτ`, the quotient `B / f²` and the particular solution
  `-(1/4) f(s) ∫₀ˢ B / f²` of reduction of order.
* `modeSolution μ F`: the regular solution with `Ψ(1) = 0`.

## Main results

* `contDiff_profileSeries`, `hasDerivAt_profileSeries`: smoothness and derivatives.
* `modeProfile_equation`, `one_le_modeProfile`, `modeProfile_pos`.
* `modeAverage_identity`: `σ B' + 2 B = f F`, the identity behind reduction of order.
* `contDiffOn_modeSolution`, `modeSolution_equation`, `modeSolution_one`: the mode solution is
  smooth on `s > -4/μ²`, solves the mode equation there and vanishes at the wall.
* `le_of_modeEquation`: the maximum principle for the mode equation on `[0, 1]`.
* `iteratedDeriv_modeSolution_equation`: the differentiated mode equation.
* `abs_modeSolution_le`, `abs_iteratedDeriv_modeSolution_le`: on the collar interval
  `[-2/μ², 1 + 2/μ²]`, `|Ψ| ≤ 3 sup|F| / μ²` and
  `|Ψ^{(m)}| ≤ 3 (1 + μ²)^m (∑_{j ≤ m} sup|F^{(j)}|) / μ²`.

## How it works

The homogeneous mode is an explicit power series (`modeProfile_equation`), positive on the mode
domain `s > -4/μ²` (`modeProfile_pos`), so reduction of order works there. By
`modeAverage_identity`, `particularMode μ F` solves the equation and is regular at the axis, and
`modeSolution μ F` subtracts the multiple of `homogeneousMode μ` that makes it vanish at `s = 1`.
For the bounds, the maximum principle `le_of_modeEquation`, applied to `Ψ` and `-Ψ`, gives
`|Ψ| ≤ sup|F| / μ²` on `[0, 1]`. By the differentiated equation, `s^{m+2} Ψ^{(m+1)}` has derivative
`(1/4) s^{m+1} (μ² Ψ^{(m)} - F^{(m)})`, so the mean value theorem on the segment from `0` to `s`
bounds the next derivative by `(μ² K + M) / 4` on the collar interval when `|Ψ^{(m)}| ≤ K` and
`|F^{(m)}| ≤ M` (`abs_iteratedDeriv_succ_modeSolution_le`). With `m = 0`, the mean value theorem
across a collar of length `2/μ²` bounds `|Ψ|` at its maximum point, which gives the factor `3`, and
induction on `m` gives the derivative bounds.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 6, (6.3)-(6.4), for the
  stream function equation in the cylinder.
  <https://arxiv.org/abs/2210.07191v4>
* G. N. Watson, *A Treatise on the Theory of Bessel Functions*, 2nd ed., Cambridge University Press,
  1944, Section 3.7, p. 77, for the series of `I₁`.
-/

@[expose] public section

namespace Euler.Cylinder

open Filter Nat
open scoped Topology

set_option linter.missingDocs true

noncomputable section

/-! ### The profile series -/

/-- The power series `∑ tʲ / (j! (j + k + 1)!)`. For `k = 0` it is `modeProfile`; its derivative
is the series with `k + 1` (`hasDerivAt_profileSeries`). -/
def profileSeries (k : ℕ) (t : ℝ) : ℝ :=
  ∑' j : ℕ, t ^ j / ((j ! : ℝ) * ((j + k + 1) ! : ℝ))

/-- The terms of the profile series are bounded by those of the exponential series. -/
theorem abs_profileSeries_term_le (k j : ℕ) (t : ℝ) :
    |t ^ j / ((j ! : ℝ) * ((j + k + 1) ! : ℝ))| ≤ |t| ^ j / (j ! : ℝ) := by
  have h1 : (1 : ℝ) ≤ ((j + k + 1) ! : ℝ) := Nat.one_le_cast.2 (Nat.factorial_pos _)
  have hj : (0 : ℝ) < (j ! : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hk : (0 : ℝ) < ((j + k + 1) ! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [abs_div, abs_pow, abs_of_pos (mul_pos hj hk)]
  apply div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg _) _) hj
  nlinarith

/-- The profile series converges everywhere. -/
theorem summable_profileSeries (k : ℕ) (t : ℝ) :
    Summable fun j : ℕ ↦ t ^ j / ((j ! : ℝ) * ((j + k + 1) ! : ℝ)) :=
  Summable.of_norm_bounded (Real.summable_pow_div_factorial |t|) fun j ↦ by
    rw [Real.norm_eq_abs]
    exact abs_profileSeries_term_le k j t

/-- The termwise derivatives of the profile series, reindexed, form the next profile series. -/
theorem tsum_profileSeries_deriv (k : ℕ) (t : ℝ) :
    ∑' j : ℕ, (j : ℝ) * t ^ (j - 1) / ((j ! : ℝ) * ((j + k + 1) ! : ℝ)) =
      profileSeries (k + 1) t := by
  have hshift : ∀ j : ℕ, ((j + 1 : ℕ) : ℝ) * t ^ (j + 1 - 1) /
      (((j + 1) ! : ℝ) * ((j + 1 + k + 1) ! : ℝ)) =
      t ^ j / ((j ! : ℝ) * ((j + (k + 1) + 1) ! : ℝ)) := by
    intro j
    have hj : (0 : ℝ) < (j ! : ℝ) := by exact_mod_cast Nat.factorial_pos j
    have hk : (0 : ℝ) < ((j + (k + 1) + 1) ! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [show j + 1 + k + 1 = j + (k + 1) + 1 by ring, Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    field_simp
  have hsum : Summable fun j : ℕ ↦
      (j : ℝ) * t ^ (j - 1) / ((j ! : ℝ) * ((j + k + 1) ! : ℝ)) := by
    rw [← summable_nat_add_iff 1]
    simp only [hshift]
    exact summable_profileSeries (k + 1) t
  rw [hsum.tsum_eq_zero_add]
  simp only [CharP.cast_eq_zero, zero_mul, zero_div, zero_add]
  simp only [hshift, profileSeries]

/-- The derivative of the profile series. -/
theorem hasDerivAt_profileSeries (k : ℕ) (t : ℝ) :
    HasDerivAt (profileSeries k) (profileSeries (k + 1) t) t := by
  set R : ℝ := |t| + 1
  have hR : 0 ≤ R := by positivity
  set u : ℕ → ℝ := fun j ↦ (j : ℝ) * R ^ (j - 1) / (j ! : ℝ)
  have hu : Summable u := by
    rw [← summable_nat_add_iff 1]
    have : (fun j ↦ u (j + 1)) = fun j : ℕ ↦ R ^ j / (j ! : ℝ) := by
      funext j
      have hj : (0 : ℝ) < (j ! : ℝ) := by exact_mod_cast Nat.factorial_pos j
      simp only [u, Nat.add_sub_cancel, Nat.factorial_succ]
      push_cast
      field_simp
    rw [this]
    exact Real.summable_pow_div_factorial R
  have hderiv : ∀ (j : ℕ) (y : ℝ), y ∈ Metric.ball (0 : ℝ) R →
      HasDerivAt (fun z : ℝ ↦ z ^ j / ((j ! : ℝ) * ((j + k + 1) ! : ℝ)))
        ((j : ℝ) * y ^ (j - 1) / ((j ! : ℝ) * ((j + k + 1) ! : ℝ))) y := by
    intro j y _
    exact (hasDerivAt_pow j y).div_const _
  have hbound : ∀ (j : ℕ) (y : ℝ), y ∈ Metric.ball (0 : ℝ) R →
      ‖(j : ℝ) * y ^ (j - 1) / ((j ! : ℝ) * ((j + k + 1) ! : ℝ))‖ ≤ u j := by
    intro j y hy
    have hy' : |y| ≤ R := (mem_ball_zero_iff.1 hy).le
    have h1 : (1 : ℝ) ≤ ((j + k + 1) ! : ℝ) := Nat.one_le_cast.2 (Nat.factorial_pos _)
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, Nat.abs_cast,
      abs_of_pos (show (0 : ℝ) < (j ! : ℝ) * ((j + k + 1) ! : ℝ) by positivity)]
    calc (j : ℝ) * |y| ^ (j - 1) / ((j ! : ℝ) * ((j + k + 1) ! : ℝ))
        ≤ (j : ℝ) * R ^ (j - 1) / ((j ! : ℝ) * 1) := by gcongr
      _ = u j := by simp [u]
  have h := hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0 : ℝ) R).isPreconnected hderiv hbound (Metric.mem_ball_self (by positivity))
    (summable_profileSeries k 0)
    (mem_ball_zero_iff.2 (by simp only [R, Real.norm_eq_abs]; linarith))
  rwa [tsum_profileSeries_deriv] at h

/-- The derivative of the profile series as a function. -/
theorem deriv_profileSeries (k : ℕ) : deriv (profileSeries k) = profileSeries (k + 1) :=
  funext fun t ↦ (hasDerivAt_profileSeries k t).deriv

/-- The profile series are smooth. -/
theorem contDiff_profileSeries (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (profileSeries k) := by
  have key : ∀ n : ℕ, ∀ k : ℕ, ContDiff ℝ n (profileSeries k) := by
    intro n
    induction n with
    | zero =>
      intro k
      exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun t ↦
        (hasDerivAt_profileSeries k t).continuousAt)
    | succ n ih =>
      intro k
      rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by norm_cast,
        contDiff_succ_iff_deriv]
      refine ⟨fun t ↦ (hasDerivAt_profileSeries k t).differentiableAt, by simp, ?_⟩
      rw [deriv_profileSeries]
      exact ih (k + 1)
  exact contDiff_infty.2 fun n ↦ key n k

/-- The iterated derivatives of the profile series. -/
theorem iteratedDeriv_profileSeries (m k : ℕ) :
    iteratedDeriv m (profileSeries k) = profileSeries (k + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih, deriv_profileSeries]
    rfl

/-! ### The mode profile -/

/-- The mode profile `modeProfile t = ∑ tʲ / (j! (j + 1)!)`, the regular solution of
`t g'' + 2 g' = g` with `g(0) = 1`. -/
def modeProfile : ℝ → ℝ :=
  profileSeries 0

/-- The mode profile is smooth. -/
theorem contDiff_modeProfile : ContDiff ℝ (⊤ : ℕ∞) modeProfile :=
  contDiff_profileSeries 0

/-- The derivative of the mode profile. -/
theorem deriv_modeProfile : deriv modeProfile = profileSeries 1 :=
  deriv_profileSeries 0

/-- The second derivative of the mode profile. -/
theorem iteratedDeriv_two_modeProfile : iteratedDeriv 2 modeProfile = profileSeries 2 :=
  iteratedDeriv_profileSeries 2 0

/-- **The mode profile equation** `t g'' + 2 g' = g`. -/
theorem profileSeries_equation (t : ℝ) :
    t * profileSeries 2 t + 2 * profileSeries 1 t = profileSeries 0 t := by
  have h0 := summable_profileSeries 0 t
  have h1 := summable_profileSeries 1 t
  have hdiff : profileSeries 0 t - 2 * profileSeries 1 t =
      ∑' j : ℕ, (t ^ j / ((j ! : ℝ) * ((j + 0 + 1) ! : ℝ)) -
        2 * (t ^ j / ((j ! : ℝ) * ((j + 1 + 1) ! : ℝ)))) := by
    rw [Summable.tsum_sub h0 (h1.mul_left 2), tsum_mul_left]
    rfl
  have hs : Summable fun j : ℕ ↦ (t ^ j / ((j ! : ℝ) * ((j + 0 + 1) ! : ℝ)) -
      2 * (t ^ j / ((j ! : ℝ) * ((j + 1 + 1) ! : ℝ)))) := h0.sub (h1.mul_left 2)
  have hterm : ∀ j : ℕ, t ^ (j + 1) / (((j + 1) ! : ℝ) * ((j + 1 + 0 + 1) ! : ℝ)) -
      2 * (t ^ (j + 1) / (((j + 1) ! : ℝ) * ((j + 1 + 1 + 1) ! : ℝ))) =
      t * (t ^ j / ((j ! : ℝ) * ((j + 2 + 1) ! : ℝ))) := by
    intro j
    have hj : (0 : ℝ) < (j ! : ℝ) := by exact_mod_cast Nat.factorial_pos j
    have hj2 : (0 : ℝ) < ((j + 2) ! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [show j + 1 + 0 + 1 = j + 2 by ring, show j + 1 + 1 + 1 = j + 2 + 1 by ring,
      Nat.factorial_succ (j + 2), Nat.factorial_succ j]
    push_cast
    field_simp
    ring
  rw [hs.tsum_eq_zero_add] at hdiff
  simp only [pow_zero, Nat.factorial_zero, zero_add, Nat.factorial_one, Nat.cast_one,
    mul_one, one_mul] at hdiff
  simp only [hterm, tsum_mul_left] at hdiff
  have : profileSeries 2 t = ∑' j : ℕ, t ^ j / ((j ! : ℝ) * ((j + 2 + 1) ! : ℝ)) := rfl
  rw [this]
  norm_num at hdiff
  linarith

/-- **The mode profile equation** `t g'' + 2 g' = g`. -/
theorem modeProfile_equation (t : ℝ) :
    t * iteratedDeriv 2 modeProfile t + 2 * deriv modeProfile t = modeProfile t := by
  rw [iteratedDeriv_two_modeProfile, deriv_modeProfile]
  exact profileSeries_equation t

/-- The mode profile is at least one on the nonnegative half-line. -/
theorem one_le_modeProfile {t : ℝ} (ht : 0 ≤ t) : 1 ≤ modeProfile t := by
  have h := (summable_profileSeries 0 t).le_tsum 0 fun j _ ↦ by positivity
  simpa [modeProfile, profileSeries] using h

/-- The coefficients of the first derivative series are at most `2^-(j+1)`. -/
theorem two_pow_le_factorial_mul (j : ℕ) : 2 ^ (j + 1) ≤ j ! * (j + 1 + 1) ! := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.factorial_succ j, show j + 1 + 1 + 1 = (j + 2) + 1 by ring, Nat.factorial_succ (j + 2),
      show j + 1 + 1 = j + 2 by ring] at *
    calc 2 ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) := by ring
      _ ≤ 2 * (j ! * (j + 2) !) := by omega
      _ ≤ (j + 1) * (j + 2 + 1) * (j ! * (j + 2) !) := by
          apply Nat.mul_le_mul_right
          nlinarith
      _ = (j + 1) * j ! * ((j + 2 + 1) * (j + 2) !) := by ring

/-- The derivative of the mode profile is at most one in absolute value on `[-1, 1]`. -/
theorem abs_profileSeries_one_le {t : ℝ} (ht : |t| ≤ 1) : |profileSeries 1 t| ≤ 1 := by
  have hb : ∀ j : ℕ, ‖t ^ j / ((j ! : ℝ) * ((j + 1 + 1) ! : ℝ))‖ ≤ (1 / 2) ^ (j + 1) := by
    intro j
    have hpos : (0 : ℝ) < (j ! : ℝ) * ((j + 1 + 1) ! : ℝ) := by positivity
    have h2 : ((2 : ℝ) ^ (j + 1)) ≤ (j ! : ℝ) * ((j + 1 + 1) ! : ℝ) := by
      exact_mod_cast two_pow_le_factorial_mul j
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hpos, div_pow, one_pow]
    calc |t| ^ j / ((j ! : ℝ) * ((j + 1 + 1) ! : ℝ))
        ≤ 1 / ((j ! : ℝ) * ((j + 1 + 1) ! : ℝ)) :=
          div_le_div_of_nonneg_right (pow_le_one₀ (abs_nonneg _) ht) hpos.le
      _ ≤ 1 / 2 ^ (j + 1) := one_div_le_one_div_of_le (by positivity) h2
  have hgeom : Summable fun j : ℕ ↦ ((1 : ℝ) / 2) ^ (j + 1) :=
    (summable_geometric_two).comp_injective (add_left_injective 1)
  calc |profileSeries 1 t| = ‖∑' j : ℕ, t ^ j / ((j ! : ℝ) * ((j + 1 + 1) ! : ℝ))‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∑' j : ℕ, ((1 : ℝ) / 2) ^ (j + 1) := tsum_of_norm_bounded hgeom.hasSum hb
    _ = 1 := by
        rw [show (fun j : ℕ ↦ ((1 : ℝ) / 2) ^ (j + 1)) = fun j ↦ 1 / 2 * (1 / 2) ^ j from
          funext fun j ↦ by ring, tsum_mul_left, tsum_geometric_two]
        norm_num

/-- The mode profile is positive on `(-1, ∞)`. -/
theorem modeProfile_pos {t : ℝ} (ht : -1 < t) : 0 < modeProfile t := by
  rcases le_or_gt 0 t with h | h
  · exact one_pos.trans_le (one_le_modeProfile h)
  · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope modeProfile (profileSeries 1) h
      (contDiff_modeProfile.continuous.continuousOn)
      (fun x _ ↦ hasDerivAt_profileSeries 0 x)
    have hc1 : |c| ≤ 1 := abs_le.2 ⟨by linarith [hc.1], by linarith [hc.2]⟩
    have hd := abs_profileSeries_one_le hc1
    have h0 : modeProfile 0 = 1 := by
      simp only [modeProfile, profileSeries]
      rw [tsum_eq_single 0 (fun j hj ↦ by simp [zero_pow hj])]
      simp
    rw [h0, eq_div_iff (by linarith)] at hslope
    have := abs_le.1 hd
    nlinarith

/-! ### The homogeneous mode -/

/-- The regular homogeneous mode `f_μ(s) = modeProfile (μ² s / 4)`, a solution of
`4 s f'' + 8 f' = μ² f`. -/
def homogeneousMode (μ s : ℝ) : ℝ :=
  modeProfile (μ ^ 2 * s / 4)

/-- The derivative of the homogeneous mode. -/
def homogeneousModeDeriv (μ s : ℝ) : ℝ :=
  μ ^ 2 / 4 * profileSeries 1 (μ ^ 2 * s / 4)

/-- The second derivative of the homogeneous mode. -/
def homogeneousModeDeriv₂ (μ s : ℝ) : ℝ :=
  (μ ^ 2 / 4) ^ 2 * profileSeries 2 (μ ^ 2 * s / 4)

/-- The homogeneous mode has derivative `homogeneousModeDeriv`. -/
theorem hasDerivAt_homogeneousMode (μ s : ℝ) :
    HasDerivAt (homogeneousMode μ) (homogeneousModeDeriv μ s) s := by
  have hlin : HasDerivAt (fun x : ℝ ↦ μ ^ 2 * x / 4) (μ ^ 2 / 4) s := by
    simpa using ((hasDerivAt_id s).const_mul (μ ^ 2)).div_const 4
  have h := (hasDerivAt_profileSeries 0 (μ ^ 2 * s / 4)).comp s hlin
  rw [show homogeneousMode μ = profileSeries 0 ∘ fun x ↦ μ ^ 2 * x / 4 from rfl]
  convert h using 1
  rw [homogeneousModeDeriv, mul_comm]

/-- The derivative of the homogeneous mode has derivative `homogeneousModeDeriv₂`. -/
theorem hasDerivAt_homogeneousModeDeriv (μ s : ℝ) :
    HasDerivAt (homogeneousModeDeriv μ) (homogeneousModeDeriv₂ μ s) s := by
  have hlin : HasDerivAt (fun x : ℝ ↦ μ ^ 2 * x / 4) (μ ^ 2 / 4) s := by
    simpa using ((hasDerivAt_id s).const_mul (μ ^ 2)).div_const 4
  have h := ((hasDerivAt_profileSeries 1 (μ ^ 2 * s / 4)).comp s hlin).const_mul (μ ^ 2 / 4)
  rw [show homogeneousModeDeriv μ = fun y ↦ μ ^ 2 / 4 * (profileSeries 1 ∘
    fun x ↦ μ ^ 2 * x / 4) y from rfl]
  convert h using 1
  rw [homogeneousModeDeriv₂]
  ring

/-- The homogeneous mode is smooth. -/
theorem contDiff_homogeneousMode (μ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (homogeneousMode μ) :=
  contDiff_modeProfile.comp ((contDiff_const.mul contDiff_id).div_const 4)

/-- The homogeneous mode equation `4 s f'' + 8 f' = μ² f`. -/
theorem homogeneousMode_equation (μ s : ℝ) :
    4 * s * homogeneousModeDeriv₂ μ s + 8 * homogeneousModeDeriv μ s =
      μ ^ 2 * homogeneousMode μ s := by
  have h := profileSeries_equation (μ ^ 2 * s / 4)
  simp only [homogeneousModeDeriv₂, homogeneousModeDeriv, homogeneousMode, modeProfile]
  linear_combination μ ^ 2 * h

/-- The homogeneous mode is positive for `s > -4/μ²`. -/
theorem homogeneousMode_pos {μ s : ℝ} (hμ : 0 < μ) (hs : -4 / μ ^ 2 < s) :
    0 < homogeneousMode μ s := by
  apply modeProfile_pos
  have hμ2 : 0 < μ ^ 2 := by positivity
  rw [div_lt_iff₀ hμ2] at hs
  linarith

/-- The homogeneous mode is at least one at the wall. -/
theorem one_le_homogeneousMode_one (μ : ℝ) : 1 ≤ homogeneousMode μ 1 :=
  one_le_modeProfile (by positivity)

/-! ### Reduction of order -/

/-- The averaged source `B(σ) = ∫₀¹ τ f_μ(στ) F(στ) dτ`. -/
def modeAverage (μ : ℝ) (F : ℝ → ℝ) (σ : ℝ) : ℝ :=
  ∫ τ in (0 : ℝ)..1, τ * (homogeneousMode μ (σ * τ) * F (σ * τ))

/-- The averaged source is smooth. -/
theorem contDiff_modeAverage (μ : ℝ) {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (modeAverage μ F) := by
  have hm : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ ↦ p.1 * p.2) := contDiff_fst.mul contDiff_snd
  have hH : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ ↦ p.2 * (homogeneousMode μ (p.1 * p.2) * F (p.1 * p.2))) :=
    contDiff_snd.mul (((contDiff_homogeneousMode μ).comp hm).mul (hF.comp hm))
  have heq : modeAverage μ F = fun x ↦ ∫ t in (0 : ℝ)..1,
      (fun p : ℝ × ℝ ↦ p.2 * (homogeneousMode μ (p.1 * p.2) * F (p.1 * p.2))) (x, t) := by
    funext x
    simp [modeAverage]
  rw [heq]
  exact PDE.Analysis.contDiff_intervalIntegral hH 0 1

/-- The weighted primitive identity `σ² B(σ) = ∫₀^σ u f_μ(u) F(u) du`. -/
theorem sq_mul_modeAverage (μ : ℝ) (F : ℝ → ℝ) (σ : ℝ) :
    σ ^ 2 * modeAverage μ F σ =
      ∫ u in (0 : ℝ)..σ, u * (homogeneousMode μ u * F u) := by
  rcases eq_or_ne σ 0 with rfl | hσ
  · simp
  have h := intervalIntegral.integral_comp_mul_left
    (fun u ↦ u * (homogeneousMode μ u * F u)) hσ (a := 0) (b := 1)
  simp only [mul_zero, mul_one, smul_eq_mul] at h
  have hB : modeAverage μ F σ =
      σ⁻¹ * ∫ τ in (0 : ℝ)..1, σ * τ * (homogeneousMode μ (σ * τ) * F (σ * τ)) := by
    rw [← intervalIntegral.integral_const_mul]
    unfold modeAverage
    congr 1
    funext τ
    field_simp
  rw [hB, h, ← mul_assoc, ← mul_assoc, show σ ^ 2 * σ⁻¹ * σ⁻¹ = 1 by field_simp, one_mul]

/-- **The reduction-of-order identity** `σ B'(σ) + 2 B(σ) = f_μ(σ) F(σ)`. -/
theorem modeAverage_identity (μ : ℝ) {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (σ : ℝ) :
    σ * deriv (modeAverage μ F) σ + 2 * modeAverage μ F σ =
      homogeneousMode μ σ * F σ := by
  have hcont : Continuous fun u ↦ u * (homogeneousMode μ u * F u) :=
    continuous_id.mul ((contDiff_homogeneousMode μ).continuous.mul hF.continuous)
  have hB := ((contDiff_modeAverage μ hF).differentiable (by simp)) σ
  have h1 : HasDerivAt (fun y ↦ y ^ 2 * modeAverage μ F y)
      (2 * σ * modeAverage μ F σ + σ ^ 2 * deriv (modeAverage μ F) σ) σ := by
    have := ((hasDerivAt_pow 2 σ).mul hB.hasDerivAt)
    convert this using 1
    simp
  have h2 : HasDerivAt (fun y ↦ y ^ 2 * modeAverage μ F y)
      (σ * (homogeneousMode μ σ * F σ)) σ := by
    rw [show (fun y ↦ y ^ 2 * modeAverage μ F y) =
        fun y ↦ ∫ u in (0 : ℝ)..y, u * (homogeneousMode μ u * F u) from
      funext (sq_mul_modeAverage μ F)]
    exact (hcont.integral_hasStrictDerivAt 0 σ).hasDerivAt
  have heq := h1.unique h2
  rcases eq_or_ne σ 0 with rfl | hσ
  · simp only [zero_mul, zero_add]
    have : modeAverage μ F 0 = homogeneousMode μ 0 * F 0 / 2 := by
      unfold modeAverage
      simp only [zero_mul]
      rw [intervalIntegral.integral_mul_const, integral_id]
      ring
    rw [this]
    ring
  · have : σ * (σ * deriv (modeAverage μ F) σ + 2 * modeAverage μ F σ) =
        σ * (homogeneousMode μ σ * F σ) := by linarith
    exact mul_left_cancel₀ hσ this

/-- The quotient `W(σ) = B(σ) / f_μ(σ)²` of reduction of order. -/
def modeQuotient (μ : ℝ) (F : ℝ → ℝ) (σ : ℝ) : ℝ :=
  modeAverage μ F σ / homogeneousMode μ σ ^ 2

/-- The particular mode `P(s) = -(1/4) f_μ(s) ∫₀ˢ W(σ) dσ`. -/
def particularMode (μ : ℝ) (F : ℝ → ℝ) (s : ℝ) : ℝ :=
  -(1 / 4) * homogeneousMode μ s * ∫ σ in (0 : ℝ)..s, modeQuotient μ F σ

/-- **The mode solution**: the regular solution of `4 s Ψ'' + 8 Ψ' - μ² Ψ = -F` with
`Ψ(1) = 0`. -/
def modeSolution (μ : ℝ) (F : ℝ → ℝ) (s : ℝ) : ℝ :=
  particularMode μ F s - particularMode μ F 1 / homogeneousMode μ 1 * homogeneousMode μ s

/-- The mode solution vanishes at the wall. -/
theorem modeSolution_one (μ : ℝ) (F : ℝ → ℝ) : modeSolution μ F 1 = 0 := by
  have h := (one_pos.trans_le (one_le_homogeneousMode_one μ)).ne'
  simp only [modeSolution]
  field_simp
  ring

section Regularity

variable {μ : ℝ} {F : ℝ → ℝ}

/-- The open half-line `s > -4/μ²` on which the mode solution is regular. -/
theorem zero_mem_modeDomain (hμ : 0 < μ) : (0 : ℝ) ∈ Set.Ioi (-4 / μ ^ 2) := by
  simp only [Set.mem_Ioi]
  have : 0 < 4 / μ ^ 2 := by positivity
  rw [neg_div]
  linarith

/-- The segment from `0` to a point of the mode domain lies in the mode domain. -/
theorem uIcc_subset_modeDomain (hμ : 0 < μ) {s : ℝ} (hs : s ∈ Set.Ioi (-4 / μ ^ 2)) :
    Set.uIcc 0 s ⊆ Set.Ioi (-4 / μ ^ 2) :=
  (convex_Ioi _).ordConnected.uIcc_subset (zero_mem_modeDomain hμ) hs

/-- The quotient of reduction of order is smooth on the mode domain. -/
theorem contDiffOn_modeQuotient (hμ : 0 < μ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiffOn ℝ (⊤ : ℕ∞) (modeQuotient μ F) (Set.Ioi (-4 / μ ^ 2)) :=
  (contDiff_modeAverage μ hF).contDiffOn.div ((contDiff_homogeneousMode μ).pow 2).contDiffOn
    fun _ hs ↦ (pow_pos (homogeneousMode_pos hμ hs) 2).ne'

/-- The primitive of the quotient has derivative the quotient on the mode domain. -/
theorem hasDerivAt_integral_modeQuotient (hμ : 0 < μ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) {s : ℝ}
    (hs : s ∈ Set.Ioi (-4 / μ ^ 2)) :
    HasDerivAt (fun y ↦ ∫ σ in (0 : ℝ)..y, modeQuotient μ F σ) (modeQuotient μ F s) s := by
  have hW := (contDiffOn_modeQuotient hμ hF).continuousOn
  exact intervalIntegral.integral_hasDerivAt_right
    ((hW.mono (uIcc_subset_modeDomain hμ hs)).intervalIntegrable)
    (hW.stronglyMeasurableAtFilter isOpen_Ioi s hs)
    (hW.continuousAt (isOpen_Ioi.mem_nhds hs))

/-- The primitive of the quotient is smooth on the mode domain. -/
theorem contDiffOn_integral_modeQuotient (hμ : 0 < μ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y ↦ ∫ σ in (0 : ℝ)..y, modeQuotient μ F σ)
      (Set.Ioi (-4 / μ ^ 2)) := by
  rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun s hs ↦ (hasDerivAt_integral_modeQuotient hμ hF hs).differentiableAt
    |>.differentiableWithinAt, ?_⟩
  exact (contDiffOn_modeQuotient hμ hF).congr fun s hs ↦
    (hasDerivAt_integral_modeQuotient hμ hF hs).deriv

/-- The mode solution is smooth on the mode domain `s > -4/μ²`. -/
theorem contDiffOn_modeSolution (hμ : 0 < μ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiffOn ℝ (⊤ : ℕ∞) (modeSolution μ F) (Set.Ioi (-4 / μ ^ 2)) := by
  have hf := (contDiff_homogeneousMode μ).contDiffOn (s := Set.Ioi (-4 / μ ^ 2))
  have hP : ContDiffOn ℝ (⊤ : ℕ∞) (particularMode μ F) (Set.Ioi (-4 / μ ^ 2)) :=
    (contDiffOn_const.mul hf).mul (contDiffOn_integral_modeQuotient hμ hF)
  exact hP.sub (contDiffOn_const.mul hf)

/-- **The mode equation.** On the mode domain `s > -4/μ²` the mode solution solves
`4 s Ψ'' + 8 Ψ' - μ² Ψ = -F`. -/
theorem modeSolution_equation (hμ : 0 < μ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) {s : ℝ}
    (hs : -4 / μ ^ 2 < s) :
    4 * s * iteratedDeriv 2 (modeSolution μ F) s + 8 * deriv (modeSolution μ F) s -
      μ ^ 2 * modeSolution μ F s = -F s := by
  set U : Set ℝ := Set.Ioi (-4 / μ ^ 2)
  have hsU : s ∈ U := hs
  set f := homogeneousMode μ
  set f1 := homogeneousModeDeriv μ
  set f2 := homogeneousModeDeriv₂ μ
  set W := modeQuotient μ F
  set V : ℝ → ℝ := fun y ↦ ∫ σ in (0 : ℝ)..y, W σ
  set c : ℝ := particularMode μ F 1 / f 1
  set D1 : ℝ → ℝ := fun y ↦ -(1 / 4) * (f1 y * V y + f y * W y) - c * f1 y
  have hD1 : ∀ y ∈ U, HasDerivAt (modeSolution μ F) (D1 y) y := by
    intro y hy
    have h := (((hasDerivAt_homogeneousMode μ y).const_mul (-(1 / 4))).mul
      (hasDerivAt_integral_modeQuotient hμ hF hy)).sub
      ((hasDerivAt_homogeneousMode μ y).const_mul c)
    exact h.congr_deriv (by simp only [D1]; ring)
  have hWd : DifferentiableAt ℝ W s :=
    ((contDiffOn_modeQuotient hμ hF).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioi.mem_nhds hsU)
  have hD2 : HasDerivAt D1 (-(1 / 4) * (f2 s * V s + f1 s * W s + (f1 s * W s +
      f s * deriv W s)) - c * f2 s) s :=
    ((((hasDerivAt_homogeneousModeDeriv μ s).mul
      (hasDerivAt_integral_modeQuotient hμ hF hsU)).add
      ((hasDerivAt_homogeneousMode μ s).mul hWd.hasDerivAt)).const_mul (-(1 / 4))).sub
      ((hasDerivAt_homogeneousModeDeriv μ s).const_mul c)
  have hderiv : deriv (modeSolution μ F) s = D1 s := (hD1 s hsU).deriv
  have hderiv2 : iteratedDeriv 2 (modeSolution μ F) s = -(1 / 4) * (f2 s * V s + f1 s * W s +
      (f1 s * W s + f s * deriv W s)) - c * f2 s := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have hev : deriv (modeSolution μ F) =ᶠ[𝓝 s] D1 := by
      filter_upwards [isOpen_Ioi.mem_nhds hsU] with y hy
      exact (hD1 y hy).deriv
    rw [hev.deriv_eq]
    exact hD2.deriv
  -- The identity `s (f W' + 2 f₁ W) + 2 f W = F` from reduction of order.
  have hfpos := homogeneousMode_pos hμ hs
  have hBW : ∀ y ∈ U, modeAverage μ F y = W y * f y ^ 2 := by
    intro y hy
    have := (homogeneousMode_pos hμ hy).ne'
    simp only [W, modeQuotient, f]
    field_simp
  have hBderiv : deriv (modeAverage μ F) s = deriv W s * f s ^ 2 + W s * (2 * f s * f1 s) := by
    have h : HasDerivAt (fun y ↦ W y * f y ^ 2) (deriv W s * f s ^ 2 + W s * (2 * f s * f1 s))
        s := (hWd.hasDerivAt.mul ((hasDerivAt_homogeneousMode μ s).pow 2)).congr_deriv
      (by simp only [f, f1, Pi.pow_apply]; ring)
    have hev : (fun y ↦ W y * f y ^ 2) =ᶠ[𝓝 s] modeAverage μ F := by
      filter_upwards [isOpen_Ioi.mem_nhds hsU] with y hy
      exact (hBW y hy).symm
    exact (h.congr_of_eventuallyEq hev.symm).deriv
  have hI : s * (f s * deriv W s + 2 * f1 s * W s) + 2 * f s * W s = F s := by
    have hkey := modeAverage_identity μ hF s
    rw [hBderiv, hBW s hsU] at hkey
    have : f s * (s * (f s * deriv W s + 2 * f1 s * W s) + 2 * f s * W s) = f s * F s := by
      rw [← hkey]
      ring
    exact mul_left_cancel₀ hfpos.ne' this
  have hhom := homogeneousMode_equation μ s
  rw [hderiv2, hderiv]
  simp only [D1, modeSolution, particularMode]
  change 4 * s * (-(1 / 4) * (f2 s * V s + f1 s * W s + (f1 s * W s + f s * deriv W s)) -
      c * f2 s) + 8 * (-(1 / 4) * (f1 s * V s + f s * W s) - c * f1 s) -
      μ ^ 2 * (-(1 / 4) * f s * V s - c * f s) = -F s
  linear_combination (-(1 / 4) * V s - c) * hhom - hI

end Regularity

/-! ### Bounds for the mode solution -/

/-- At a maximum on `[a, b]` at the left endpoint, the derivative is nonpositive. -/
theorem deriv_nonpos_of_isMaxOn_Icc_left {f : ℝ → ℝ} {a b : ℝ} (hmax : IsMaxOn f (Set.Icc a b) a)
    (hab : a < b) (hf : DifferentiableAt ℝ f a) : deriv f a ≤ 0 := by
  have hmax' : IsMaxOn (fun x ↦ f (-x)) (Set.Icc (-b) (-a)) (-a) := by
    intro x hx
    have hx' : -x ∈ Set.Icc a b := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    simpa using hmax hx'
  have hd : DifferentiableAt ℝ (fun x ↦ f (-x)) (-a) := by
    have : DifferentiableAt ℝ f (-(-a)) := by simpa using hf
    exact this.comp (-a) differentiableAt_id.neg
  have := hmax'.deriv_nonneg_of_left_lt (by linarith) le_rfl hd
  rw [deriv_comp_neg, neg_neg] at this
  linarith

/-- **The maximum principle for the mode equation.** If `u` is `C²` near `[0, 1]`, solves
`4 s u'' + 8 u' - μ² u = -F` on `[0, 1]` (the axis `s = 0` included) with `u(1) = 0`, and
`F ≤ G` there with `G ≥ 0`, then `u ≤ G / μ²` on `[0, 1]`. -/
theorem le_of_modeEquation {μ G : ℝ} (hμ : 0 < μ) {u F : ℝ → ℝ}
    (hu : ∀ s ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 2 u s)
    (heq : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      4 * s * deriv (deriv u) s + 8 * deriv u s - μ ^ 2 * u s = -F s)
    (h1 : u 1 = 0) (hF : ∀ s ∈ Set.Icc (0 : ℝ) 1, F s ≤ G) (hG : 0 ≤ G) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, u s ≤ G / μ ^ 2 := by
  have hμ2 : 0 < μ ^ 2 := by positivity
  have hcont : ContinuousOn u (Set.Icc 0 1) := fun s hs ↦ (hu s hs).continuousAt.continuousWithinAt
  obtain ⟨p, hp, hpmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 zero_le_one) hcont
  intro s hs
  refine (hpmax hs).trans ?_
  by_contra! hlt
  have hGμ : 0 ≤ G / μ ^ 2 := div_nonneg hG hμ2.le
  have hp1 : p ≠ 1 := by
    rintro rfl
    linarith
  have hkey : μ ^ 2 * u p ≤ G := by
    have he := heq p hp
    have hdiff : DifferentiableAt ℝ u p := (hu p hp).differentiableAt (by norm_num)
    rcases hp.1.lt_or_eq with h0 | h0
    · have hpI : p ∈ Set.Ioo (0 : ℝ) 1 := ⟨h0, lt_of_le_of_ne hp.2 hp1⟩
      have hloc : IsLocalMax u p := by
        filter_upwards [Ioo_mem_nhds hpI.1 hpI.2] with y hy
        exact hpmax ⟨hy.1.le, hy.2.le⟩
      have hd1 : deriv u p = 0 := hloc.deriv_eq_zero
      have hd2 : deriv (deriv u) p ≤ 0 := hloc.deriv_deriv_nonpos (hu p hp).continuousAt
      have := hF p hp
      nlinarith
    · subst h0
      have hd1 : deriv u 0 ≤ 0 := deriv_nonpos_of_isMaxOn_Icc_left hpmax zero_lt_one hdiff
      have := hF 0 hp
      simp only [mul_zero, zero_mul, zero_add] at he
      linarith
  exact hlt.not_ge ((le_div_iff₀ hμ2).2 (by linarith))

section Bounds

variable {μ : ℝ} {F : ℝ → ℝ}

/-- The mode solution is smooth at every point of the mode domain. -/
theorem contDiffAt_modeSolution (hμ : 0 < μ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) {s : ℝ}
    (hs : -4 / μ ^ 2 < s) : ContDiffAt ℝ (⊤ : ℕ∞) (modeSolution μ F) s :=
  (contDiffOn_modeSolution hμ hF).contDiffAt (isOpen_Ioi.mem_nhds hs)

/-- The iterated derivatives of the mode solution are differentiable on the mode domain. -/
theorem differentiableAt_iteratedDeriv_modeSolution (hμ : 0 < μ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (m : ℕ) {s : ℝ} (hs : -4 / μ ^ 2 < s) :
    DifferentiableAt ℝ (iteratedDeriv m (modeSolution μ F)) s := by
  have h := (contDiffOn_infty.1 (contDiffOn_modeSolution hμ hF) (m + 1)
    ).differentiableOn_iteratedDerivWithin (m := m) (by exact_mod_cast Nat.lt_succ_self m)
    (isOpen_Ioi.uniqueDiffOn)
  have h' : DifferentiableOn ℝ (iteratedDeriv m (modeSolution μ F)) (Set.Ioi (-4 / μ ^ 2)) :=
    h.congr fun y hy ↦ (iteratedDerivWithin_of_isOpen isOpen_Ioi hy).symm
  exact h'.differentiableAt (isOpen_Ioi.mem_nhds hs)

/-- **The differentiated mode equation**
`4 s Ψ^{(m+2)} + (8 + 4m) Ψ^{(m+1)} - μ² Ψ^{(m)} = -F^{(m)}` on the mode domain. -/
theorem iteratedDeriv_modeSolution_equation (hμ : 0 < μ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (m : ℕ)
    {s : ℝ} (hs : -4 / μ ^ 2 < s) :
    4 * s * iteratedDeriv (m + 2) (modeSolution μ F) s +
        (8 + 4 * m) * iteratedDeriv (m + 1) (modeSolution μ F) s -
        μ ^ 2 * iteratedDeriv m (modeSolution μ F) s = -iteratedDeriv m F s := by
  induction m generalizing s with
  | zero =>
    have h := modeSolution_equation hμ hF hs
    simpa [iteratedDeriv_one] using h
  | succ m ih =>
    set D : ℕ → ℝ → ℝ := fun k ↦ iteratedDeriv k (modeSolution μ F)
    have hD : ∀ k, HasDerivAt (D k) (D (k + 1) s) s := by
      intro k
      have := (differentiableAt_iteratedDeriv_modeSolution hμ hF k hs).hasDerivAt
      simpa [D, iteratedDeriv_succ] using this
    have hL : HasDerivAt (fun y ↦ 4 * y * D (m + 2) y + (8 + 4 * m) * D (m + 1) y -
        μ ^ 2 * D m y) (4 * D (m + 2) s + 4 * s * D (m + 3) s + (8 + 4 * m) * D (m + 2) s -
        μ ^ 2 * D (m + 1) s) s := by
      have h := ((((hasDerivAt_id s).const_mul 4).mul (hD (m + 2))).add
        ((hD (m + 1)).const_mul (8 + 4 * (m : ℝ)))).sub ((hD m).const_mul (μ ^ 2))
      exact h.congr_deriv (by simp only [id]; ring)
    have hFd : HasDerivAt (fun y ↦ -iteratedDeriv m F y) (-iteratedDeriv (m + 1) F s) s := by
      have := (((contDiff_infty.1 hF (m + 1)).differentiable_iteratedDeriv m
        (by exact_mod_cast Nat.lt_succ_self m)) s).hasDerivAt.neg
      exact this.congr_deriv (by rw [iteratedDeriv_succ])
    have hev : (fun y ↦ 4 * y * D (m + 2) y + (8 + 4 * m) * D (m + 1) y - μ ^ 2 * D m y) =ᶠ[𝓝 s]
        fun y ↦ -iteratedDeriv m F y := by
      filter_upwards [isOpen_Ioi.mem_nhds (show s ∈ Set.Ioi (-4 / μ ^ 2) from hs)] with y hy
      exact ih hy
    have := (hL.congr_of_eventuallyEq hev.symm).unique hFd
    push_cast
    simp only [D] at this
    linarith

/-- The collar interval `[-2/μ², 1 + 2/μ²]` lies in the mode domain. -/
theorem modeInterval_subset (hμ : 0 < μ) :
    Set.Icc (-2 / μ ^ 2) (1 + 2 / μ ^ 2) ⊆ Set.Ioi (-4 / μ ^ 2) := by
  intro s hs
  have hμ2 : 0 < μ ^ 2 := by positivity
  have : -4 / μ ^ 2 < -2 / μ ^ 2 := div_lt_div_of_pos_right (by norm_num) hμ2
  exact this.trans_le hs.1

/-- The segment from `0` to a point of the collar interval lies in the collar interval. -/
theorem uIcc_subset_modeInterval (hμ : 0 < μ) {s : ℝ}
    (hs : s ∈ Set.Icc (-2 / μ ^ 2) (1 + 2 / μ ^ 2)) :
    Set.uIcc 0 s ⊆ Set.Icc (-2 / μ ^ 2) (1 + 2 / μ ^ 2) := by
  have h0 : (0 : ℝ) ∈ Set.Icc (-2 / μ ^ 2) (1 + 2 / μ ^ 2) := by
    have : 0 < 2 / μ ^ 2 := by positivity
    constructor
    · rw [neg_div]; linarith
    · linarith
  exact (convex_Icc _ _).ordConnected.uIcc_subset h0 hs

/-- **The derivative step.** If `|Ψ^{(m)}| ≤ K` and `|F^{(m)}| ≤ M` on the collar interval,
then `|Ψ^{(m+1)}| ≤ (μ² K + M) / 4` there. -/
theorem abs_iteratedDeriv_succ_modeSolution_le (hμ : 0 < μ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (m : ℕ) {K M : ℝ}
    (hK : ∀ s ∈ Set.Icc (-2 / μ ^ 2) (1 + 2 / μ ^ 2), |iteratedDeriv m (modeSolution μ F) s| ≤ K)
    (hM : ∀ s ∈ Set.Icc (-2 / μ ^ 2) (1 + 2 / μ ^ 2), |iteratedDeriv m F s| ≤ M)
    {s : ℝ} (hs : s ∈ Set.Icc (-2 / μ ^ 2) (1 + 2 / μ ^ 2)) :
    |iteratedDeriv (m + 1) (modeSolution μ F) s| ≤ (μ ^ 2 * K + M) / 4 := by
  set I := Set.Icc (-2 / μ ^ 2) (1 + 2 / μ ^ 2)
  set D : ℕ → ℝ → ℝ := fun k ↦ iteratedDeriv k (modeSolution μ F)
  have hseg := uIcc_subset_modeInterval hμ hs
  have h0I : (0 : ℝ) ∈ I := hseg Set.left_mem_uIcc
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 h0I)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 h0I)
  have hsum : 0 ≤ μ ^ 2 * K + M := by positivity
  -- the right-hand side `μ² Ψ^{(m)} - F^{(m)}` of the differentiated equation
  have hrhs : ∀ y ∈ I, |μ ^ 2 * D m y - iteratedDeriv m F y| ≤ μ ^ 2 * K + M := fun y hy ↦
    (abs_sub _ _).trans <| by
      rw [abs_mul, abs_of_pos (by positivity)]
      exact add_le_add (mul_le_mul_of_nonneg_left (hK y hy) (by positivity)) (hM y hy)
  rcases eq_or_ne s 0 with rfl | hs0
  · have he := iteratedDeriv_modeSolution_equation hμ hF m (modeInterval_subset hμ h0I)
    simp only [mul_zero, zero_mul, zero_add] at he
    have hpos : (0 : ℝ) < 8 + 4 * m := by positivity
    have h0 : D (m + 1) 0 = (μ ^ 2 * D m 0 - iteratedDeriv m F 0) / (8 + 4 * m) :=
      eq_div_of_mul_eq hpos.ne' (by simp only [D]; linarith)
    change |D (m + 1) 0| ≤ _
    rw [h0, abs_div, abs_of_pos hpos]
    exact div_le_div₀ hsum (hrhs 0 h0I) (by norm_num) (by linarith [m.cast_nonneg (α := ℝ)])
  -- the mean value theorem for `G(y) = y^{m+2} Ψ^{(m+1)}(y)` on the segment `[0, s]`
  have hG : ∀ y ∈ Set.uIcc 0 s, HasDerivWithinAt (fun y ↦ y ^ (m + 2) * D (m + 1) y)
      (y ^ (m + 1) / 4 * (μ ^ 2 * D m y - iteratedDeriv m F y)) (Set.uIcc 0 s) y := by
    intro y hy
    have hyU := modeInterval_subset hμ (hseg hy)
    have he := iteratedDeriv_modeSolution_equation hμ hF m hyU
    refine ((hasDerivAt_pow (m + 2) y).mul (differentiableAt_iteratedDeriv_modeSolution hμ hF
      (m + 1) hyU).hasDerivAt).hasDerivWithinAt.congr_deriv ?_
    simp only [D, ← iteratedDeriv_succ]
    rw [show m + 1 + 1 = m + 2 by ring, show m + 2 - 1 = m + 1 by omega]
    push_cast
    linear_combination (y ^ (m + 1) / 4) * he
  have hbound : ∀ y ∈ Set.uIcc 0 s, ‖y ^ (m + 1) / 4 * (μ ^ 2 * D m y - iteratedDeriv m F y)‖ ≤
      |s| ^ (m + 1) / 4 * (μ ^ 2 * K + M) := by
    intro y hy
    have hys : |y| ≤ |s| := by
      rcases Set.mem_uIcc.1 hy with h | h <;> exact abs_le.2
        ⟨by linarith [neg_abs_le s, abs_nonneg s], by linarith [le_abs_self s, abs_nonneg s]⟩
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    gcongr
    exact hrhs y (hseg hy)
  have h := (convex_uIcc 0 s).norm_image_sub_le_of_norm_hasDerivWithin_le hG hbound
    Set.left_mem_uIcc Set.right_mem_uIcc
  rw [zero_pow (by omega), zero_mul, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_mul, abs_pow] at h
  exact le_of_mul_le_mul_left (h.trans_eq (by ring)) (pow_pos (abs_pos.2 hs0) _)

/-- **The sup bound.** `|Ψ| ≤ 3 G / μ²` on the collar interval when `|F| ≤ G` there. -/
theorem abs_modeSolution_le (hμ : 0 < μ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) {G : ℝ}
    (hG : ∀ s ∈ Set.Icc (-2 / μ ^ 2) (1 + 2 / μ ^ 2), |F s| ≤ G)
    {s : ℝ} (hs : s ∈ Set.Icc (-2 / μ ^ 2) (1 + 2 / μ ^ 2)) :
    |modeSolution μ F s| ≤ 3 * G / μ ^ 2 := by
  set I := Set.Icc (-2 / μ ^ 2) (1 + 2 / μ ^ 2)
  set Ψ := modeSolution μ F
  have hμ2 : 0 < μ ^ 2 := by positivity
  have hδ : 0 < 2 / μ ^ 2 := by positivity
  have h01 : Set.Icc (0 : ℝ) 1 ⊆ I := Set.Icc_subset_Icc (by rw [neg_div]; linarith) (by linarith)
  have h0I : (0 : ℝ) ∈ I := h01 ⟨le_rfl, zero_le_one⟩
  have h1I : (1 : ℝ) ∈ I := h01 ⟨zero_le_one, le_rfl⟩
  have hG0 : 0 ≤ G := (abs_nonneg _).trans (hG 0 h0I)
  have hreg : ∀ y ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 2 Ψ y := fun y hy ↦
    (contDiffAt_modeSolution hμ hF (modeInterval_subset hμ (h01 hy))).of_le (by norm_num)
  have heq : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      4 * y * deriv (deriv Ψ) y + 8 * deriv Ψ y - μ ^ 2 * Ψ y = -F y := fun y hy ↦ by
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using
      modeSolution_equation hμ hF (modeInterval_subset hμ (h01 hy))
  -- the maximum principle for `Ψ` and `-Ψ` bounds `Ψ` on `[0, 1]`
  have hcore : ∀ y ∈ Set.Icc (0 : ℝ) 1, |Ψ y| ≤ G / μ ^ 2 := by
    intro y hy
    have hdn := le_of_modeEquation (u := -Ψ) (F := -F) hμ (fun y hy ↦ (hreg y hy).neg)
      (fun y hy ↦ by
        rw [deriv.neg', show (fun x ↦ -deriv Ψ x) = -deriv Ψ from rfl, deriv.neg]
        simp only [Pi.neg_apply]
        linarith [heq y hy])
      (by simp [Ψ, modeSolution_one]) (fun y hy ↦ (neg_le_abs _).trans (by
        simpa using hG y (h01 hy))) hG0 y hy
    simp only [Pi.neg_apply] at hdn
    exact abs_le.2 ⟨by linarith, le_of_modeEquation hμ hreg heq (modeSolution_one μ F)
      (fun y hy ↦ (le_abs_self _).trans (hG y (h01 hy))) hG0 y hy⟩
  -- `|Ψ|` attains its maximum on the collar interval at `p`
  obtain ⟨p, hp, hpmax⟩ := isCompact_Icc.exists_isMaxOn ⟨s, hs⟩ fun y hy ↦
    ((contDiffAt_modeSolution hμ hF (modeInterval_subset hμ hy)).continuousAt.abs
      ).continuousWithinAt
  have hA : ∀ y ∈ I, |Ψ y| ≤ |Ψ p| := fun y hy ↦ hpmax hy
  have hderiv : ∀ y ∈ I, |deriv Ψ y| ≤ (μ ^ 2 * |Ψ p| + G) / 4 := fun y hy ↦ by
    simpa [iteratedDeriv_one] using abs_iteratedDeriv_succ_modeSolution_le hμ hF 0
      (K := |Ψ p|) (M := G) (fun y hy ↦ by rw [iteratedDeriv_zero]; exact hA y hy)
      (fun y hy ↦ by rw [iteratedDeriv_zero]; exact hG y hy) hy
  -- the mean value theorem across a collar of length `2/μ²`
  have hcollar : ∀ a ∈ I, ∀ b ∈ I, |b - a| ≤ 2 / μ ^ 2 →
      |Ψ b - Ψ a| ≤ |Ψ p| / 2 + G / μ ^ 2 / 2 := fun a ha b hb hab ↦
    ((convex_Icc _ _).norm_image_sub_le_of_norm_deriv_le (fun y hy ↦
      (contDiffAt_modeSolution hμ hF (modeInterval_subset hμ hy)).differentiableAt (by simp))
      hderiv ha hb).trans <| (mul_le_mul_of_nonneg_left hab
        (div_nonneg (add_nonneg (by positivity) hG0) (by norm_num))).trans_eq (by field_simp; ring)
  have hGμ : 0 ≤ G / μ ^ 2 := div_nonneg hG0 hμ2.le
  rw [mul_div_assoc]
  refine (hA s hs).trans ?_
  rcases lt_or_ge p 0 with hp0 | hp0
  · have h1 := hcollar p hp 0 h0I (by
      rw [zero_sub, abs_neg, abs_of_neg hp0]; linarith [hp.1, neg_div (μ ^ 2) (2 : ℝ)])
    linarith [abs_sub_abs_le_abs_sub (Ψ p) (Ψ 0), abs_sub_comm (Ψ p) (Ψ 0),
      hcore 0 ⟨le_rfl, zero_le_one⟩]
  rcases le_or_gt p 1 with hp1 | hp1
  · linarith [hcore p ⟨hp0, hp1⟩]
  have h1 := hcollar 1 h1I p hp (by rw [abs_of_pos (by linarith)]; linarith [hp.2])
  rw [show Ψ 1 = 0 from modeSolution_one μ F, sub_zero] at h1
  linarith

/-- **Polynomial bounds for the derivatives of the mode solution.** If `|F^{(j)}| ≤ M j` on
the collar interval `[-2/μ², 1 + 2/μ²]` for `j ≤ m`, then there
`|Ψ^{(m)}| ≤ 3 (1 + μ²)^m (M 0 + ⋯ + M m) / μ²`. -/
theorem abs_iteratedDeriv_modeSolution_le (hμ : 0 < μ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (m : ℕ)
    (M : ℕ → ℝ)
    (hM : ∀ j ≤ m, ∀ s ∈ Set.Icc (-2 / μ ^ 2) (1 + 2 / μ ^ 2), |iteratedDeriv j F s| ≤ M j)
    {s : ℝ} (hs : s ∈ Set.Icc (-2 / μ ^ 2) (1 + 2 / μ ^ 2)) :
    |iteratedDeriv m (modeSolution μ F) s| ≤
      3 * (1 + μ ^ 2) ^ m * (∑ j ∈ Finset.range (m + 1), M j) / μ ^ 2 := by
  have hμ2 : 0 < μ ^ 2 := by positivity
  have hM0 : ∀ j ≤ m, 0 ≤ M j := fun j hj ↦ (abs_nonneg _).trans (hM j hj s hs)
  have key : ∀ k ≤ m, ∀ y ∈ Set.Icc (-2 / μ ^ 2) (1 + 2 / μ ^ 2),
      |iteratedDeriv k (modeSolution μ F) y| ≤
        3 * (1 + μ ^ 2) ^ k * (∑ j ∈ Finset.range (k + 1), M j) / μ ^ 2 := by
    intro k
    induction k with
    | zero =>
      intro _ y hy
      simpa using abs_modeSolution_le hμ hF (G := M 0) (fun y hy ↦ by
        simpa using hM 0 (Nat.zero_le _) y hy) hy
    | succ k ih =>
      intro hk y hy
      have hk' : k ≤ m := Nat.le_of_succ_le hk
      set P := (1 + μ ^ 2) ^ k with hPdef
      set S := ∑ j ∈ Finset.range (k + 1), M j with hSdef
      have hrange : ∀ j ∈ Finset.range (k + 1), 0 ≤ M j := fun j hj ↦
        hM0 j (by have := Finset.mem_range.1 hj; omega)
      have hS : 0 ≤ S := Finset.sum_nonneg hrange
      have hP : 1 ≤ P := one_le_pow₀ (by linarith)
      have hPS : S ≤ P * S := le_mul_of_one_le_left hS hP
      have hMk : M k ≤ S := Finset.single_le_sum hrange (Finset.self_mem_range_succ k)
      refine (abs_iteratedDeriv_succ_modeSolution_le hμ hF k (ih hk') (hM k hk') hy).trans ?_
      rw [Finset.sum_range_succ, ← hSdef, pow_succ (1 + μ ^ 2) k, ← hPdef,
        show μ ^ 2 * (3 * P * S / μ ^ 2) = 3 * P * S by field_simp, le_div_iff₀ hμ2]
      -- `M k ≤ S ≤ P S`, so the left side is at most `P S μ²`
      have hM' := mul_nonneg (zero_le_one.trans hP) (hM0 (k + 1) hk)
      linarith [mul_le_mul_of_nonneg_right (hMk.trans hPS) hμ2.le, hS.trans hPS,
        mul_nonneg (hS.trans hPS) hμ2.le, mul_nonneg hM' hμ2.le]
  exact key m le_rfl s hs

end Bounds

end

end Euler.Cylinder
