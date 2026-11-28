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

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Separation.CompletelyRegular
public import PDE.Analysis.MeasureTheory.AlmostEverywhere

set_option linter.style.header false

/-!
# Integrals over intervals of the real line

The lemmas state interval integrability, split an interval integral at a point or over a sum,
integrate by parts, substitute, and evaluate integrals of powers and exponentials. The proofs use
the fundamental theorem of calculus as Mathlib states it
(`intervalIntegral.integral_eq_sub_of_hasDerivAt`) and
`intervalIntegral.integral_add_adjacent_intervals`.

## Main results

* `PDE.Analysis.integral_eq_integral_Ioo_of_periodic`: For a complex function `f : ℝ → ℂ` that is
  periodic with period `2 * π`, `∫ θ in 0..2 * π, f θ = ∫ θ in Ioo (-π) π, f θ`.
* `PDE.Analysis.intervalIntegrable_mul_of_memLp_two`: If `g h : ℝ → ℝ` both satisfy
  `MemLp _ 2 (volume.restrict (Ioc 0 (2 * π)))`, then the product `θ ↦ g θ * h θ` is interval
  integrable between `0` and `2 * π`.
* `PDE.Analysis.integral_cexp_mul_deriv_param_eq_zero`: Let `s` be a neighbourhood of `x₀` and let
  `F`, `F' : ℝ → ℝ → ℝ` be such that, for `x ∈ s` and all `t`, `F x` is continuous, `|F' x t| ≤ C`
  and `fun x ↦ F x t` has derivative `F' x t` at `x`, with `F' x₀` continuous. If
  `∫ t in 0..2 * π, Complex.exp (-(k * t) * Complex.I) * F x t = 0` for all `x ∈ s`, where `k` is
  real, then `∫ t in 0..2 * π, Complex.exp (-(k * t) * Complex.I) * F' x₀ t = 0`.
* `PDE.Analysis.integral_mul_re_eq_re_integral`: Let `f : ℝ → ℝ` be interval integrable on
  `0..2 * π` and `w : ℝ → ℂ` continuous. Then
  `∫ θ in 0..2 * π, f θ * (w θ).re = (∫ θ in 0..2 * π, (f θ : ℂ) * w θ).re`.
* `PDE.Analysis.integral_ofReal_mul_cexp_eq_conj`: For arbitrary functions `f`, `t : ℝ → ℝ`,
  `∫ θ in 0..2 * π, (f θ : ℂ) * Complex.exp (t θ * Complex.I)` equals the complex conjugate of
  `∫ θ in 0..2 * π, Complex.exp (-(t θ) * Complex.I) * (f θ : ℂ)`.
* `PDE.Analysis.integral_sub_rpow`: For `γ < 1` and all real `t₀`, `t`,
  `∫ s in t₀..t, (t - s) ^ (-γ) = (t - t₀) ^ (-γ + 1) / (-γ + 1)`.
* `PDE.Analysis.intervalIntegrable_finsetSum_real`: Let `s` be a finite set of indices and let
  `f i : ℝ → ℝ` be interval integrable on `a..b` for each `i ∈ s`. Then the pointwise sum
  `fun x ↦ ∑ i ∈ s, f i x` is interval integrable on `a..b`.
* `PDE.Analysis.intervalIntegrable_sub_rpow`: For `γ < 1` and all real `t₀`, `t`, the function
  `fun s ↦ (t - s) ^ (-γ)` is interval integrable on `t₀..t` with respect to Lebesgue measure.

There are 80 further lemmas of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Real Filter Topology Polynomial

namespace PDE.Analysis

/-- Let `Y`, `Z : ℝ → ℂ` be interval integrable on `0..2 * π`, let `c d : ℂ`, and let
`X θ = c * Y θ + d * Z θ` for all `θ`. Then the averages over `0..2 * π` satisfy the same relation:
`(1 / (2 * π)) * ∫ θ in 0..2 * π, X θ = c * ((1 / (2 * π)) * ∫ θ in 0..2 * π, Y θ) + d * ((1 / (2 *
π)) * ∫ θ in 0..2 * π, Z θ)`. -/
theorem average_two_pi_mul_add_mul {X Y Z : ℝ → ℂ}
    (hY : IntervalIntegrable Y volume 0 (2 * Real.pi))
    (hZ : IntervalIntegrable Z volume 0 (2 * Real.pi)) (c d : ℂ)
        (h : ∀ θ, X θ = c * Y θ + d * Z θ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), X θ =
      c * ((1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), Y θ) +
        d * ((1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), Z θ) := by
  rw [intervalIntegral.integral_congr (fun θ _ ↦ h θ),
    intervalIntegral.integral_add (hY.const_mul c) (hZ.const_mul d),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

/-- For an integer `m`, the integral of `t ↦ Complex.exp (-(2 * π * Complex.I * (m * t)))` over
`Set.Icc (0 : ℝ) 1` equals `1` if `m = 0` and `0` otherwise. For `m ≠ 0` the exponential has an
explicit primitive, which takes the same value at `0` and at `1`. -/
theorem integral_Icc_cexp_neg_int_mul (m : ℤ) :
    ∫ t in Icc (0 : ℝ) 1, Complex.exp (-(2 * π * Complex.I * (((m : ℝ) * t : ℝ) : ℂ))) =
      if m = 0 then 1 else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  split_ifs with hm
  · subst hm
    simp
  · have hc : (-(2 * π * Complex.I * (m : ℂ)) : ℂ) ≠ 0 := by
      simp [hm, Real.pi_ne_zero, Complex.I_ne_zero]
    have e : ∀ t : ℝ, Complex.exp (-(2 * π * Complex.I * (((m : ℝ) * t : ℝ) : ℂ))) =
        Complex.exp ((-(2 * π * Complex.I * (m : ℂ))) * t) := by
      intro t
      push_cast
      ring_nf
    simp_rw [e]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp ((-(2 * π * Complex.I * (m : ℂ))) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [Complex.ofReal_one, mul_one,
        show -(2 * ↑π * Complex.I * (m : ℂ)) = ((-m : ℤ) : ℂ) * (2 * π * Complex.I) by
          push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I (-m)
    rw [h1]
    simp

/-- For a real `a`, a natural number `L` and an integer `m`, the integral of
`t ↦ Complex.exp (2 * π * Complex.I * (m * t))` over `Set.Icc a (a + L)` equals `L` if `m = 0` and
`0` otherwise. For `m ≠ 0` the exponential has an explicit primitive, which takes the same value at
`a` and at `a + L` because `m * L` is an integer. -/
theorem integral_Icc_cexp_two_pi_int_mul (a : ℝ) (L : ℕ) (m : ℤ) :
    ∫ t in Icc a (a + L), Complex.exp (2 * π * Complex.I * (((m : ℝ) * t : ℝ) : ℂ)) =
      if m = 0 then (L : ℂ) else 0 := by
  have hL : a ≤ a + L := by linarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL]
  split_ifs with hm
  · subst hm
    simp
  · have hc : (2 * π * Complex.I * m) ≠ 0 := by simp [hm, pi_ne_zero]
    have h : ∀ t : ℝ, Complex.exp (2 * π * Complex.I * (((m : ℝ) * t : ℝ) : ℂ)) =
        Complex.exp ((2 * π * Complex.I * m) * t) := by
      intro t
      push_cast
      ring_nf
    simp_rw [h]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * π * Complex.I * m * ((a + L : ℝ) : ℂ)) =
        Complex.exp (2 * π * Complex.I * m * a) := by
      have h2 : 2 * π * Complex.I * m * ((a + L : ℝ) : ℂ) =
          2 * π * Complex.I * m * a + ((m * L : ℤ) : ℂ) * (2 * π * Complex.I) := by
        push_cast
        ring
      rw [h2, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [h1, sub_self, zero_div]

/-- If `g : ℝ → ℝ` is of class `C¹` and `g 1 = g 0`, then `∫ σ in Icc 0 1, deriv g σ * g σ = 0`. The
integrand is the derivative of `s ↦ g s * g s / 2`, so by the fundamental theorem of calculus the
integral is `g 1 * g 1 / 2 - g 0 * g 0 / 2`, which is zero. -/
theorem integral_Icc_deriv_mul_self_eq_zero (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (hp : g 1 = g 0) :
    ∫ σ in Set.Icc (0 : ℝ) 1, deriv g σ * g σ = 0 := by
  have hd : Differentiable ℝ g := hg.differentiable (by norm_num)
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  have hder : ∀ σ ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s ↦ g s * g s / 2) (deriv g σ * g σ) σ := by
    intro σ _
    have h := ((hd σ).hasDerivAt.mul (hd σ).hasDerivAt).div_const 2
    have e : deriv g σ * g σ = (deriv g σ * g σ + g σ * deriv g σ) / 2 := by ring
    rw [e]
    exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    (((hg.continuous_deriv (by norm_num)).mul hg.continuous).intervalIntegrable _ _)]
  simp [hp]

/-- If `u : ℝ → ℂ` has derivative `du x` at every real `x`, `du` is continuous and `a ≤ b`, then
`∫ x in Icc a b, du x = u b - u a`. -/
theorem integral_Icc_eq_sub_of_hasDerivAt {u du : ℝ → ℂ} (hdu : Continuous du)
    (hu : ∀ x, HasDerivAt u (du x) x) {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Icc a b, du x = u b - u a := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hu x)
      (hdu.intervalIntegrable a b)

open scoped ContDiff in
/-- For a smooth (`ContDiff ℝ ∞`) function `θ : ℝ → ℝ` with compact support and every real `τ`,
`∫ t in Set.Ici τ, deriv θ t = -θ τ`. This is the fundamental theorem of calculus on `Set.Ioi τ`,
using that `θ` tends to `0` at infinity. -/
theorem integral_Ici_deriv_of_hasCompactSupport {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hθc : HasCompactSupport θ)
    (τ : ℝ) : ∫ t in Ici τ, deriv θ t = -θ τ := by
  rw [integral_Ici_eq_integral_Ioi]
  have hd : ∀ x, HasDerivAt θ (deriv θ x) x := fun x ↦
    ((hθ.differentiable (by simp)) x).hasDerivAt
  have hi : Integrable (deriv θ) :=
    (hθ.continuous_deriv (by simp)).integrable_of_hasCompactSupport hθc.deriv
  have ht : Tendsto θ atTop (𝓝 0) := hθc.is_zero_at_infty.mono_left atTop_le_cocompact
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hθ.continuous.continuousWithinAt
    (fun x _ ↦ hd x) hi.integrableOn ht]
  ring

open intervalIntegral in
/-- For `-1 < a` and `0 ≤ T`, the function `fun τ : ℝ ↦ τ ^ a` is integrable on `Ioc 0 T` and
`∫ τ in Ioc 0 T, τ ^ a = T ^ (a + 1) / (a + 1)`. -/
theorem integral_Ioc_rpow {a T : ℝ} (ha : -1 < a) (hT : 0 ≤ T) :
    IntegrableOn (fun τ : ℝ ↦ τ ^ a) (Ioc 0 T) ∧
      ∫ τ in Ioc 0 T, τ ^ a = T ^ (a + 1) / (a + 1) := by
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 (intervalIntegrable_rpow' ha), ?_⟩
  rw [← intervalIntegral.integral_of_le hT, integral_rpow (Or.inl ha),
    Real.zero_rpow (by linarith), sub_zero]

/-- For `0 < R`, `∫ τ in Ioc 0 (R ^ 2), τ ^ (-(1 / 2 : ℝ)) = 2 * R`. -/
theorem integral_Ioc_rpow_neg_half {R : ℝ} (hR : 0 < R) :
    ∫ τ in Ioc 0 (R ^ 2), τ ^ (-(1 / 2 : ℝ)) = 2 * R := by
  rw [← intervalIntegral.integral_of_le (by positivity), integral_rpow (Or.inl (by norm_num)),
    Real.zero_rpow (by norm_num),
    show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, Real.sqrt_sq hR.le]
  ring

/-- For `0 < R`, `∫ τ in Ioi (R ^ 2), τ ^ (-(5 / 2 : ℝ)) = 2 / 3 * (R ^ 3)⁻¹`. -/
theorem integral_Ioi_rpow_neg_five_half {R : ℝ} (hR : 0 < R) :
    ∫ τ in Ioi (R ^ 2), τ ^ (-(5 / 2 : ℝ)) = 2 / 3 * (R ^ 3)⁻¹ := by
  rw [integral_Ioi_rpow_of_lt (by norm_num) (by positivity), ← Real.rpow_two,
    ← Real.rpow_mul hR.le, show (2 : ℝ) * (-(5 / 2 : ℝ) + 1) = -((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg hR.le, Real.rpow_natCast]
  ring

/-- For `0 < m`, `0 < ρ` and `2 < e`,
`∫ s in 0..1, (m + s * ρ) ^ (1 - e) ≤ ρ⁻¹ * (m ^ (2 - e) / (e - 2))`. The proof substitutes
`u = ρ * s + m`, integrates the power exactly, and drops the nonnegative term `(ρ + m) ^ (2 - e)`.
-/
theorem integral_add_mul_rpow_le {m ρ e : ℝ} (hm : 0 < m) (hρ : 0 < ρ) (he : 2 < e) :
    ∫ s in (0 : ℝ)..1, (m + s * ρ) ^ (1 - e) ≤ ρ⁻¹ * (m ^ (2 - e) / (e - 2)) := by
  have hfun : (fun s : ℝ ↦ (m + s * ρ) ^ (1 - e)) = fun s ↦
      (fun u : ℝ ↦ u ^ (1 - e)) (ρ * s + m) := by
    funext s
    simp only
    rw [show m + s * ρ = ρ * s + m by ring]
  rw [hfun, intervalIntegral.integral_comp_mul_add (fun u : ℝ ↦ u ^ (1 - e)) hρ.ne' m,
    mul_zero, zero_add, mul_one]
  have h0 : (0 : ℝ) ∉ uIcc m (ρ + m) := by
    rw [mem_uIcc]
    rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> linarith
  rw [integral_rpow (Or.inr ⟨by linarith, h0⟩), show 1 - e + 1 = 2 - e by ring, smul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hρ.le)
  have hp : 0 ≤ (ρ + m) ^ (2 - e) := rpow_nonneg (by linarith) _
  rw [show (2 - e) = -(e - 2) by ring, div_neg, ← neg_div]
  rw [← show (2 - e) = -(e - 2) by ring]
  exact (div_le_div_iff_of_pos_right (by linarith)).2 (by linarith)

/-- For a nonzero integer `m`, `∫ θ in (-π)..π, Complex.exp (m * θ * Complex.I) = 0`. The proof
integrates the exponential explicitly and uses that `Complex.exp (m * (2 * π * Complex.I)) = 1`. -/
theorem integral_cexp_int_mul_neg_pi_pi (m : ℤ) (hm : m ≠ 0) :
    ∫ θ in (-Real.pi)..Real.pi, Complex.exp ((m : ℂ) * (θ : ℂ) * Complex.I) = 0 := by
  have hc : (m : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hm) Complex.I_ne_zero
  have hfun : (fun θ : ℝ ↦ Complex.exp ((m : ℂ) * (θ : ℂ) * Complex.I)) =
      fun θ : ℝ ↦ Complex.exp ((m : ℂ) * Complex.I * (θ : ℂ)) := by
    funext θ
    ring_nf
  rw [hfun, integral_exp_mul_complex hc]
  have h2 : Complex.exp ((m : ℂ) * Complex.I * ((Real.pi : ℝ) : ℂ)) =
      Complex.exp ((m : ℂ) * Complex.I * ((-Real.pi : ℝ) : ℂ)) := by
    have hsplit : (m : ℂ) * Complex.I * ((Real.pi : ℝ) : ℂ) =
        (m : ℂ) * Complex.I * ((-Real.pi : ℝ) : ℂ) + (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [h2, sub_self, zero_div]

/-- For a nonzero integer `j`, `∫ x in 0..2 * π, Complex.exp (j * Complex.I * x) = 0`. The proof
integrates the exponential explicitly and uses that `Complex.exp (j * (2 * π * Complex.I)) = 1`. -/
theorem integral_cexp_int_mul_zero_two_pi (j : ℤ) (hj : j ≠ 0) :
    ∫ x in (0 : ℝ)..(2 * Real.pi), Complex.exp ((j : ℂ) * Complex.I * (x : ℂ)) = 0 := by
  have hc : (j : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hj) Complex.I_ne_zero
  rw [integral_exp_mul_complex hc]
  have h1 : Complex.exp ((j : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
    rw [show (j : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ) = j * (2 * Real.pi * Complex.I) by
      push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I j
  rw [h1]
  simp

/-- Let `s` be a neighbourhood of `x₀` and let `F`, `F' : ℝ → ℝ → ℝ` be such that, for `x ∈ s` and
all `t`, `F x` is continuous, `|F' x t| ≤ C` and `fun x ↦ F x t` has derivative `F' x t` at `x`,
with `F' x₀` continuous. If `∫ t in 0..2 * π, Complex.exp (-(k * t) * Complex.I) * F x t = 0` for
all `x ∈ s`, where `k` is real, then
`∫ t in 0..2 * π, Complex.exp (-(k * t) * Complex.I) * F' x₀ t = 0`. The proof differentiates under
the integral sign at `x₀` and compares with the derivative of the zero function. -/
theorem integral_cexp_mul_deriv_param_eq_zero {F F' : ℝ → ℝ → ℝ} {x₀ C k : ℝ} {s : Set ℝ}
    (hs : s ∈ 𝓝 x₀)
    (hFc : ∀ x ∈ s, Continuous (F x)) (hF'c : Continuous (F' x₀)) (hb : ∀ x ∈ s, ∀ t, |F' x t| ≤ C)
    (hd : ∀ x ∈ s, ∀ t, HasDerivAt (fun x ↦ F x t) (F' x t) x)
    (hz : ∀ x ∈ s, ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(k * t : ℝ) * Complex.I) *
        (F x t : ℂ) = 0) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(k * t : ℝ) * Complex.I) * (F' x₀ t : ℂ) = 0 := by
  have hec : Continuous (fun t : ℝ ↦ Complex.exp (-(k * t : ℝ) * Complex.I)) := by fun_prop
  have hnorm : ∀ t : ℝ, ‖Complex.exp (-(k * t : ℝ) * Complex.I)‖ = 1 := fun t ↦ by
    rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := 0) (b := 2 * Real.pi) (bound := fun _ ↦ C)
    (F := fun x t ↦ Complex.exp (-(k * t : ℝ) * Complex.I) * (F x t : ℂ))
    (F' := fun x t ↦ Complex.exp (-(k * t : ℝ) * Complex.I) * (F' x t : ℂ)) hs
    (Filter.eventually_of_mem hs fun x hx ↦
      (hec.mul (Complex.continuous_ofReal.comp (hFc x hx))).aestronglyMeasurable)
    ((hec.mul (Complex.continuous_ofReal.comp (hFc x₀ (mem_of_mem_nhds hs)))).intervalIntegrable _
        _)
    ((hec.mul (Complex.continuous_ofReal.comp hF'c)).aestronglyMeasurable)
    (ae_of_all _ fun t _ x hx ↦ by
      rw [norm_mul, hnorm, one_mul, Complex.norm_real, Real.norm_eq_abs]; exact hb x hx t)
    intervalIntegrable_const
    (ae_of_all _ fun t _ x hx ↦ ((hd x hx t).ofReal_comp).const_mul _)
  have h0 : HasDerivAt (fun x ↦ ∫ t in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(k * t : ℝ) * Complex.I) * (F x t : ℂ)) 0 x₀ :=
    (hasDerivAt_const x₀ (0 : ℂ)).congr_of_eventuallyEq
        (Filter.eventually_of_mem hs fun x hx ↦ hz x hx)
  exact key.2.unique h0

/-- For `0 < a`, `∫ s in (0 : ℝ)..1, s / (1 + a * s) ^ 3 ≤ 1 / a ^ 2`. The integrand is bounded by
`1 / (a * (1 + a * s) ^ 2)`, which has the primitive `-1 / (a ^ 2 * (1 + a * s))`. -/
theorem integral_div_one_add_mul_cube_le {a : ℝ} (ha : 0 < a) :
    ∫ s in (0 : ℝ)..1, s / (1 + a * s) ^ 3 ≤ 1 / a ^ 2 := by
  have hpos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < 1 + a * s := fun s hs ↦ by nlinarith [hs.1]
  have hcont1 : ContinuousOn (fun s : ℝ ↦ s / (1 + a * s) ^ 3) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact continuousOn_id.div (by fun_prop) (fun s hs ↦ (pow_pos (hpos s hs) 3).ne')
  have hcont2 : ContinuousOn (fun s : ℝ ↦ 1 / (a * (1 + a * s) ^ 2)) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact continuousOn_const.div (by fun_prop)
      (fun s hs ↦ (mul_pos ha (pow_pos (hpos s hs) 2)).ne')
  have hmono := intervalIntegral.integral_mono_on zero_le_one
      (hcont1.intervalIntegrable (μ := MeasureTheory.volume))
    (hcont2.intervalIntegrable (μ := MeasureTheory.volume)) (fun s hs ↦ by
      have h1 := hpos s hs
      rw [div_le_div_iff₀ (pow_pos h1 3) (mul_pos ha (pow_pos h1 2))]
      nlinarith [sq_nonneg (1 + a * s)])
  have hF : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s ↦ -1 / (a ^ 2 * (1 + a * s)))
      (1 / (a * (1 + a * s) ^ 2)) s := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    have h1 := hpos s hs
    have hd : HasDerivAt (fun s ↦ a ^ 2 * (1 + a * s)) (a ^ 2 * (a * 1)) s :=
      (((hasDerivAt_id' s).const_mul a).const_add 1).const_mul (a ^ 2)
    have hq := (hasDerivAt_const s (-1 : ℝ)).div hd (mul_pos (pow_pos ha 2) h1).ne'
    refine hq.congr_deriv ?_
    rw [div_eq_div_iff (pow_pos (mul_pos (pow_pos ha 2) h1) 2).ne' (mul_pos ha (pow_pos h1 2)).ne']
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
      (hcont2.intervalIntegrable (μ := MeasureTheory.volume))] at hmono
  simp only [mul_one, mul_zero, add_zero] at hmono
  have h2 : 0 ≤ 1 / (a ^ 2 * (1 + a)) := by positivity
  have e : -1 / (a ^ 2 * (1 + a)) - -1 / a ^ 2 = 1 / a ^ 2 - 1 / (a ^ 2 * (1 + a)) := by ring
  linarith

/-- For a complex function `f : ℝ → ℂ` that is periodic with period `2 * π`,
`∫ θ in 0..2 * π, f θ = ∫ θ in Ioo (-π) π, f θ`. -/
theorem integral_eq_integral_Ioo_of_periodic (f : ℝ → ℂ) (hf : Function.Periodic f (2 * π)) :
    ∫ θ in (0 : ℝ)..(2 * π), f θ = ∫ θ in Ioo (-π) π, f θ := by
  have h := hf.intervalIntegral_add_eq 0 (-π)
  rw [zero_add, show -π + 2 * π = π by ring] at h
  rw [h, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]

/-- For a real function `f : ℝ → ℝ` that is periodic with period `2 * π`,
`∫ θ in 0..2 * π, f θ = ∫ θ in Ioo (-π) π, f θ`. -/
theorem integral_eq_integral_Ioo_of_periodic_real (f : ℝ → ℝ) (hf : Function.Periodic f (2 * π)) :
    ∫ θ in (0 : ℝ)..(2 * π), f θ = ∫ θ in Ioo (-π) π, f θ := by
  have h := hf.intervalIntegral_add_eq 0 (-π)
  rw [zero_add, show -π + 2 * π = π by ring] at h
  rw [h, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]

/-- If `g : ℝ → ℂ` is periodic with period `2 * π`, then
`∫ θ in 0..2 * π, g θ = ∫ θ in Ioc (-π) π, g θ`. -/
theorem integral_eq_setIntegral_Ioc_of_periodic (g : ℝ → ℂ)
    (hg : Function.Periodic g (2 * Real.pi)) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), g θ = ∫ θ in Set.Ioc (-Real.pi) Real.pi, g θ := by
  have h := hg.intervalIntegral_add_eq 0 (-Real.pi)
  rw [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring] at h
  rw [h, intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]

/-- Integration by parts on `0..1` for real polynomials `a` and `b`:
`∫ x in 0..1, b.eval x * (derivative a).eval x = b.eval 1 * a.eval 1 - b.eval 0 * a.eval 0 - ∫ x in
0..1, (derivative b).eval x * a.eval x`. -/
theorem integral_eval_mul_eval_derivative (a b : ℝ[X]) :
    ∫ x in (0 : ℝ)..1, b.eval x * (derivative a).eval x
      = b.eval 1 * a.eval 1 - b.eval 0 * a.eval 0
        - ∫ x in (0 : ℝ)..1, (derivative b).eval x * a.eval x :=
  intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun x _ ↦ b.hasDerivAt x)
    (fun x _ ↦ a.hasDerivAt x) ((derivative b).continuous.intervalIntegrable _ _)
    ((derivative a).continuous.intervalIntegrable _ _)

/-- If `ω * L = 2 * π * k` for an integer `k`, then
`∫ t in 0..L, Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I)` equals `L` when `ω = 0` and `0`
otherwise. For `ω ≠ 0` the proof evaluates the integral with the primitive of the exponential and
uses `Complex.exp (ω * Complex.I * L) = 1`. -/
theorem integral_exp_full_period (ω L : ℝ) (k : ℤ) (h : ω * L = 2 * Real.pi * k) :
    ∫ t in (0 : ℝ)..L, Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I) = if ω = 0 then (L : ℂ) else
        0 := by
  split_ifs with hω
  · subst hω
    simp
  · have hc : (ω : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hω) Complex.I_ne_zero
    have e : ∀ t : ℝ, Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((ω : ℂ) * Complex.I) * (t : ℂ)) := by
      intro t
      congr 1
      push_cast
      ring
    simp_rw [e]
    rw [integral_exp_mul_complex hc]
    have hL : (ω : ℂ) * (L : ℂ) = 2 * (Real.pi : ℂ) * (k : ℂ) := by exact_mod_cast h
    have h1 : Complex.exp (((ω : ℂ) * Complex.I) * (L : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I k]
      congr 1
      linear_combination Complex.I * hL
    simp [h1]

/-- If `a ≠ 0` and `a * L = 2 * π * k` for an integer `k`, then
`∫ x in 0..L, Complex.exp (((a * x : ℝ) : ℂ) * Complex.I) = 0`. The proof evaluates the integral
with the primitive of the exponential and uses that `Complex.exp` of an integer multiple of
`2 * π * Complex.I` is `1`. -/
theorem integral_exp_mul_I_eq_zero (a L : ℝ) (k : ℤ) (ha : a ≠ 0) (hk : a * L = 2 * Real.pi * k) :
    ∫ x in (0 : ℝ)..L, Complex.exp (((a * x : ℝ) : ℂ) * Complex.I) = 0 := by
  have hc : (a : ℂ) * Complex.I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr ha) Complex.I_ne_zero
  have hfun : (fun x : ℝ ↦ Complex.exp (((a * x : ℝ) : ℂ) * Complex.I))
      = fun x : ℝ ↦ Complex.exp ((a : ℂ) * Complex.I * (x : ℂ)) := by
    funext x
    congr 1
    push_cast
    ring
  rw [hfun, integral_exp_mul_complex hc]
  have hL : (a : ℂ) * Complex.I * (L : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
    have h := congrArg (fun r : ℝ ↦ (r : ℂ)) hk
    push_cast at h
    linear_combination Complex.I * h
  rw [hL, Complex.exp_int_mul_two_pi_mul_I, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
      sub_self,
    zero_div]

/-- For `0 < k` and every real `h`,
`∫ u in 0..h, Real.exp ((-k) * u) = (1 - Real.exp (-(k * h))) / k`. -/
theorem integral_exp_neg_mul {k h : ℝ} (hk : 0 < k) :
    ∫ u in (0 : ℝ)..h, Real.exp ((-k) * u) = (1 - Real.exp (-(k * h))) / k := by
  rw [intervalIntegral.integral_comp_mul_left (fun x ↦ Real.exp x) (by linarith : (-k) ≠ 0),
    integral_exp]
  simp only [mul_zero, Real.exp_zero, smul_eq_mul]
  field_simp
  ring_nf

/-- For `c ≠ 0` and all real `a`, `t`,
`∫ s in a..t, Real.exp (-(c * (t - s))) = (1 - Real.exp (-(c * (t - a)))) / c`. The proof applies
the fundamental theorem of calculus to the antiderivative `fun s ↦ Real.exp (-(c * (t - s))) / c`.
-/
theorem integral_exp_neg_mul_sub {a t c : ℝ} (hc : c ≠ 0) :
    ∫ s in a..t, Real.exp (-(c * (t - s))) = (1 - Real.exp (-(c * (t - a)))) / c := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s ↦ Real.exp (-(c * (t - s))) / c)]
  · simp only [sub_self, mul_zero, neg_zero, Real.exp_zero]
    ring
  · intro s _
    have h0 : HasDerivAt (fun s : ℝ ↦ -(c * (t - s))) (-(c * (0 - 1))) s :=
      (((hasDerivAt_const s t).sub (hasDerivAt_id' s)).const_mul c).neg
    have h1 : HasDerivAt (fun s : ℝ ↦ -(c * (t - s))) c s := h0.congr_deriv (by ring)
    exact ((h1.exp).div_const c).congr_deriv (by field_simp)
  · exact (by fun_prop : Continuous fun s : ℝ ↦ Real.exp (-(c * (t - s)))).intervalIntegrable _ _

/-- If `c : ℂ` is nonzero and `Complex.exp (c * L) = 1` for a real `L`, then
`∫ x in 0..L, Complex.exp (c * x) = 0`. -/
theorem integral_exp_period_eq_zero {c : ℂ} (hc : c ≠ 0) {L : ℝ} (hL : Complex.exp (c * L) = 1) :
    ∫ x in (0 : ℝ)..L, Complex.exp (c * x) = 0 := by
  rw [integral_exp_mul_complex hc, hL]
  simp

/-- For every real `L`, `∫ x in 0..L, Complex.exp ((((0 : ℝ) * x : ℝ) : ℂ) * Complex.I) = L`. -/
theorem integral_exp_zero_mul_I (L : ℝ) :
    ∫ x in (0 : ℝ)..L, Complex.exp ((((0 : ℝ) * x : ℝ) : ℂ) * Complex.I) = L := by
  simp

/-- Integration by parts against a function `E` with derivative `-(k * I) * E`: let `E F G : ℝ → ℂ`
and `k : ℝ`, with `E` and `G` continuous, `HasDerivAt E (-(k * I) * E t) t` and
`HasDerivAt F (G t) t` for all `t`. If the boundary values agree, `E b * F b = E a * F a`, then
`∫ t in a..b, E t * G t = (k * I) * ∫ t in a..b, E t * F t`. -/
theorem integral_mul_deriv_eq_const_mul_integral (F G E : ℝ → ℂ) (k : ℝ)
    (hE : ∀ t, HasDerivAt E (-(k * Complex.I) * E t) t)
    (hF : ∀ t, HasDerivAt F (G t) t) (hEc : Continuous E) (hGc : Continuous G)
    {a b : ℝ} (hper : E b * F b = E a * F a) :
    ∫ t in a..b, E t * G t = (k * Complex.I) * ∫ t in a..b, E t * F t := by
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun t _ ↦ hE t) (fun t _ ↦ hF t)
    ((continuous_const.mul hEc).intervalIntegrable _ _) (hGc.intervalIntegrable _ _), hper,
        sub_self,
    zero_sub, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
  congr 1
  funext t
  ring

/-- For all real `a`, `t` and `x`,
`∫ s in a..t, x * Real.exp (-(8 * π ^ 2 * (t - s) * x)) = (1 - Real.exp (-(8 * π ^ 2 * (t - a) *
x))) / (8 * π ^ 2)`. The function `s ↦ Real.exp (-(8 * π ^ 2 * (t - s) * x)) / (8 * π ^
2)` is a primitive of the integrand. -/
theorem integral_mul_exp_neg_mul_sub_mul {a t : ℝ} (x : ℝ) :
    ∫ s in a..t, x * Real.exp (-(8 * π ^ 2 * (t - s) * x)) =
      (1 - Real.exp (-(8 * π ^ 2 * (t - a) * x))) / (8 * π ^ 2) := by
  have hk : (8 * π ^ 2 : ℝ) ≠ 0 := by positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s ↦ Real.exp (-(8 * π ^ 2 * (t - s) * x)) / (8 * π ^ 2))]
  · simp only [sub_self, mul_zero, zero_mul, neg_zero, Real.exp_zero]
    ring
  · intro s _
    have h0 : HasDerivAt (fun s : ℝ ↦ -(8 * π ^ 2 * (t - s) * x)) (-(8 * π ^ 2 * (0 - 1) * x)) s :=
      ((((hasDerivAt_const s t).sub (hasDerivAt_id' s)).const_mul (8 * π ^ 2)).mul_const x).neg
    have h1 : HasDerivAt (fun s : ℝ ↦ -(8 * π ^ 2 * (t - s) * x)) (8 * π ^ 2 * x) s :=
      h0.congr_deriv (by ring)
    exact ((h1.exp).div_const (8 * π ^ 2)).congr_deriv (by rw [div_eq_iff hk]; ring)
  · exact (by
      fun_prop : Continuous fun s : ℝ ↦ x * Real.exp (-(8 * π ^ 2 * (t - s) *
          x))).intervalIntegrable _ _

/-- Folding an integral onto one period: let `g : ℝ → ℝ` be continuous and zero outside
`Ioo (-1) 1`, and let `a : ℝ → ℝ` satisfy `a (s + 1) = a s` for all `s` and be integrable on
`Icc 0 1`. Then `∫ s, g s * a s = ∫ s in 0..1, (g (s - 1) + g s) * a s`. The proof restricts the
integral to the interval from `-1` to `1`, splits it at `0`, and shifts the left half by one period.
-/
theorem integral_mul_periodic {g : ℝ → ℝ} (hg : Continuous g)
    (hz : ∀ s, s ∉ Set.Ioo (-1 : ℝ) 1 → g s = 0) {a : ℝ → ℝ} (ha : ∀ s, a (s + 1) = a s)
    (hi : IntegrableOn a (Set.Icc (0 : ℝ) 1)) :
    ∫ s, g s * a s = ∫ s in (0 : ℝ)..1, (g (s - 1) + g s) * a s := by
  have hI : IntervalIntegrable a volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
    exact hi
  have hI' : IntervalIntegrable a volume (-1) 0 := by
    have h := hI.comp_add_right 1
    rw [show (fun x ↦ a (x + 1)) = a from funext ha, zero_sub, sub_self] at h
    exact h
  have hA : IntervalIntegrable (fun s ↦ g s * a s) volume (-1) 0 :=
    hI'.continuousOn_mul hg.continuousOn
  have hB : IntervalIntegrable (fun s ↦ g s * a s) volume 0 1 :=
    hI.continuousOn_mul hg.continuousOn
  have hC : IntervalIntegrable (fun s ↦ g (s - 1) * a s) volume 0 1 :=
    hI.continuousOn_mul (hg.comp (continuous_sub_right 1)).continuousOn
  have hzero : ∫ s, g s * a s = ∫ s in (-1 : ℝ)..1, g s * a s := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ ?_)).symm
    rw [hz x (fun h' ↦ hx ⟨h'.1, h'.2.le⟩), zero_mul]
  have hshift : ∫ s in (-1 : ℝ)..0, g s * a s = ∫ s in (0 : ℝ)..1, g (s - 1) * a s := by
    have h := intervalIntegral.integral_comp_sub_right (fun s ↦ g s * a s) (a := 0) (b := 1) 1
    simp only [zero_sub, sub_self] at h
    rw [← h]
    refine intervalIntegral.integral_congr (fun s _ ↦ ?_)
    have e := ha (s - 1)
    rw [sub_add_cancel] at e
    simp only [e]
  rw [hzero, ← intervalIntegral.integral_add_adjacent_intervals hA hB, hshift,
    ← intervalIntegral.integral_add hC hB]
  refine intervalIntegral.integral_congr (fun s _ ↦ ?_)
  ring

/-- Let `f : ℝ → ℝ` be interval integrable on `0..2 * π` and `w : ℝ → ℂ` continuous. Then
`∫ θ in 0..2 * π, f θ * (w θ).re = (∫ θ in 0..2 * π, (f θ : ℂ) * w θ).re`. The proof commutes the
continuous real-linear map `Complex.reCLM` with the interval integral. -/
theorem integral_mul_re_eq_re_integral (f : ℝ → ℝ) (w : ℝ → ℂ)
    (hf : IntervalIntegrable f volume 0 (2 * Real.pi)) (hw : Continuous w) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), f θ * (w θ).re = (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (f θ : ℂ) * w θ).re := by
  have hc : IntervalIntegrable (fun θ ↦ (f θ : ℂ) * w θ) volume 0 (2 * Real.pi) :=
    (show IntervalIntegrable (fun θ ↦ (f θ : ℂ)) volume 0 (2 * Real.pi) from
      ⟨hf.1.ofReal, hf.2.ofReal⟩).mul_continuousOn hw.continuousOn
  have := Complex.reCLM.intervalIntegral_comp_comm hc
  rw [Complex.reCLM_apply] at this
  rw [← this]
  refine intervalIntegral.integral_congr fun θ _ ↦ ?_
  simp only [Complex.reCLM_apply, Complex.re_ofReal_mul]

/-- For arbitrary functions `f`, `t : ℝ → ℝ`,
`∫ θ in 0..2 * π, (f θ : ℂ) * Complex.exp (t θ * Complex.I)` equals the complex conjugate of
`∫ θ in 0..2 * π, Complex.exp (-(t θ) * Complex.I) * (f θ : ℂ)`. -/
theorem integral_ofReal_mul_cexp_eq_conj (f t : ℝ → ℝ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), (f θ : ℂ) * Complex.exp ((t θ : ℝ) * Complex.I) =
      (starRingEnd ℂ) (∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(t θ : ℝ) * Complex.I) *
          (f θ : ℂ)) := by
  have h : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  rw [intervalIntegral.integral_of_le h, intervalIntegral.integral_of_le h, ← integral_conj]
  refine integral_congr_ae (ae_of_all _ fun θ ↦ ?_)
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, Complex.conj_I]
  ring_nf

/-- For every natural number `n`, `∫ x in (-1 : ℝ)..1, x ^ (2 * n) = 2 / (2 * n + 1)`. -/
theorem integral_pow_two_mul_neg_one_one (n : ℕ) :
    (∫ x in (-1 : ℝ)..1, x ^ (2 * n)) = 2 / (2 * n + 1) := by
  rw [integral_pow]
  have h : ((-1 : ℝ)) ^ (2 * n + 1) = -1 := Odd.neg_one_pow ⟨n, rfl⟩
  rw [h]
  push_cast
  ring

/-- For every natural number `m`, `∫ y in (0 : ℝ)..1, y ^ m = 1 / ((m : ℝ) + 1)`. -/
theorem integral_pow_zero_one (m : ℕ) : (∫ y in (0 : ℝ)..1, y ^ m) = 1 / ((m : ℝ) + 1) := by
  rw [integral_pow]
  simp

/-- If `0 < h` and `g : ℝ → ℂ` is integrable on `Ioc 0 h`, then
`∫ z in 0..h, ∫ s in 0..z, g s = ∫ s in 0..h, g s * ((h - s : ℝ) : ℂ)`. The proof exchanges the
order of integration over the triangle `s ≤ z` by Fubini. -/
theorem integral_primitive_eq_integral_mul_sub {g : ℝ → ℂ} {h : ℝ} (hh : 0 < h)
    (hg : IntegrableOn g (Ioc 0 h)) :
    ∫ z in (0 : ℝ)..h, ∫ s in (0 : ℝ)..z, g s = ∫ s in (0 : ℝ)..h, g s * ((h - s : ℝ) : ℂ) := by
  set μ := volume.restrict (Ioc (0 : ℝ) h) with hμ
  set K : ℝ × ℝ → ℂ := Set.indicator {p : ℝ × ℝ | p.2 ≤ p.1} (fun p ↦ g p.2) with hK
  have hone : Integrable (fun _ : ℝ ↦ (1 : ℂ)) μ :=
    integrableOn_const (by simp)
  have hKi : Integrable K (μ.prod μ) := by
    have := (hone.mul_prod (show Integrable g μ from hg)).indicator
      (measurableSet_le measurable_snd measurable_fst)
    simpa [hK, one_mul] using this
  have inner : ∀ z ∈ Ioc (0 : ℝ) h, ∫ s in (0 : ℝ)..z, g s = ∫ s, K (z, s) ∂μ := by
    intro z hz
    rw [intervalIntegral.integral_of_le hz.1.le]
    have : (fun s ↦ K (z, s)) = Set.indicator (Iic z) g := by
      funext s
      simp [hK, Set.indicator_apply]
    rw [this, hμ, setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, min_eq_right hz.2]
  have outer : ∀ s ∈ Ioc (0 : ℝ) h, ∫ z, K (z, s) ∂μ = g s * ((h - s : ℝ) : ℂ) := by
    intro s hs
    have : (fun z ↦ K (z, s)) = Set.indicator (Ici s) (fun _ ↦ g s) := by
      funext z
      simp [hK, Set.indicator_apply]
    rw [this, hμ, setIntegral_indicator measurableSet_Ici, setIntegral_const]
    have hset : Ioc (0 : ℝ) h ∩ Ici s = Icc s h := by
      ext x
      simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨⟨_, b⟩, c⟩
        exact ⟨c, b⟩
      · rintro ⟨c, b⟩
        exact ⟨⟨by linarith [hs.1], b⟩, c⟩
    rw [hset, Real.volume_real_Icc_of_le hs.2, Complex.real_smul, mul_comm]
  rw [intervalIntegral.integral_of_le hh.le, intervalIntegral.integral_of_le hh.le,
    setIntegral_congr_fun measurableSet_Ioc inner,
    setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ (outer s hs).symm]
  exact integral_integral_swap (f := fun z s ↦ K (z, s)) hKi

/-- For real `a`, `t` and `r` with `-1 < r`,
`∫ s in a..t, (t - s) ^ r = (t - a) ^ (r + 1) / (r + 1)`. -/
theorem integral_rpow_sub_left {a t r : ℝ} (hr : -1 < r) :
    ∫ s in a..t, (t - s) ^ r = (t - a) ^ (r + 1) / (r + 1) := by
  have e := intervalIntegral.integral_comp_sub_left (fun s : ℝ ↦ s ^ r) (a := a) (b := t) t
  rw [e, sub_self, integral_rpow (Or.inl hr), zero_rpow (by linarith : (0 : ℝ) < r + 1).ne',
    sub_zero]

/-- For real `a`, `t` and `r` with `-1 < r`,
`∫ s in a..t, (s - a) ^ r = (t - a) ^ (r + 1) / (r + 1)`. -/
theorem integral_rpow_sub_right {a t r : ℝ} (hr : -1 < r) :
    ∫ s in a..t, (s - a) ^ r = (t - a) ^ (r + 1) / (r + 1) := by
  have e := intervalIntegral.integral_comp_sub_right (fun s : ℝ ↦ s ^ r) (a := a) (b := t) a
  rw [e, sub_self, integral_rpow (Or.inl hr), zero_rpow (by linarith : (0 : ℝ) < r + 1).ne',
    sub_zero]

/-- For `γ < 1` and all real `t₀`, `t`,
`∫ s in t₀..t, (t - s) ^ (-γ) = (t - t₀) ^ (-γ + 1) / (-γ + 1)`. -/
theorem integral_sub_rpow {γ : ℝ} (hγ : γ < 1) (t₀ t : ℝ) :
    ∫ s in t₀..t, (t - s) ^ (-γ) = (t - t₀) ^ (-γ + 1) / (-γ + 1) := by
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ ↦ x ^ (-γ)), sub_self,
    integral_rpow (Or.inl (by linarith))]
  rw [Real.zero_rpow (by linarith), sub_zero]

/-- If `F i l : ℝ → ℂ` is interval integrable on `0..2 * π` for all `i l : Fin 3`, then
`∫ θ in 0..2 * π, ∑ i, ∑ l, F i l θ = ∑ i, ∑ l, ∫ θ in 0..2 * π, F i l θ`. -/
theorem integral_sum_sum_fin_three {F : Fin 3 → Fin 3 → ℝ → ℂ}
    (h : ∀ i l, IntervalIntegrable (F i l) volume 0 (2 * Real.pi)) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), ∑ i : Fin 3, ∑ l : Fin 3, F i l θ =
      ∑ i : Fin 3, ∑ l : Fin 3, ∫ θ in (0 : ℝ)..(2 * Real.pi), F i l θ := by
  rw [intervalIntegral.integral_finsetSum fun i _ ↦ ?_]
  · exact Finset.sum_congr rfl fun i _ ↦ intervalIntegral.integral_finsetSum fun l _ ↦ h i l
  · simp only [Fin.sum_univ_three]
    exact ((h i 0).add (h i 1)).add (h i 2)

/-- Let `E` be a normed additive commutative group and `R : ℝ → E → ℂ` such that
`fun q : ℝ × E ↦ R q.1 q.2` is continuous and `‖R θ u‖ ≤ ‖u‖` for all `θ` and `u`. If `F : ℝ → E`
is integrable on `Ioc 0 (2 * π)`, then `fun θ ↦ R θ (F θ)` is interval integrable on `0..(2 * π)`.
-/
theorem intervalIntegrable_comp_of_norm_le_norm {E : Type*} [NormedAddCommGroup E] {R : ℝ → E → ℂ}
    (hR : Continuous (fun q : ℝ × E ↦ R q.1 q.2)) (hRb : ∀ θ u, ‖R θ u‖ ≤ ‖u‖) {F : ℝ → E}
    (hF : IntegrableOn F (Ioc (0 : ℝ) (2 * Real.pi))) :
    IntervalIntegrable (fun θ ↦ R θ (F θ)) volume 0 (2 * Real.pi) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
  refine Integrable.mono' hF.norm ?_ (Filter.Eventually.of_forall fun θ ↦ hRb θ (F θ))
  exact hR.comp_aestronglyMeasurable (measurable_id.aestronglyMeasurable.prodMk
      hF.aestronglyMeasurable)

/-- If `u : ℝ → ℂ` is Lipschitz with constant `C`, then `deriv u` is interval integrable on `a..b`
for all real `a`, `b`. It is measurable and bounded in norm by `C`. -/
theorem intervalIntegrable_deriv_of_lipschitzWith {u : ℝ → ℂ} {C : NNReal} (hu : LipschitzWith C u)
    (a b : ℝ) :
    IntervalIntegrable (deriv u) volume a b :=
  (intervalIntegrable_const (c := (C : ℝ))).mono_fun' (measurable_deriv u).aestronglyMeasurable
    (ae_of_all _ fun _ ↦ norm_deriv_le_of_lipschitz hu)

/-- If `h : ℝ → ℂ` satisfies `MemLp h 2 (volume.restrict (Ioc (-π) π))`, then for every integer `k`
the function `θ ↦ exp (-(k * θ * I)) * h θ` is interval integrable between `-π` and `π`. -/
theorem intervalIntegrable_exp_neg_mul_of_memLp_two (h : ℝ → ℂ)
    (hh : MemLp h 2 (volume.restrict (Ioc (-Real.pi) Real.pi))) (k : ℤ) :
    IntervalIntegrable (fun θ ↦ Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)) * h θ) volume
        (-Real.pi) Real.pi := by
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hi : IntegrableOn h (Ioc (-Real.pi) Real.pi) := hh.integrable one_le_two
  have h1 : IntervalIntegrable h volume (-Real.pi) Real.pi :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi).mpr hi
  exact h1.continuousOn_mul (by fun_prop : Continuous fun θ : ℝ ↦
    Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I))).continuousOn

/-- Let `s` be a finite set of indices and let `f i : ℝ → ℂ` be interval integrable on `0..2 * π`
for each `i ∈ s`. Then the pointwise sum `fun θ ↦ ∑ i ∈ s, f i θ` is interval integrable on
`0..2 * π`. The proof is by induction on `s`. -/
theorem intervalIntegrable_finsetSum_complex_two_pi {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (h : ∀ i ∈ s, IntervalIntegrable (f i) volume 0 (2 * Real.pi)) :
    IntervalIntegrable (fun θ ↦ ∑ i ∈ s, f i θ) volume 0 (2 * Real.pi) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp
  · intro a s ha ih h
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- Let `s` be a finite set of indices and let `f i : ℝ → ℝ` be interval integrable on `a..b` for
each `i ∈ s`. Then the pointwise sum `fun x ↦ ∑ i ∈ s, f i x` is interval integrable on `a..b`. -/
theorem intervalIntegrable_finsetSum_real {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} {a b : ℝ}
    (h : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun x ↦ ∑ i ∈ s, f i x) volume a b := by
  exact ⟨integrable_finsetSum s fun i hi ↦ (h i hi).1,
      integrable_finsetSum s fun i hi ↦ (h i hi).2⟩

/-- If `ρ₁ ≤ ρ₂`, `u : ℝ → ℂ` is integrable on `Icc ρ₁ ρ₂` and `f : ℝ × ℝ → ℝ` is Lipschitz, then
`fun r ↦ u r * (f (r, 0) : ℂ) * (r : ℂ)` is interval integrable on `ρ₁..ρ₂`. -/
theorem intervalIntegrable_mul_lipschitzWith_mul_id {u : ℝ → ℂ} {ρ₁ ρ₂ : ℝ} (hρ : ρ₁ ≤ ρ₂)
    (hu : IntegrableOn u (Icc ρ₁ ρ₂))
    {f : ℝ × ℝ → ℝ} {K : NNReal} (hf : LipschitzWith K f) :
    IntervalIntegrable (fun r ↦ u r * (f (r, 0) : ℂ) * (r : ℂ)) volume ρ₁ ρ₂ := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hρ]
  have c1 : Continuous fun r : ℝ ↦ (f (r, 0) : ℂ) :=
    Complex.continuous_ofReal.comp (hf.continuous.comp (by fun_prop))
  have c2 : Continuous fun r : ℝ ↦ (r : ℂ) := Complex.continuous_ofReal
  exact (hu.mul_continuousOn c1.continuousOn isCompact_Icc).mul_continuousOn c2.continuousOn
      isCompact_Icc

/-- If `g h : ℝ → ℝ` both satisfy `MemLp _ 2 (volume.restrict (Ioc 0 (2 * π)))`, then the product
`θ ↦ g θ * h θ` is interval integrable between `0` and `2 * π`. -/
theorem intervalIntegrable_mul_of_memLp_two {g h : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Set.Ioc 0 (2 * π))))
    (hh : MemLp h 2 (volume.restrict (Set.Ioc 0 (2 * π)))) :
    IntervalIntegrable (fun θ ↦ g θ * h θ) volume 0 (2 * π) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le]
  exact hg.integrable_mul hh

/-- If `fz : ℝ → ℂ` is integrable on `Ioo l r` and `l ≤ a`, `a ≤ b`, `b < r`, then `fz` is interval
integrable on `a..b`. -/
theorem intervalIntegrable_of_integrableOn_Ioo {fz : ℝ → ℂ} {l r a b : ℝ}
    (h : IntegrableOn fz (Ioo l r)) (hla : l ≤ a) (hab : a ≤ b) (hbr : b < r) :
    IntervalIntegrable fz volume a b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
    (h.mono_set fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩)

/-- A function `B : ℝ → ℂ` that is locally integrable with respect to Lebesgue measure is interval
integrable on `a..b` for all real `a`, `b`. -/
theorem intervalIntegrable_of_locallyIntegrable {B : ℝ → ℂ} (hB : LocallyIntegrable B volume)
    (a b : ℝ) :
    IntervalIntegrable B volume a b :=
  (hB.integrableOn_isCompact isCompact_uIcc).intervalIntegrable

/-- If `f : ℝ → ℝ` satisfies `MemLp f 2 (volume.restrict (Ioc 0 (2 * π)))`, then `f` is interval
integrable between `0` and `2 * π`. The interval has finite measure, so `L²` is contained in `L¹`
there. -/
theorem intervalIntegrable_of_memLp_two {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π)))) :
    IntervalIntegrable f volume 0 (2 * π) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le]
  have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (2 * π))) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  exact hf.integrable (by norm_num)

/-- For real `a`, `t` and `r` with `-1 < r`, the function `fun s ↦ (t - s) ^ r` is interval
integrable on `a..t`. -/
theorem intervalIntegrable_rpow_sub_left {a t r : ℝ} (hr : -1 < r) :
    IntervalIntegrable (fun s ↦ (t - s) ^ r) volume a t := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t - a) hr).comp_sub_left t
  rw [sub_zero, sub_sub_cancel] at h
  exact h.symm

/-- For real `a`, `t` and `r` with `-1 < r`, the function `fun s ↦ (s - a) ^ r` is interval
integrable on `a..t`. -/
theorem intervalIntegrable_rpow_sub_right {a t r : ℝ} (hr : -1 < r) :
    IntervalIntegrable (fun s ↦ (s - a) ^ r) volume a t := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t - a) hr).comp_sub_right a
  rw [zero_add, sub_add_cancel] at h
  exact h

/-- Let `g : ℝ × ℝ → ℝ` be continuous and let `W : ℝ × ℝ → ℝ` be continuous on a set `U`. If
`(t, c) ∈ U` for all `t ∈ uIcc a b`, then `fun t ↦ g (t, c) ^ 2 * W (t, c)` is interval integrable
on `a..b`. -/
theorem intervalIntegrable_sq_mul_of_continuousOn {g W : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hg : Continuous g)
    (hW : ContinuousOn W U) {c a b : ℝ} (h : ∀ t ∈ uIcc a b, (t, c) ∈ U) :
    IntervalIntegrable (fun t ↦ g (t, c) ^ 2 * W (t, c)) volume a b :=
  ContinuousOn.intervalIntegrable
    (((hg.comp (continuous_id.prodMk continuous_const)).pow 2).continuousOn.mul
      (hW.comp (continuous_id.prodMk continuous_const).continuousOn h))

/-- For `γ < 1` and all real `t₀`, `t`, the function `fun s ↦ (t - s) ^ (-γ)` is interval
integrable on `t₀..t` with respect to Lebesgue measure. -/
theorem intervalIntegrable_sub_rpow {γ : ℝ} (hγ : γ < 1) (t₀ t : ℝ) :
    IntervalIntegrable (fun s : ℝ ↦ (t - s) ^ (-γ)) volume t₀ t := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := t - t₀) (b := t - t)
    (r := -γ) (by linarith)).comp_sub_left t
  simpa only [sub_sub_cancel] using h

/-- If `F l : ℝ → ℂ` is interval integrable on `0..2 * π` for each `l : Fin 3`, then so is the sum
`fun θ ↦ ∑ l, F l θ`. A case of `PDE.Analysis.intervalIntegrable_finsetSum_complex_two_pi`. -/
theorem intervalIntegrable_sum_fin_three {F : Fin 3 → ℝ → ℂ}
    (h : ∀ l, IntervalIntegrable (F l) volume 0 (2 * Real.pi)) :
    IntervalIntegrable (fun θ ↦ ∑ l : Fin 3, F l θ) volume 0 (2 * Real.pi) :=
  intervalIntegrable_finsetSum_complex_two_pi Finset.univ F fun i _ ↦ h i

/-- If `F i l : ℝ → ℂ` is interval integrable on `0..2 * π` for all `i l : Fin 3`, then so is the
double sum `fun θ ↦ ∑ i, ∑ l, F i l θ`. -/
theorem intervalIntegrable_sum_sum_fin_three {F : Fin 3 → Fin 3 → ℝ → ℂ}
    (h : ∀ i l, IntervalIntegrable (F i l) volume 0 (2 * Real.pi)) :
    IntervalIntegrable (fun θ ↦ ∑ i : Fin 3, ∑ l : Fin 3, F i l θ) volume 0 (2 * Real.pi) := by
  simp only [Fin.sum_univ_three]
  have := fun i ↦ ((h i 0).add (h i 1)).add (h i 2)
  exact ((this 0).add (this 1)).add (this 2)

/-- If `f : ℝ → ℂ` is almost everywhere strongly measurable with respect to Lebesgue measure and
`‖f θ‖ ≤ C` for all `θ`, then `f` is interval integrable on `0..2 * π`. -/
theorem intervalIntegrable_two_pi_of_norm_le (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume)
    (C : ℝ) (hC : ∀ θ, ‖f θ‖ ≤ C) :
    IntervalIntegrable f volume 0 (2 * Real.pi) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
  have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))) :=
    isFiniteMeasure_restrict.mpr (by simp [ENNReal.mul_eq_top])
  exact Integrable.mono' (integrable_const C) hf.restrict (ae_of_all _ hC)

/-- For `q : ℝ → ℂ` periodic with period `2 * π`,
`∫ φ in 0..(2 * π), q (-φ) = ∫ φ in 0..(2 * π), q φ`. -/
theorem intervalIntegral_comp_neg_of_periodic (q : ℝ → ℂ) (hq : Function.Periodic q (2 * Real.pi)) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi), q (-φ) = ∫ φ in (0 : ℝ)..(2 * Real.pi), q φ := by
  rw [intervalIntegral.integral_comp_neg, neg_zero]
  have h := hq.intervalIntegral_add_eq (-(2 * Real.pi)) 0
  rwa [neg_add_cancel, zero_add] at h

/-- If `f : ℝ → ℝ` satisfies `f t = 0` for all `t`, then `∫ t in a..b, f t = 0` for all real `a` and
`b`. -/
theorem intervalIntegral_eq_zero_of_forall_eq_zero {f : ℝ → ℝ} {a b : ℝ} (h : ∀ t, f t = 0) :
    ∫ t in a..b, f t = 0 := by
  simp [h]

/-- Let `a ≤ b`, let `D : ℝ → ℂ` be integrable on `Ioc a b`, and let `k : ℝ → ℂ` have derivative
`k' x` at every `x`, with `k'` continuous. Then for every complex `c`,
`∫ x in a..b, (D x * k x + (c + ∫ s in a..x, D s) * k' x) = (c + ∫ s in a..b, D s) * k b - c * k
a`. The proof exchanges the order of integration in `∫ x in a..b, (∫ s in a..x, D s) * k'
x` by Fubini on the triangle `s ≤ x`. -/
theorem intervalIntegral_mul_add_primitive_mul_deriv {D k k' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hD : IntegrableOn D (Ioc a b))
    (hk : ∀ x, HasDerivAt k (k' x) x) (hk' : Continuous k') (c : ℂ) :
    ∫ x in a..b, (D x * k x + (c + ∫ s in a..x, D s) * k' x) = (c + ∫ s in a..b, D s) * k b - c *
        k a := by
  set μ := volume.restrict (Ioc a b) with hμ
  have hkc : Continuous k := continuous_iff_continuousAt.2 fun x ↦ (hk x).continuousAt
  have hDμ : Integrable D μ := hD
  have hk'μ : Integrable k' μ := (hk'.integrableOn_Icc (a := a) (b := b)).mono_set
      Ioc_subset_Icc_self
  set Kf : ℝ × ℝ → ℂ := indicator {p : ℝ × ℝ | p.2 ≤ p.1} (fun p ↦ k' p.1 * D p.2) with hKf
  have hKi : Integrable Kf (μ.prod μ) :=
    (hk'μ.mul_prod hDμ).indicator (measurableSet_le measurable_snd measurable_fst)
  have inner : ∀ x ∈ Ioc a b, (∫ s in a..x, D s) * k' x = ∫ s, Kf (x, s) ∂μ := by
    intro x hx
    rw [intervalIntegral.integral_of_le hx.1.le]
    have : (fun s ↦ Kf (x, s)) = indicator (Iic x) (fun s ↦ k' x * D s) := by
      funext s
      simp [hKf, indicator_apply]
    rw [this, hμ, setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, min_eq_right hx.2,
      integral_const_mul, mul_comm]
  have outer : ∀ s ∈ Ioc a b, ∫ x, Kf (x, s) ∂μ = D s * (k b - k s) := by
    intro s hs
    have : (fun x ↦ Kf (x, s)) = indicator (Ici s) (fun x ↦ k' x * D s) := by
      funext x
      simp [hKf, indicator_apply]
    rw [this, hμ, setIntegral_indicator measurableSet_Ici, integral_mul_const]
    have hset : Ioc a b ∩ Ici s = Icc s b := by
      ext x
      simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h3, h2⟩
        exact ⟨⟨by linarith [hs.1], h2⟩, h3⟩
    rw [hset, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs.2,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hk x) (hk'.intervalIntegrable s b)]
    ring
  have hP : ∫ x in a..b, (∫ s in a..x, D s) * k' x = ∫ s in a..b, D s * (k b - k s) := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
      setIntegral_congr_fun measurableSet_Ioc inner,
      setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ (outer s hs).symm]
    exact integral_integral_swap (f := fun x s ↦ Kf (x, s)) hKi
  have iD : IntervalIntegrable D volume a b := (intervalIntegrable_iff_integrableOn_Ioc_of_le
      hab).2 hD
  have hPc : ContinuousOn (fun x ↦ ∫ s in a..x, D s) (uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval (by
      rw [uIcc_of_le hab]
      exact (integrableOn_Icc_iff_integrableOn_Ioc).2 hD)
  have i1 : IntervalIntegrable (fun x ↦ D x * k x) volume a b :=
      iD.mul_continuousOn hkc.continuousOn
  have i3 : IntervalIntegrable (fun x ↦ (∫ s in a..x, D s) * k' x) volume a b :=
    (hPc.mul hk'.continuousOn).intervalIntegrable
  have i4 : IntervalIntegrable (fun x ↦ c * k' x) volume a b :=
      (hk'.intervalIntegrable a b).const_mul c
  have i2 : IntervalIntegrable (fun x ↦ (c + ∫ s in a..x, D s) * k' x) volume a b := by
    refine (i4.add i3).congr ?_
    intro x _
    simp only
    ring
  have i5 : IntervalIntegrable (fun x ↦ D x * k b) volume a b := iD.mul_const _
  rw [intervalIntegral.integral_add i1 i2]
  have e2 : ∫ x in a..b, (c + ∫ s in a..x, D s) * k' x = c * (k b - k a) + ∫ x in a..b,
      (∫ s in a..x, D s) * k' x := by
    have : (fun x ↦ (c + ∫ s in a..x, D s) * k' x) = fun x ↦ c * k' x + (∫ s in a..x, D s) *
        k' x := by
      funext x
      ring
    rw [this, intervalIntegral.integral_add i4 i3, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hk x) (hk'.intervalIntegrable a b)]
  have e3 : ∫ s in a..b, D s * (k b - k s) = (∫ s in a..b, D s) * k b - ∫ s in a..b, D s * k s := by
    have : (fun s ↦ D s * (k b - k s)) = fun s ↦ D s * k b - D s * k s := by
      funext s
      ring
    rw [this, intervalIntegral.integral_sub i5 i1, intervalIntegral.integral_mul_const]
  rw [e2, hP, e3]
  ring

/-- For `f : ℝ → ℂ` periodic with period `2 * π`, `∫ θ in 0..(2 * π), f θ = ∫ θ in (-π)..π, f θ`. -/
theorem intervalIntegral_two_pi_eq_neg_pi_pi (f : ℝ → ℂ) (hf : Function.Periodic f (2 * Real.pi)) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), f θ = ∫ θ in (-Real.pi)..Real.pi, f θ := by
  have h := hf.intervalIntegral_add_eq 0 (-Real.pi)
  rw [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring] at h
  exact h

/-- Let `f : ℝ → G` take values in a real normed space and let `-1 < e`. If `‖f s‖ ≤ K * s ^ e` for
all `s ∈ Ioc 0 1`, then `‖∫ s in 0..1, f s‖ ≤ K / (e + 1)`. -/
theorem norm_integral_le_of_le_mul_rpow {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : ℝ → G)
    {K e : ℝ} (he : -1 < e) (hK : ∀ s ∈ Ioc (0 : ℝ) 1, ‖f s‖ ≤ K * s ^ e) :
    ‖∫ s in (0 : ℝ)..1, f s‖ ≤ K / (e + 1) := by
  have hint : IntervalIntegrable (fun s : ℝ ↦ K * s ^ e) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' he).const_mul K
  refine (intervalIntegral.norm_integral_le_of_norm_le zero_le_one (ae_of_all _ hK) hint).trans
    (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl he), Real.one_rpow,
    Real.zero_rpow (by linarith)]
  ring

/-- Let `a ≤ b`, let `fd : ℝ → ℂ` be integrable on `Icc a b`, and suppose `|(r - o) / (c - o)| ≤ 1`
for all `r ∈ Icc a b`. Then
`‖∫ r in Icc a b, (((r - o) / (c - o) : ℝ) : ℂ) * fd r‖ ≤ ∫ r in a..b, ‖fd r‖`. -/
theorem norm_setIntegral_div_mul_le_integral_norm (fd : ℝ → ℂ) (a b c o : ℝ) (hab : a ≤ b)
    (hfd : IntegrableOn fd (Icc a b))
    (hw : ∀ r ∈ Icc a b, |(r - o) / (c - o)| ≤ 1) :
    ‖∫ r in Icc a b, (((r - o) / (c - o) : ℝ) : ℂ) * fd r‖ ≤ ∫ r in a..b, ‖fd r‖ := by
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  refine norm_integral_le_of_norm_le hfd.norm ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (hw r hr)

/-- For `a ≤ t` and `0 ≤ L`,
`(1 + L) * ∫ s in a..t, Real.exp (-(8 * π ^ 2 * L) * (t - s)) ≤ (t - a) + 1`. The integrand is at
most `1`, so the integral is at most `t - a`, and `L` times the integral equals
`(1 - Real.exp (-(8 * π ^ 2 * L) * (t - a))) / (8 * π ^ 2)`, which is at most `1`. -/
theorem one_add_mul_integral_exp_neg_le {a t L : ℝ} (hat : a ≤ t) (hL : 0 ≤ L) :
    (1 + L) * ∫ s in a..t, Real.exp (-(8 * π ^ 2 * L) * (t - s)) ≤ (t - a) + 1 := by
  have hc : Continuous (fun s : ℝ ↦ Real.exp (-(8 * π ^ 2 * L) * (t - s))) := by fun_prop
  have hI1 : ∫ s in a..t, Real.exp (-(8 * π ^ 2 * L) * (t - s)) ≤ t - a := by
    have h := intervalIntegral.integral_mono_on hat (hc.intervalIntegrable (μ := volume) a t)
      (continuous_const.intervalIntegrable (μ := volume) a t) (fun s hs ↦ by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ 8 * π ^ 2 * L * (t - s) := by
          have : 0 ≤ t - s := by linarith [hs.2]
          positivity
        linarith)
    simpa using h
  have hI2 : L * ∫ s in a..t, Real.exp (-(8 * π ^ 2 * L) * (t - s)) ≤ 1 := by
    rcases hL.eq_or_lt with h0 | hpos
    · rw [← h0, zero_mul]
      norm_num
    · set c := 8 * π ^ 2 * L with hcdef
      have hcpos : 0 < c := by positivity
      have hderiv : ∀ x ∈ uIcc a t, HasDerivAt (fun s ↦ Real.exp (-c * (t - s)) / c)
          (Real.exp (-c * (t - x))) x := by
        intro x _
        have h1 : HasDerivAt (fun s ↦ -c * (t - s)) (-c * (0 - 1)) x :=
          ((hasDerivAt_const x t).sub (hasDerivAt_id x)).const_mul (-c)
        have h2 := h1.exp.div_const c
        have e : Real.exp (-c * (t - x)) * (-c * (0 - 1)) / c = Real.exp (-c * (t - x)) := by
          rw [show -c * (0 - 1) = c by ring, mul_div_assoc, div_self hcpos.ne', mul_one]
        rw [e] at h2
        exact h2
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hc.intervalIntegrable a t)]
      have hpi : 0 < π ^ 2 := by positivity
      have hexp : 0 < Real.exp (-c * (t - a)) := Real.exp_pos _
      simp only [sub_self, mul_zero, Real.exp_zero]
      rw [hcdef]
      have hL' : L * ((1 / (8 * π ^ 2 * L)) - Real.exp (-(8 * π ^ 2 * L) * (t - a)) /
          (8 * π ^ 2 * L))
          = (1 - Real.exp (-(8 * π ^ 2 * L) * (t - a))) / (8 * π ^ 2) := by
        field_simp
      rw [hL']
      rw [div_le_one (by positivity)]
      have : 1 ≤ 8 * π ^ 2 := by nlinarith [Real.pi_gt_three]
      linarith [Real.exp_pos (-(8 * π ^ 2 * L) * (t - a))]
  nlinarith

/-- For a `C^1` function `ψ : ℝ → ℝ` and `a ≤ t`, `∫ r in Ico a t, deriv ψ r = ψ t - ψ a`. -/
theorem setIntegral_Ico_deriv_eq_sub {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) {a t : ℝ} (hat : a ≤ t) :
    ∫ r in Ico a t, deriv ψ r = ψ t - ψ a := by
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hat]
  exact intervalIntegral.integral_deriv_eq_sub (fun x _ ↦ (hψ.differentiable one_ne_zero) x)
    ((hψ.continuous_deriv le_rfl).intervalIntegrable _ _)

/-- Let `0 < T` and let `f : ℝ → ℝ` be almost everywhere strongly measurable for Lebesgue measure
restricted to `Ioi 0`, with `0 ≤ f τ` for all `τ > 0`. If `g` is integrable on `Ioc 0 T` with
`f τ ≤ g τ` there, and `h` is integrable on `Ioi T` with `f τ ≤ h τ` there, then `f` is integrable
on `Ioi 0` and `∫ τ in Ioi 0, f τ ≤ (∫ τ in Ioc 0 T, g τ) + ∫ τ in Ioi T, h τ`. The proof splits
`Ioi 0` into `Ioc 0 T` and `Ioi T` and compares on each piece. -/
theorem setIntegral_Ioi_le_integral_Ioc_add_Ioi {f g h : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hf0 : ∀ τ : ℝ, 0 < τ → 0 ≤ f τ)
    (hg : IntegrableOn g (Ioc 0 T)) (hh : IntegrableOn h (Ioi T))
    (hfg : ∀ τ ∈ Ioc 0 T, f τ ≤ g τ) (hfh : ∀ τ ∈ Ioi T, f τ ≤ h τ) :
    IntegrableOn f (Ioi 0) ∧
      ∫ τ in Ioi 0, f τ ≤ (∫ τ in Ioc 0 T, g τ) + ∫ τ in Ioi T, h τ := by
  have h1 : IntegrableOn f (Ioc 0 T) := by
    refine hg.mono' (hf.mono_set Ioc_subset_Ioi_self) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun τ hτ ↦ ?_)
    rw [Real.norm_of_nonneg (hf0 τ hτ.1)]
    exact hfg τ hτ
  have h2 : IntegrableOn f (Ioi T) := by
    refine hh.mono' (hf.mono_set (Ioi_subset_Ioi hT.le)) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun τ hτ ↦ ?_)
    rw [Real.norm_of_nonneg (hf0 τ (hT.trans hτ))]
    exact hfh τ hτ
  have hU : Ioc 0 T ∪ Ioi T = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi hT.le
  refine ⟨by rw [← hU]; exact h1.union h2, ?_⟩
  rw [← hU, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi h1 h2]
  exact add_le_add (setIntegral_mono_on h1 hg measurableSet_Ioc hfg)
    (setIntegral_mono_on h2 hh measurableSet_Ioi hfh)

/-- For every `F : ℝ → ℂ` and real `a`, `∫ x in Ioo (-a) a, F (-x) = ∫ x in Ioo (-a) a, F x`. The
proof uses that negation preserves Lebesgue measure and maps `Ioo (-a) a` onto itself. -/
theorem setIntegral_Ioo_symm_comp_neg {a : ℝ} (F : ℝ → ℂ) :
    ∫ x in Set.Ioo (-a) a, F (-x) = ∫ x in Set.Ioo (-a) a, F x := by
  have hpre : (fun x : ℝ ↦ -x) ⁻¹' Set.Ioo (-a) a = Set.Ioo (-a) a := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioo]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
    (Homeomorph.neg ℝ).measurableEmbedding F (Set.Ioo (-a) a)
  rw [hpre] at h
  exact h

/-- For real `a`, `b`, `A : ℝ → ℂ` integrable on `Icc a b` and `k : ℝ → ℂ` continuous,
`∫ z in Icc a b, (∫ u in a..z, A u) * k z = ∫ u in Icc a b, A u * ∫ z in u..b, k z`. The proof
applies Fubini to `A u * k z` on the triangle `u ≤ z` inside `Icc a b ×ˢ Icc a b`. -/
theorem setIntegral_primitive_mul_eq_mul_primitive {a b : ℝ} {A : ℝ → ℂ}
    (hA : IntegrableOn A (Icc a b))
    {k : ℝ → ℂ} (hk : Continuous k) :
    ∫ z in Icc a b, (∫ u in a..z, A u) * k z = ∫ u in Icc a b, A u * ∫ z in u..b, k z := by
  set μ := volume.restrict (Icc a b)
  have hkI : Integrable k μ := hk.continuousOn.integrableOn_compact isCompact_Icc
  have hmeas : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} :=
      measurableSet_le measurable_fst measurable_snd
  have hint : Integrable ({p : ℝ × ℝ | p.1 ≤ p.2}.indicator (fun p ↦ A p.1 * k p.2)) (μ.prod μ) :=
    (Integrable.mul_prod hA hkI).indicator hmeas
  have h1 : ∀ z ∈ Icc a b, ∫ u in Icc a b, {p : ℝ × ℝ | p.1 ≤ p.2}.indicator
      (fun p ↦ A p.1 * k p.2) (u, z)
      = (∫ u in a..z, A u) * k z := by
    intro z hz
    have e : (fun u ↦ {p : ℝ × ℝ | p.1 ≤ p.2}.indicator (fun p ↦ A p.1 * k p.2) (u, z))
        = (Iic z).indicator (fun u ↦ A u * k z) := by
      funext u
      simp [Set.indicator]
    rw [e, setIntegral_indicator measurableSet_Iic, integral_mul_const]
    congr 1
    have hs : Icc a b ∩ Iic z = Icc a z := by
      ext u
      simp only [mem_inter_iff, mem_Icc, mem_Iic]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨⟨h1, le_trans h3 hz.2⟩, h3⟩
    rw [hs, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hz.1]
  have h2 : ∀ u ∈ Icc a b, ∫ z in Icc a b, {p : ℝ × ℝ | p.1 ≤ p.2}.indicator
      (fun p ↦ A p.1 * k p.2) (u, z)
      = A u * ∫ z in u..b, k z := by
    intro u hu
    have e : (fun z ↦ {p : ℝ × ℝ | p.1 ≤ p.2}.indicator (fun p ↦ A p.1 * k p.2) (u, z))
        = (Ici u).indicator (fun z ↦ A u * k z) := by
      funext z
      simp [Set.indicator]
    rw [e, setIntegral_indicator measurableSet_Ici, integral_const_mul]
    congr 1
    have hs : Icc a b ∩ Ici u = Icc u b := by
      ext z
      simp only [mem_inter_iff, mem_Icc, mem_Ici]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h1, h3⟩
        exact ⟨⟨le_trans hu.1 h1, h3⟩, h1⟩
    rw [hs, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hu.2]
  have hswap := integral_integral_swap (μ := μ) (ν := μ)
    (f := fun u z ↦ {p : ℝ × ℝ | p.1 ≤ p.2}.indicator (fun p ↦ A p.1 * k p.2) (u, z)) hint
  rw [← setIntegral_congr_fun measurableSet_Icc h1, ← setIntegral_congr_fun measurableSet_Icc h2]
  exact hswap.symm

/-- Cauchy-Schwarz inequality on `0..1` for real polynomials `f` and `g`, under the hypothesis
`0 < ∫ y in 0..1, g.eval y ^ 2`:
`(∫ y in 0..1, f.eval y * g.eval y) ^ 2 ≤ (∫ y in 0..1, f.eval y ^ 2) * ∫ y in 0..1, g.eval y ^
2`. The proof expands the nonnegative integral of `(c * f.eval y - b * g.eval y) ^
2`, where `b` is the integral of the product and `c` the integral of `g.eval y ^ 2`. -/
theorem sq_integral_eval_mul_eval_le (f g : ℝ[X]) (hc : 0 < ∫ y in (0 : ℝ)..1, g.eval y ^ 2) :
    (∫ y in (0 : ℝ)..1, f.eval y * g.eval y) ^ 2
      ≤ (∫ y in (0 : ℝ)..1, f.eval y ^ 2) * ∫ y in (0 : ℝ)..1, g.eval y ^ 2 := by
  set a := ∫ y in (0 : ℝ)..1, f.eval y ^ 2
  set b := ∫ y in (0 : ℝ)..1, f.eval y * g.eval y
  set c := ∫ y in (0 : ℝ)..1, g.eval y ^ 2
  have h0 : 0 ≤ ∫ y in (0 : ℝ)..1, (c * f.eval y - b * g.eval y) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun y _ ↦ sq_nonneg _)
  have e : ∀ y : ℝ, (c * f.eval y - b * g.eval y) ^ 2
      = c ^ 2 * f.eval y ^ 2 + (-2 * c * b) * (f.eval y * g.eval y) + b ^ 2 * g.eval y ^ 2 := by
    intro y
    ring
  simp_rw [e] at h0
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h0
  · have h1 : 0 ≤ c * (c * a - b ^ 2) := by nlinarith
    have h2 : 0 ≤ c * a - b ^ 2 := by
      by_contra hneg
      rw [not_le] at hneg
      nlinarith
    nlinarith
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- Cauchy-Schwarz inequality on `0..1` with weight `r` for real polynomials `u` and `v`:
`(∫ r in 0..1, u.eval r * v.eval r * r) ^ 2 ≤ (∫ r in 0..1, u.eval r ^ 2 * r) * ∫ r in 0..1, v.eval
r ^ 2 * r`. The proof uses that `∫ r in 0..1, (t * u.eval r - v.eval r) ^ 2 *
r` is a nonnegative quadratic in `t`, so its discriminant is nonpositive. -/
theorem sq_integral_eval_mul_eval_mul_le (u v : ℝ[X]) :
    (∫ r in (0 : ℝ)..1, u.eval r * v.eval r * r) ^ 2
      ≤ (∫ r in (0 : ℝ)..1, u.eval r ^ 2 * r) * ∫ r in (0 : ℝ)..1, v.eval r ^ 2 * r := by
  set A := ∫ r in (0 : ℝ)..1, u.eval r ^ 2 * r
  set B := ∫ r in (0 : ℝ)..1, u.eval r * v.eval r * r
  set D := ∫ r in (0 : ℝ)..1, v.eval r ^ 2 * r
  have key : ∀ t : ℝ, 0 ≤ A * (t * t) + (-2 * B) * t + D := by
    intro t
    have hnn : 0 ≤ ∫ r in (0 : ℝ)..1, (t * u.eval r - v.eval r) ^ 2 * r :=
      intervalIntegral.integral_nonneg zero_le_one (fun r hr ↦ mul_nonneg (sq_nonneg _) hr.1)
    have e : (fun r ↦ (t * u.eval r - v.eval r) ^ 2 * r) = fun r ↦
        (t * t) * (u.eval r ^ 2 * r) + (-2 * t) * (u.eval r * v.eval r * r) + v.eval r ^ 2 * r := by
      funext r; ring
    have c1 : Continuous fun r ↦ u.eval r ^ 2 * r := by fun_prop
    have c2 : Continuous fun r ↦ u.eval r * v.eval r * r := by fun_prop
    have c3 : Continuous fun r ↦ v.eval r ^ 2 * r := by fun_prop
    rw [e, intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hnn
    · linarith
    · exact (c1.const_smul (t * t)).intervalIntegrable _ _
    · exact (c2.const_smul (-2 * t)).intervalIntegrable _ _
    · exact ((c1.const_smul (t * t)).add (c2.const_smul (-2 * t))).intervalIntegrable _ _
    · exact c3.intervalIntegrable _ _
  have h := discrim_le_zero key
  unfold discrim at h
  nlinarith

/-- Let `φ : ℝ → ℂ` be integrable on `Icc inner outer` with `inner ≤ outer`, and let `lo`,
`hi : Fin k → ℝ` with `lo s ≤ hi s` give intervals `[lo s, hi s]` that lie in `[inner, outer]`,
cover it, and satisfy `hi s ≤ lo s'` or `hi s' ≤ lo s` whenever `s ≠ s'`. Then
`∑ s, ∫ r in lo s..hi s, φ r = ∫ r in inner..outer, φ r`. The proof writes each integral with the
indicator of `Ioc (lo s) (hi s)` and shows that these indicators add up to the indicator of
`Ioc inner outer` away from the finitely many points `lo s`. -/
theorem sum_intervalIntegral_eq_of_cover_disjoint (φ : ℝ → ℂ) {inner outer : ℝ} {k : ℕ}
    (lo hi : Fin k → ℝ)
    (hφ : IntegrableOn φ (Icc inner outer)) (hio : inner ≤ outer) (hlohi : ∀ s, lo s ≤ hi s)
    (cover : ∀ r, inner ≤ r → r ≤ outer → ∃ s, lo s ≤ r ∧ r ≤ hi s)
    (disj : ∀ s s', s ≠ s' → hi s ≤ lo s' ∨ hi s' ≤ lo s)
    (inside : ∀ s, inner ≤ lo s ∧ hi s ≤ outer) :
    ∑ s, ∫ r in lo s..hi s, φ r = ∫ r in inner..outer, φ r := by
  simp_rw [intervalIntegral.integral_of_le (hlohi _), intervalIntegral.integral_of_le hio,
    ← integral_indicator measurableSet_Ioc]
  rw [← integral_finsetSum]
  · refine integral_congr_ae ?_
    filter_upwards [ae_forall_fin_ne lo] with r hr
    by_cases hm : r ∈ Ioc inner outer
    · obtain ⟨s, hs1, hs2⟩ := cover r hm.1.le hm.2
      have hs : r ∈ Ioc (lo s) (hi s) := ⟨lt_of_le_of_ne hs1 (hr s).symm, hs2⟩
      rw [Finset.sum_eq_single s, indicator_of_mem hm, indicator_of_mem hs]
      · intro s' _ hs'
        refine indicator_of_notMem (fun h' ↦ ?_) _
        rcases disj s s' (Ne.symm hs') with h | h
        · linarith [hs.2, h'.1]
        · linarith [h'.2, hs.1]
      · intro h
        exact absurd (Finset.mem_univ s) h
    · rw [indicator_of_notMem hm]
      refine Finset.sum_eq_zero (fun s _ ↦ indicator_of_notMem (fun h ↦ hm ?_) _)
      exact ⟨lt_of_le_of_lt (inside s).1 h.1, h.2.trans (inside s).2⟩
  · intro s _
    exact (integrable_indicator_iff measurableSet_Ioc).2
      (hφ.mono_set (fun r hr ↦ ⟨(inside s).1.trans hr.1.le, hr.2.trans (inside s).2⟩))

/-- Let `u : ℝ → ℂ` be Lipschitz and `L : ℂ →L[ℝ] ℝ` a continuous real-linear functional. Then for
real `A`, `o`, `a`, `b`,
`L (∫ r in a..b, (A * u r + ((r - o) * A) * deriv u r)) = ((b - o) * A) * L (u b) - ((a - o) * A) *
L (u a)`, the real coefficients inside the integral being cast to `ℂ`. The proof applies integration
by parts for absolutely continuous functions to `fun r ↦ (r - o) * A` and `fun r ↦ L (u r)`. -/
theorem clm_integral_mul_add_sub_mul_deriv (L : ℂ →L[ℝ] ℝ) {u : ℝ → ℂ} {C : NNReal}
    (hu : LipschitzWith C u) (A o a b : ℝ) :
    L (∫ r in a..b, (((A : ℝ) : ℂ) * u r + (((r - o) * A : ℝ) : ℂ) * deriv u r)) =
      ((b - o) * A) * L (u b) - ((a - o) * A) * L (u a) := by
  have hcont : Continuous u := hu.continuous
  have hF : IntervalIntegrable (fun r ↦ (((A : ℝ) : ℂ) * u r + (((r - o) * A : ℝ) : ℂ) *
      deriv u r)) volume a b := by
    refine IntervalIntegrable.add ?_ ?_
    · exact (continuous_const.mul hcont).intervalIntegrable _ _
    · exact (intervalIntegrable_deriv_of_lipschitzWith hu a b).continuousOn_mul (by fun_prop)
  rw [← L.intervalIntegral_comp_comm hF]
  have hw : LipschitzWith ‖A‖₊ (fun r : ℝ ↦ (r - o) * A) := by
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    rw [Real.dist_eq, Real.dist_eq, coe_nnNorm, Real.norm_eq_abs, ← sub_mul, abs_mul, mul_comm]
    ring_nf
    rfl
  have hLu : LipschitzWith (‖L‖₊ * C) (fun r ↦ L (u r)) := L.lipschitzWith.comp hu
  have key := AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub
    (hw.lipschitzOnWith.absolutelyContinuousOnInterval (a := a) (b := b))
    (hLu.lipschitzOnWith.absolutelyContinuousOnInterval (a := a) (b := b))
  rw [← key]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hu.ae_differentiableAt_real] with r hr _
  have h1 : deriv (fun r ↦ L (u r)) r = L (deriv u r) :=
    (L.hasFDerivAt.comp_hasDerivAt r hr.hasDerivAt).deriv
  have h2 : deriv (fun r : ℝ ↦ (r - o) * A) r = A := by
    have : HasDerivAt (fun r : ℝ ↦ (r - o) * A) (1 * A) r :=
      ((hasDerivAt_id' r).sub_const o).mul_const A
    rw [this.deriv]; ring
  rw [h1, h2]
  simp only [map_add]
  rw [show (((A : ℝ) : ℂ) * u r) = A • u r from (Complex.real_smul).symm,
    show ((((r - o) * A : ℝ) : ℂ) * deriv u r) = ((r - o) * A) • deriv u r from
        (Complex.real_smul).symm,
    map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- For all real `a`, `t` and `K`,
`∫ s in a..t, K * (t - s) ^ (-(3 / 4 : ℝ)) = K * (4 * (t - a) ^ (1 / 4 : ℝ))`. -/
theorem integral_const_mul_rpow_neg_three_quarters {a t K : ℝ} :
    ∫ s in a..t, K * (t - s) ^ (-(3 / 4 : ℝ)) = K * (4 * (t - a) ^ (1 / 4 : ℝ)) := by
  rw [intervalIntegral.integral_const_mul, integral_rpow_sub_left (r := -(3 / 4 : ℝ)) (by norm_num)]
  have q1 : (-(3 / 4 : ℝ) + 1) = 1 / 4 := by norm_num
  rw [q1]
  ring

/-- For real polynomials `a` and `b` with `a.eval 0 = 0` and `a.eval 1 = 0`,
`∫ x in 0..1, (derivative a).eval x * b.eval x = -∫ x in 0..1, a.eval x * (derivative b).eval
x`. This is integration by parts on `0..1` with vanishing boundary terms. -/
theorem integral_derivative_mul_of_eval_eq_zero (a b : ℝ[X]) (h0 : a.eval 0 = 0)
    (h1 : a.eval 1 = 0) :
    ∫ x in (0 : ℝ)..1, (derivative a).eval x * b.eval x
      = -∫ x in (0 : ℝ)..1, a.eval x * (derivative b).eval x := by
  have h := integral_eval_mul_eval_derivative a b
  rw [h0, h1, mul_zero, mul_zero, sub_zero, zero_sub] at h
  have e1 : (fun x ↦ (derivative a).eval x * b.eval x) = fun x ↦ b.eval x *
      (derivative a).eval x := by
    funext x; ring
  have e2 : (fun x ↦ a.eval x * (derivative b).eval x) = fun x ↦ (derivative b).eval x *
      a.eval x := by
    funext x; ring
  rw [e1, e2, h]

/-- For a nonzero integer `k`,
`∫ φ in 0..2 * π, Complex.exp (-(((k * φ : ℝ) : ℂ) * Complex.I)) = 0`. The proof rewrites the
integrand as `Complex.exp (c * φ)` with `c = -k * Complex.I` and uses
`Complex.exp (c * (2 * π)) = 1`. -/
theorem integral_exp_neg_int_mul_I {k : ℤ} (hk : k ≠ 0) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(((k * φ : ℝ) : ℂ) * Complex.I)) = 0 := by
  have e : ∀ φ : ℝ, Complex.exp (-(((k * φ : ℝ) : ℂ) * Complex.I))
      = Complex.exp ((-(k : ℂ) * Complex.I) * (φ : ℂ)) := fun φ ↦ by
    congr 1
    push_cast
    ring
  simp_rw [e]
  refine integral_exp_period_eq_zero (mul_ne_zero (neg_ne_zero.2 (Int.cast_ne_zero.2 hk))
      Complex.I_ne_zero) ?_
  rw [show (-(k : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ) = ((-k : ℤ) : ℂ) *
      (2 * Real.pi * Complex.I) by
    push_cast
    ring]
  exact Complex.exp_int_mul_two_pi_mul_I _

/-- For a nonzero integer `k`,
`∫ τ in 0..1, Complex.exp (-(((2 * π * k * τ : ℝ) : ℂ) * Complex.I)) = 0`. The proof rewrites the
integrand as `Complex.exp (c * τ)` with `c = -k * (2 * π * Complex.I)` and uses `Complex.exp c = 1`.
-/
theorem integral_exp_neg_two_pi_mul_int {k : ℤ} (hk : k ≠ 0) :
    ∫ τ in (0 : ℝ)..1, Complex.exp (-(((2 * Real.pi * k * τ : ℝ) : ℂ) * Complex.I)) = 0 := by
  have e : ∀ τ : ℝ, Complex.exp (-(((2 * Real.pi * k * τ : ℝ) : ℂ) * Complex.I))
      = Complex.exp ((((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) * (τ : ℂ)) := fun τ ↦ by
    congr 1
    push_cast
    ring
  simp_rw [e]
  refine integral_exp_period_eq_zero
    (mul_ne_zero (Int.cast_ne_zero.2 (neg_ne_zero.2 hk)) Complex.two_pi_I_ne_zero) ?_
  rw [Complex.ofReal_one, mul_one]
  exact Complex.exp_int_mul_two_pi_mul_I _

/-- If `ω * L = 2 * π * k` for an integer `k`, then for every `c : ℂ` the integral
`∫ t in 0..L, (c * Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I)).re` equals `L * c.re` when `ω = 0`
and `0` otherwise. The proof moves the real part and the constant `c` out of the integral and uses
the value of the integral of the exponential over whole periods. -/
theorem integral_re_exp_full_period (ω L : ℝ) (k : ℤ) (h : ω * L = 2 * Real.pi * k) (c : ℂ) :
    ∫ t in (0 : ℝ)..L, (c * Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I)).re =
      if ω = 0 then L * c.re else 0 := by
  have hi : IntervalIntegrable (fun t : ℝ ↦ c * Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I))
      volume 0 L :=
    (by fun_prop : Continuous fun t : ℝ ↦ c * Complex.exp
        (((ω * t : ℝ) : ℂ) * Complex.I)).intervalIntegrable _ _
  have hre := Complex.reCLM.intervalIntegral_comp_comm hi
  simp only [Complex.reCLM_apply] at hre
  rw [hre, intervalIntegral.integral_const_mul, integral_exp_full_period ω L k h]
  split_ifs
  · simp [mul_comm]
  · simp

/-- For `a < t`, `∫ s in a..t, (2 * (t - a) ^ (-(1 / 2 : ℝ)) * (t - s) ^ (-(3 / 4 : ℝ)) + 2 * (t -
a) ^ (-(3 / 4 : ℝ)) * (s - a) ^ (-(1 / 2 : ℝ))) = 12 * ((t - a) ^ (1 / 4 : ℝ) * (t - a) ^ (-(1 / 2 :
ℝ)))`. The proof integrates the two power functions of `s` separately and combines the powers of
`t - a`. -/
theorem integral_rpow_sub_left_add_sub_right {a t : ℝ} (hat : a < t) :
    ∫ s in a..t, (2 * (t - a) ^ (-(1 / 2 : ℝ)) * (t - s) ^ (-(3 / 4 : ℝ)) +
        2 * (t - a) ^ (-(3 / 4 : ℝ)) * (s - a) ^ (-(1 / 2 : ℝ))) =
      12 * ((t - a) ^ (1 / 4 : ℝ) * (t - a) ^ (-(1 / 2 : ℝ))) := by
  have hw : 0 < t - a := sub_pos.2 hat
  have i1 := (intervalIntegrable_rpow_sub_left (a := a) (t := t) (r := -(3 / 4 : ℝ))
    (by norm_num)).const_mul (2 * (t - a) ^ (-(1 / 2 : ℝ)))
  have i2 := (intervalIntegrable_rpow_sub_right (a := a) (t := t) (r := -(1 / 2 : ℝ))
    (by norm_num)).const_mul (2 * (t - a) ^ (-(3 / 4 : ℝ)))
  rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_rpow_sub_left (r := -(3 / 4 : ℝ)) (by norm_num),
    integral_rpow_sub_right (r := -(1 / 2 : ℝ)) (by norm_num)]
  have q1 : (-(3 / 4 : ℝ) + 1) = 1 / 4 := by norm_num
  have q2 : (-(1 / 2 : ℝ) + 1) = 1 / 2 := by norm_num
  rw [q1, q2]
  have e2 : (t - a) ^ (-(3 / 4 : ℝ)) * (t - a) ^ (1 / 2 : ℝ) =
      (t - a) ^ (1 / 4 : ℝ) * (t - a) ^ (-(1 / 2 : ℝ)) := by
    rw [← rpow_add hw, ← rpow_add hw]
    norm_num
  linear_combination 4 * e2

/-- If `0 < h` and `g : ℝ → ℂ` is integrable on `Ioc 0 h`, then for every complex `F0`,
`-∫ z in 0..h, (g z * ((1 - z / h : ℝ) : ℂ) - (F0 + ∫ s in 0..z, g s) / (h : ℂ)) =
F0`. The proof uses `∫ z in 0..h, ∫ s in 0..z, g s = ∫ s in 0..h, g s * ((h - s : ℝ) :
ℂ)`, so that the terms containing `g` cancel and the constant term gives `F0`. -/
theorem neg_integral_mul_sub_primitive_div_eq {g : ℝ → ℂ} {h : ℝ} (hh : 0 < h) (F0 : ℂ)
    (hg : IntegrableOn g (Ioc 0 h)) :
    -∫ z in (0 : ℝ)..h, (g z * ((1 - z / h : ℝ) : ℂ) - (F0 + ∫ s in (0 : ℝ)..z, g s) / (h : ℂ))
      = F0 := by
  have hh0 : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hgi : IntervalIntegrable g volume 0 h :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hh.le).2 hg
  have hGc : ContinuousOn (fun z ↦ ∫ s in (0 : ℝ)..z, g s) (uIcc 0 h) :=
    intervalIntegral.continuousOn_primitive_interval (by
      rw [uIcc_of_le hh.le]
      exact (integrableOn_Icc_iff_integrableOn_Ioc).2 hg)
  have hGi : IntervalIntegrable (fun z ↦ ∫ s in (0 : ℝ)..z, g s) volume 0 h :=
    hGc.intervalIntegrable
  have hwi : IntervalIntegrable (fun z ↦ g z * ((h - z : ℝ) : ℂ)) volume 0 h :=
    hgi.mul_continuousOn (by fun_prop)
  have pt : ∀ z, g z * ((1 - z / h : ℝ) : ℂ) - (F0 + ∫ s in (0 : ℝ)..z, g s) / (h : ℂ)
      = (g z * ((h - z : ℝ) : ℂ) - ∫ s in (0 : ℝ)..z, g s) / (h : ℂ) - F0 / (h : ℂ) := by
    intro z
    push_cast
    field_simp
    ring
  simp_rw [pt]
  rw [intervalIntegral.integral_sub ((hwi.sub hGi).div_const _) intervalIntegrable_const,
    intervalIntegral.integral_div, intervalIntegral.integral_sub hwi hGi,
    integral_primitive_eq_integral_mul_sub hh hg, sub_self, zero_div,
        intervalIntegral.integral_const]
  simp only [sub_zero, Complex.real_smul]
  field_simp
  ring

/-- Let `a < b`, let `h : ℝ → ℂ` be such that `fun t ↦ ((t - a : ℝ) : ℂ) * h t` is integrable on
`Icc a b`, and suppose `u r = L - ∫ t in r..b, h t` for almost every `r` in `Icc a b`. Then for
every `C^1` function `ψ : ℝ → ℝ` with `ψ a = 0` and `ψ b = 0`,
`∫ r in Icc a b, (deriv ψ r : ℂ) * u r = -∫ r in Icc a b, (ψ r : ℂ) * h r`. The proof applies Fubini
to `deriv ψ r * h t` on the triangle `r < t`, which is integrable because its integral in `r` is
bounded by a constant times `(t - a) * ‖h t‖`. -/
theorem setIntegral_deriv_mul_eq_neg_of_weighted {a b : ℝ} (hab : a < b) (u h : ℝ → ℂ) (L : ℂ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hψa : ψ a = 0) (hψb : ψ b = 0)
    (hhw : IntegrableOn (fun t ↦ ((t - a : ℝ) : ℂ) * h t) (Icc a b))
    (hu : ∀ᵐ r ∂(volume.restrict (Icc a b)), u r = L - ∫ t in r..b, h t) :
    ∫ r in Icc a b, ((deriv ψ r : ℝ) : ℂ) * u r = -∫ r in Icc a b, ((ψ r : ℝ) : ℂ) * h r := by
  have hdc : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc a b) hdc.continuousOn
  have hhm : AEStronglyMeasurable h (volume.restrict (Icc a b)) := by
    have h1 : AEStronglyMeasurable (fun t ↦ ((t - a : ℝ) : ℂ)⁻¹ * (((t - a : ℝ) : ℂ) * h t))
        (volume.restrict (Icc a b)) :=
      ((Complex.measurable_ofReal.comp (measurable_id.sub_const a)).inv.aestronglyMeasurable).mul
          hhw.1
    refine h1.congr ?_
    have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ a := by
      rw [ae_iff]; simp
    filter_upwards [ae_restrict_of_ae hne] with t ht
    have : ((t - a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr ht
    field_simp
  set k : ℝ × ℝ → ℂ := Set.indicator {p : ℝ × ℝ | p.1 < p.2}
      (fun p ↦ ((deriv ψ p.1 : ℝ) : ℂ) * h p.2) with hk
  have hk_slice_t : ∀ t, (fun r ↦ k (r, t)) = Set.indicator (Iio t)
      (fun r ↦ ((deriv ψ r : ℝ) : ℂ) * h t) := by
    intro t; funext r; simp only [hk, Set.indicator, Set.mem_ofPred_eq, Set.mem_Iio]
  have hk_slice_r : ∀ r, (fun t ↦ k (r, t)) = Set.indicator (Ioi r)
      (fun t ↦ ((deriv ψ r : ℝ) : ℂ) * h t) := by
    intro r; funext t; simp only [hk, Set.indicator, Set.mem_ofPred_eq, Set.mem_Ioi]
  have hkm : AEStronglyMeasurable k ((volume.restrict (Icc a b)).prod
      (volume.restrict (Icc a b))) := by
    refine AEStronglyMeasurable.indicator ?_ (measurableSet_lt measurable_fst measurable_snd)
    exact ((Complex.continuous_ofReal.comp (hdc.comp continuous_fst)).aestronglyMeasurable).mul
        hhm.comp_snd
  have hwn : IntegrableOn (fun t ↦ (t - a) * ‖h t‖) (Icc a b) := by
    refine IntegrableOn.congr_fun hhw.norm (fun t ht ↦ ?_) measurableSet_Icc
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.1)]
  have hdi : IntegrableOn (fun r ↦ ((deriv ψ r : ℝ) : ℂ)) (Icc a b) :=
    (Complex.continuous_ofReal.comp hdc).integrableOn_Icc
  have hbound : ∀ t ∈ Icc a b, ∫ r, ‖k (r, t)‖ ∂(volume.restrict (Icc a b)) ≤ M *
      ((t - a) * ‖h t‖) := by
    intro t ht
    have e1 : (fun r ↦ ‖k (r, t)‖) = Set.indicator (Iio t)
        (fun r ↦ ‖((deriv ψ r : ℝ) : ℂ) * h t‖) := by
      funext r
      rw [show k (r, t) = _ from congrFun (hk_slice_t t) r]
      by_cases hr : r < t <;> simp [Set.indicator, hr]
    rw [e1, integral_indicator measurableSet_Iio]
    have hmem : ∀ᵐ r ∂((volume.restrict (Icc a b)).restrict (Iio t)), r ∈ Icc a b :=
      ae_restrict_of_ae (ae_restrict_mem measurableSet_Icc)
    calc ∫ r in Iio t, ‖((deriv ψ r : ℝ) : ℂ) * h t‖ ∂(volume.restrict (Icc a b))
        ≤ ∫ r in Iio t, M * ‖h t‖ ∂(volume.restrict (Icc a b)) := by
          refine integral_mono_ae ?_ (integrable_const _) ?_
          · refine Integrable.mono' (g := fun _ ↦ M * ‖h t‖) (integrable_const _) ?_ ?_
            · exact ((Complex.continuous_ofReal.comp hdc).mul
                  continuous_const).norm.aestronglyMeasurable
            · filter_upwards [hmem] with r hr
              rw [norm_norm, norm_mul, Complex.norm_real]
              exact mul_le_mul_of_nonneg_right (hM r hr) (norm_nonneg _)
          · filter_upwards [hmem] with r hr
            rw [norm_mul, Complex.norm_real]
            exact mul_le_mul_of_nonneg_right (hM r hr) (norm_nonneg _)
      _ = M * ((t - a) * ‖h t‖) := by
          have : Iio t ∩ Icc a b = Ico a t := by
            ext x; simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
            constructor
            · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
            · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith [ht.2]⟩
          rw [setIntegral_const, smul_eq_mul, Measure.real,
              Measure.restrict_apply measurableSet_Iio, this,
            Real.volume_Ico, ENNReal.toReal_ofReal (sub_nonneg.mpr ht.1)]
          ring
  have hkint : Integrable k ((volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))) := by
    rw [integrable_prod_iff' hkm]
    refine ⟨Eventually.of_forall fun t ↦ ?_, ?_⟩
    · rw [hk_slice_t]
      exact (hdi.mul_const (h t)).indicator measurableSet_Iio
    · refine Integrable.mono' (hwn.const_mul M) ?_ ?_
      · have := hkm.norm.prod_swap.integral_prod_right'
        exact this
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
        exact hbound t ht
  have hswap := integral_integral_swap (μ := volume.restrict (Icc a b))
      (ν := volume.restrict (Icc a b))
    (f := fun r t ↦ k (r, t)) hkint
  have hL : ∀ r ∈ Icc a b, ∫ t, k (r, t) ∂(volume.restrict (Icc a b)) =
      ((deriv ψ r : ℝ) : ℂ) * ∫ t in r..b, h t := by
    intro r hr
    have hs : Ioi r ∩ Icc a b = Ioc r b := by
      ext x; simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith [hr.1], h2⟩
    rw [hk_slice_r, integral_indicator measurableSet_Ioi,
        Measure.restrict_restrict measurableSet_Ioi, hs,
      integral_const_mul, intervalIntegral.integral_of_le hr.2]
  have hR : ∀ t ∈ Icc a b, ∫ r, k (r, t) ∂(volume.restrict (Icc a b)) = ((ψ t : ℝ) : ℂ) * h t := by
    intro t ht
    rw [hk_slice_t, integral_indicator measurableSet_Iio,
        Measure.restrict_restrict measurableSet_Iio,
      integral_mul_const]
    congr 1
    have : Iio t ∩ Icc a b = Ico a t := by
      ext x; simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith [ht.2]⟩
    rw [this, integral_complex_ofReal, setIntegral_Ico_deriv_eq_sub hψ ht.1, hψa, sub_zero]
  have h0 : ∫ r in Icc a b, ((deriv ψ r : ℝ) : ℂ) = 0 := by
    rw [integral_complex_ofReal, integral_Icc_eq_integral_Ico,
        setIntegral_Ico_deriv_eq_sub hψ hab.le, hψa, hψb]; simp
  have h0L : ∫ r in Icc a b, L * ((deriv ψ r : ℝ) : ℂ) = 0 := by
    rw [integral_const_mul]
    convert mul_zero L using 2
  calc ∫ r in Icc a b, ((deriv ψ r : ℝ) : ℂ) * u r
      = ∫ r in Icc a b, (L * ((deriv ψ r : ℝ) : ℂ) - ∫ t, k (r, t) ∂(volume.restrict (Icc a b))) :=
          by
        refine integral_congr_ae ?_
        filter_upwards [hu, ae_restrict_mem measurableSet_Icc] with r hr hr'
        rw [hr, hL r hr']; ring
    _ = -∫ t, ∫ r, k (r, t) ∂(volume.restrict (Icc a b)) ∂(volume.restrict (Icc a b)) := by
        rw [integral_sub (hdi.const_mul L) hkint.integral_prod_left, h0L, zero_sub, hswap]
    _ = -∫ r in Icc a b, ((ψ r : ℝ) : ℂ) * h r := by
        congr 1
        exact setIntegral_congr_fun measurableSet_Icc hR

/-- Let `a < b`, let `q : ℝ → ℂ` be integrable on `Icc a b`, and suppose
`u z = L - ∫ t in z..b, q t` for almost every `z` in `Icc a b`. Then for every `C^1` function
`f : ℝ → ℂ` with `f a = 0` and `f b = 0`,
`∫ z in Icc a b, u z * deriv f z = -∫ z in Icc a b, q z * f z`. The proof writes `u` as a constant
plus the primitive `fun z ↦ ∫ t in a..z, q t` and exchanges the order of integration. -/
theorem setIntegral_mul_deriv_eq_neg_of_primitive {a b : ℝ} (hab : a < b) {u q : ℝ → ℂ} {L : ℂ}
    (hq : IntegrableOn q (Icc a b))
    (hu : ∀ᵐ z ∂(volume.restrict (Icc a b)), u z = L - ∫ t in z..b, q t)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (ha : f a = 0) (hb : f b = 0) :
    ∫ z in Icc a b, u z * deriv f z = -∫ z in Icc a b, q z * f z := by
  have hdf : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hqi : ∀ c d, c ∈ Icc a b → d ∈ Icc a b → IntervalIntegrable q volume c d := fun c d hc hd ↦
    (hq.mono_set (uIcc_subset_Icc hc hd)).intervalIntegrable
  have hu' : ∀ᵐ z ∂(volume.restrict (Icc a b)), u z * deriv f z =
      (L - ∫ t in a..b, q t) * deriv f z + (∫ t in a..z, q t) * deriv f z := by
    filter_upwards [hu, ae_restrict_mem measurableSet_Icc] with z hz hzm
    rw [hz, ← intervalIntegral.integral_interval_sub_left
        (hqi a b ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩)
      (hqi a z ⟨le_rfl, hab.le⟩ hzm)]
    ring
  have hPc : ContinuousOn (fun z ↦ ∫ t in a..z, q t) (Icc a b) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (f := q) (a := a)
        (b := b)
      (by rw [uIcc_of_le hab.le]; exact hq)
    rwa [uIcc_of_le hab.le] at this
  have i1 : IntegrableOn (fun z ↦ (L - ∫ t in a..b, q t) * deriv f z) (Icc a b) :=
    (continuous_const.mul hdf).continuousOn.integrableOn_compact isCompact_Icc
  have i2 : IntegrableOn (fun z ↦ (∫ t in a..z, q t) * deriv f z) (Icc a b) :=
    (hPc.mul hdf.continuousOn).integrableOn_compact isCompact_Icc
  have hdiff : ∀ x ∈ uIcc a b, DifferentiableAt ℝ f x := fun x _ ↦
    (hf.differentiable one_ne_zero).differentiableAt
  have hI : ∫ z in Icc a b, deriv f z = 0 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le,
      intervalIntegral.integral_deriv_eq_sub' f rfl hdiff hdf.continuousOn, ha, hb, sub_zero]
  rw [integral_congr_ae hu', integral_add i1 i2, integral_const_mul, hI, mul_zero, zero_add,
    setIntegral_primitive_mul_eq_mul_primitive hq hdf, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Icc fun z hz ↦ ?_
  have hdz : ∀ x ∈ uIcc z b, DifferentiableAt ℝ f x := fun x _ ↦
    (hf.differentiable one_ne_zero).differentiableAt
  rw [intervalIntegral.integral_deriv_eq_sub' f rfl hdz hdf.continuousOn, hb]
  ring

/-- For real `a`, `b`, `A : ℝ → ℂ` integrable on `Icc a b` and a `C^1` function `h : ℝ → ℝ` with
`h b = 0`, `∫ z in Icc a b, (∫ u in a..z, A u) * (deriv h z : ℂ) = -∫ u in Icc a b, A u * (h u :
ℂ)`. The proof exchanges the order of integration and evaluates `∫ z in u..b, deriv h
z` by the fundamental theorem of calculus. -/
theorem setIntegral_primitive_mul_deriv_eq_neg {a b : ℝ} {A : ℝ → ℂ}
    (hA : IntegrableOn A (Icc a b))
    {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h) (hb : h b = 0) :
    ∫ z in Icc a b, (∫ u in a..z, A u) * ((deriv h z : ℝ) : ℂ) = -∫ u in Icc a b,
        A u * (h u : ℂ) := by
  have hd : Continuous (deriv h) := hh.continuous_deriv le_rfl
  rw [setIntegral_primitive_mul_eq_mul_primitive hA (k := fun z ↦ ((deriv h z : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp hd), ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Icc fun u hu ↦ ?_
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_deriv_eq_sub' h rfl
    (fun x _ ↦ (hh.differentiable one_ne_zero).differentiableAt) hd.continuousOn, hb]
  push_cast
  ring

/-- For a Lipschitz function `u : ℝ → ℂ` and real `A`, `o`, `a`, `b`,
`∫ r in a..b, (A * u r + ((r - o) * A) * deriv u r) = ((b - o) * A) * u b - ((a - o) * A) * u
a`, the real coefficients being cast to `ℂ`. This is the fundamental theorem of calculus for
`fun r ↦ ((r - o) * A) * u r`. -/
theorem integral_const_mul_add_sub_mul_deriv {u : ℝ → ℂ} {C : NNReal} (hu : LipschitzWith C u)
    (A o a b : ℝ) :
    ∫ r in a..b, (((A : ℝ) : ℂ) * u r + (((r - o) * A : ℝ) : ℂ) * deriv u r) =
      ((((b - o) * A : ℝ)) : ℂ) * u b - ((((a - o) * A : ℝ)) : ℂ) * u a := by
  apply Complex.ext
  · have := clm_integral_mul_add_sub_mul_deriv Complex.reCLM hu A o a b
    simp only [Complex.reCLM_apply] at this
    rw [this]; simp
  · have := clm_integral_mul_add_sub_mul_deriv Complex.imCLM hu A o a b
    simp only [Complex.imCLM_apply] at this
    rw [this]; simp

/-- For a Lipschitz function `u : ℝ → ℂ` and real `c`, `o`, `a`, `b`,
`∫ r in a..b, ((1 / (c - o)) * u r + ((r - o) / (c - o)) * deriv u r) = ((b - o) / (c - o)) * u b -
((a - o) / (c - o)) * u a`, the real coefficients being cast to `ℂ`. No hypothesis `c ≠
o` is assumed. -/
theorem integral_mul_add_sub_div_mul_deriv {u : ℝ → ℂ} {C : NNReal} (hu : LipschitzWith C u)
    (c o a b : ℝ) :
    ∫ r in a..b, ((((1 / (c - o) : ℝ)) : ℂ) * u r + (((r - o) / (c - o) : ℝ) : ℂ) * deriv u r) =
      ((((b - o) / (c - o) : ℝ)) : ℂ) * u b - ((((a - o) / (c - o) : ℝ)) : ℂ) * u a := by
  have h : ∀ r : ℝ, (r - o) / (c - o) = (r - o) * (1 / (c - o)) := fun r ↦ by ring
  simp_rw [h]
  exact integral_const_mul_add_sub_mul_deriv hu (1 / (c - o)) o a b

/-- Let `f : ℝ → Y` take values in a real normed space and let `0 ≤ u`. If `f` is continuous on the
open interval `(0, u)` and `‖f σ‖ ≤ K * (u - σ) ^ (-(3 / 4))` for every `σ` in it, then `f` is
interval integrable from `0` to `u`. The bound is integrable because `-(3 / 4) > -1`. -/
theorem intervalIntegrable_of_le_rpow_neg_three_quarters {Y : Type} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y]
    (f : ℝ → Y) {u K : ℝ} (hu : 0 ≤ u)
    (hc : ContinuousOn f (Ioo 0 u)) (hb : ∀ σ ∈ Ioo 0 u, ‖f σ‖ ≤ K * (u - σ) ^ (-(3 / 4 : ℝ))) :
    IntervalIntegrable f volume 0 u := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hu, integrableOn_Ioc_iff_integrableOn_Ioo]
  have h1 : IntervalIntegrable (fun x : ℝ ↦ x ^ (-(3 / 4 : ℝ))) volume 0 u :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h2 := (h1.comp_sub_left u).symm.const_mul K
  simp only [sub_zero, sub_self] at h2
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hu, integrableOn_Ioc_iff_integrableOn_Ioo] at h2
  exact h2.mono' (hc.aestronglyMeasurable measurableSet_Ioo)
    ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall hb))

/-- For every integer `j`, `∫ x in 0..2 * π, exp (j * I * x)` equals `2 * π` if `j = 0` and zero
otherwise. For `j ≠ 0` the antiderivative `exp (j * I * x) / (j * I)` takes the same value at
`0` and at `2 * π`. -/
theorem integral_exp_int_mul_I_mul (j : ℤ) :
    ∫ x in (0 : ℝ)..(2 * Real.pi), Complex.exp ((j : ℂ) * Complex.I * (x : ℂ)) =
      if j = 0 then 2 * (Real.pi : ℂ) else 0 := by
  split_ifs with hj
  · subst hj
    simp
  · have hc : (j : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hj) Complex.I_ne_zero
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp ((j : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [show (j : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ) = j * (2 * Real.pi * Complex.I) by
        push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I j
    rw [h1]
    simp

/-- If `f : ℝ → ℝ` is interval integrable from `0` to `2 * π` and `g : ℝ → ℂ` is continuous, then
`θ ↦ g θ * f θ`, with `f θ` seen in `ℂ`, is interval integrable from `0` to `2 * π`. -/
theorem intervalIntegrable_continuous_mul_ofReal {f : ℝ → ℝ} {g : ℝ → ℂ}
    (hf : IntervalIntegrable f volume 0 (2 * Real.pi))
    (hg : Continuous g) :
    IntervalIntegrable (fun θ ↦ g θ * (f θ : ℂ)) volume 0 (2 * Real.pi) := by
  have h : IntervalIntegrable (fun θ ↦ (f θ : ℂ)) volume 0 (2 * Real.pi) :=
      ⟨hf.1.ofReal, hf.2.ofReal⟩
  exact h.continuousOn_mul hg.continuousOn

/-- For every integer `n`, `∫ φ in 0..2 * π, exp (n * φ * I)` equals `2 * π` if `n = 0` and zero
otherwise. This is `integral_exp_int_mul_I_mul` with the exponent written `(n * φ) * I`. -/
theorem integral_exp_int_mul_mul_I (n : ℤ) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi), Complex.exp (((n * φ : ℝ) : ℂ) * Complex.I)
      = if n = 0 then (2 * Real.pi : ℂ) else 0 := by
  rw [← integral_exp_int_mul_I_mul n]
  refine intervalIntegral.integral_congr fun φ _ ↦ ?_
  push_cast
  ring_nf

/-- For every integer `n`, `∫ τ in 0..1, exp (2 * π * n * τ * I)` equals one if `n = 0` and zero
otherwise. For `n ≠ 0` the antiderivative takes the same value at `0` and at `1`. -/
theorem integral_exp_two_pi_mul_int_mul_mul_I (n : ℤ) :
    ∫ τ in (0 : ℝ)..1, Complex.exp (((2 * Real.pi * n * τ : ℝ) : ℂ) * Complex.I)
      = if n = 0 then (1 : ℂ) else 0 := by
  split_ifs with hn
  · subst hn
    simp
  · have hc : 2 * (Real.pi : ℂ) * n * Complex.I ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero))
        (Int.cast_ne_zero.2 hn)) Complex.I_ne_zero
    have e : (fun τ : ℝ ↦ Complex.exp (((2 * Real.pi * n * τ : ℝ) : ℂ) * Complex.I))
        = fun τ : ℝ ↦ Complex.exp (2 * (Real.pi : ℂ) * n * Complex.I * (τ : ℂ)) := by
      funext τ
      congr 1
      push_cast
      ring
    rw [e, integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * (Real.pi : ℂ) * n * Complex.I * ((1 : ℝ) : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I n]
      congr 1
      push_cast
      ring
    rw [h1]
    simp

/-- For all real `t` and `c`, the function `s ↦ (t - s) ^ (-(3 / 4))` is interval integrable from
`c` to `t`. -/
theorem intervalIntegrable_sub_rpow_neg_three_quarters (t c : ℝ) :
    IntervalIntegrable (fun s ↦ (t - s) ^ (-(3 / 4 : ℝ))) volume c t := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := t - c) (b := 0)
    (r := -(3 / 4 : ℝ)) (by norm_num)).comp_sub_left t
  simpa using h

/-- For every real `c`, `∫ r in 0..c, r ^ (-(3 / 4)) = 4 * c ^ (1 / 4)`, with real powers. -/
theorem integral_rpow_neg_three_quarters (c : ℝ) :
    ∫ r in (0 : ℝ)..c, r ^ (-(3 / 4 : ℝ)) = 4 * c ^ (1 / 4 : ℝ) := by
  rw [integral_rpow (Or.inl (by norm_num))]
  have e : (-(3 / 4 : ℝ)) + 1 = 1 / 4 := by norm_num
  rw [e, Real.zero_rpow (by norm_num)]
  ring

/-- For all real `t` and `m`, `∫ τ in m..t, (t - τ) ^ (-(3 / 4)) = 4 * (t - m) ^ (1 / 4)`, with real
powers. By the substitution `x = t - τ`. -/
theorem integral_sub_rpow_neg_three_quarters (t m : ℝ) :
    ∫ τ in m..t, (t - τ) ^ (-(3 / 4 : ℝ)) = 4 * (t - m) ^ (1 / 4 : ℝ) := by
  have h : ∫ τ in m..t, (t - τ) ^ (-(3 / 4 : ℝ)) = ∫ x in t - t..t - m, x ^ (-(3 / 4 : ℝ)) :=
    intervalIntegral.integral_comp_sub_left (fun x : ℝ ↦ x ^ (-(3 / 4 : ℝ))) t
  rw [h, integral_rpow (Or.inl (by norm_num)), sub_self]
  have e : (-(3 / 4 : ℝ)) + 1 = 1 / 4 := by norm_num
  rw [e, Real.zero_rpow (by norm_num)]
  ring

end PDE.Analysis
