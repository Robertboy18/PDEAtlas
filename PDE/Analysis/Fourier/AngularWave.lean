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

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import PDE.Analysis.Complex.Definitions

set_option linter.style.header false

/-!
# The angular wave `exp (i κ θ)`: products and integrals over a period

The product of two waves is the wave of the sum of the frequencies, the integral of a wave over a
period is zero unless the frequency is zero, and the real part of a multiple of a wave is the half
sum of the multiple and its conjugate. Together they give the integral over a period of a product of
two such real parts. The proofs reduce to `Complex.exp_add` and to the integral of the complex
exponential.

## Main results

* `PDE.Analysis.integral_angularWave_eq_zero`: For an integer `k ≠ 0`, the integral of
  `angularWave k` over `[0, 2 π]` is zero.
* `PDE.Analysis.integral_re_mul_angularWave_mul_re`: For complex `A`, `B` and integers `n₁, n₂ ≥ 0`,
  the integral over `[-π, π]` of `Re (A * angularWave n₁ θ) * Re (B * angularWave n₂ θ)` is zero for
  `n₁ ≠ n₂`, `2 π * (Re A * Re B)` for `n₁ = n₂ = 0`, and `π * Re (A * conj B)` for `n₁ = n₂ ≠ 0`.
* `PDE.Analysis.angularWave_mul_angularWave`: The product of two angular waves is the wave of the
  sum of the frequencies: `angularWave n θ * angularWave n' θ = angularWave (n + n') θ`.
* `PDE.Analysis.integral_angularWave_neg_pi_pi`: The integral of `angularWave n` over `[-π, π]` is
  `2 π` for `n = 0` and zero for every other integer `n`.
* `PDE.Analysis.ofReal_re_mul_angularWave`: The real part of `A * angularWave n θ`, as a complex
  number, is `(A * angularWave n θ + conj A * angularWave (-n) θ) / 2`.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace PDE.Analysis

/-- The product of two angular waves is the wave of the sum of the frequencies:
`angularWave n θ * angularWave n' θ = angularWave (n + n') θ`. -/
theorem angularWave_mul_angularWave (n n' : ℤ) (θ : ℝ) :
    angularWave n θ * angularWave n' θ = angularWave (n + n') θ := by
  unfold angularWave
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- For an integer `k ≠ 0`, the integral of `angularWave k` over `[0, 2 π]` is zero. -/
theorem integral_angularWave_eq_zero (k : ℤ) (hk : k ≠ 0) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), angularWave k θ = 0 := by
  have hc : ((k : ℂ) * Complex.I) ≠ 0 := mul_ne_zero (by exact_mod_cast hk) Complex.I_ne_zero
  have e : ∀ θ : ℝ, angularWave k θ = Complex.exp (((k : ℂ) * Complex.I) * θ) := fun θ ↦ by
    unfold angularWave
    push_cast
    ring_nf
  simp_rw [e]
  rw [integral_exp_mul_complex hc]
  have h1 : Complex.exp ((k : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
    rw [← Complex.exp_int_mul_two_pi_mul_I k]
    congr 1
    push_cast
    ring
  rw [h1]
  simp

/-- The integral of `angularWave n` over `[-π, π]` is `2 π` for `n = 0` and zero for every other
integer `n`. -/
theorem integral_angularWave_neg_pi_pi (n : ℤ) :
    ∫ θ in (-Real.pi)..Real.pi, angularWave n θ = if n = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  split_ifs with hn
  · subst hn
    simp [angularWave]
    ring
  · have hc : (n : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hn) Complex.I_ne_zero
    have hf : angularWave n = fun θ : ℝ ↦ Complex.exp ((n : ℂ) * Complex.I * θ) := by
      funext θ
      unfold angularWave
      push_cast
      ring_nf
    rw [hf, integral_exp_mul_complex hc]
    have h2 : Complex.exp ((n : ℂ) * Complex.I * (Real.pi : ℝ)) =
        Complex.exp ((n : ℂ) * Complex.I * ((-Real.pi : ℝ) : ℂ)) := by
      rw [show (n : ℂ) * Complex.I * (Real.pi : ℝ) = (n : ℂ) * Complex.I * ((-Real.pi : ℝ) : ℂ) +
          n * (2 * Real.pi * Complex.I) by
        push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [h2, sub_self, zero_div]

/-- The real part of `A * angularWave n θ`, as a complex number, is
`(A * angularWave n θ + conj A * angularWave (-n) θ) / 2`. -/
theorem ofReal_re_mul_angularWave (A : ℂ) (n : ℤ) (θ : ℝ) :
    (((A * angularWave n θ).re : ℝ) : ℂ) = (A * angularWave n θ + (starRingEnd ℂ) A *
        angularWave (-n) θ) / 2 := by
  rw [Complex.re_eq_add_conj, map_mul, conj_angularWave]

/-- For complex `A`, `B` and integers `n₁, n₂ ≥ 0`, the integral over `[-π, π]` of
`Re (A * angularWave n₁ θ) * Re (B * angularWave n₂ θ)` is zero for `n₁ ≠ n₂`, `2 π * (Re A * Re B)`
for `n₁ = n₂ = 0`, and `π * Re (A * conj B)` for `n₁ = n₂ ≠ 0`. -/
theorem integral_re_mul_angularWave_mul_re (A B : ℂ) (n₁ n₂ : ℤ) (hp1 : 0 ≤ n₁) (hp2 : 0 ≤ n₂) :
    ∫ θ in (-Real.pi)..Real.pi, (A * angularWave n₁ θ).re * (B * angularWave n₂ θ).re =
    if n₁ = n₂ then (if n₁ = 0 then 2 * Real.pi * (A.re * B.re) else Real.pi *
        (A * (starRingEnd ℂ) B).re)
    else 0 := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have hpt : (fun θ : ℝ ↦ (((A * angularWave n₁ θ).re * (B * angularWave n₂ θ).re : ℝ) : ℂ)) =
      fun θ ↦
      (A * B / 4) * angularWave (n₁ + n₂) θ + (A * (starRingEnd ℂ) B / 4) *
          angularWave (n₁ + -n₂) θ +
        ((starRingEnd ℂ) A * B / 4) * angularWave (-n₁ + n₂) θ +
        ((starRingEnd ℂ) A * (starRingEnd ℂ) B / 4) * angularWave (-n₁ + -n₂) θ := by
    funext θ
    rw [Complex.ofReal_mul, ofReal_re_mul_angularWave, ofReal_re_mul_angularWave,
        ← angularWave_mul_angularWave, ← angularWave_mul_angularWave,
            ← angularWave_mul_angularWave, ← angularWave_mul_angularWave]
    ring
  have hi : ∀ (c : ℂ) (n : ℤ), IntervalIntegrable (fun θ ↦ c * angularWave n θ) volume
      (-Real.pi) Real.pi :=
    fun c n ↦ (continuous_const.mul (continuous_angularWave n)).intervalIntegrable _ _
  rw [hpt, intervalIntegral.integral_add (((hi _ _).add (hi _ _)).add (hi _ _)) (hi _ _),
    intervalIntegral.integral_add ((hi _ _).add (hi _ _)) (hi _ _),
    intervalIntegral.integral_add (hi _ _) (hi _ _)]
  simp only [intervalIntegral.integral_const_mul, integral_angularWave_neg_pi_pi]
  by_cases h12 : n₁ = n₂
  · subst h12
    by_cases h0 : n₁ = 0
    · subst h0
      simp only [add_zero, neg_zero, ite_true]
      apply Complex.ext <;> simp <;> ring
    · rw [ite_eq_right (by
        omega : n₁ + n₁ ≠ 0), ite_eq_left (by
          omega : n₁ + -n₁ = 0), ite_eq_left (by omega : -n₁ + n₁ = 0),
        ite_eq_right (by omega : -n₁ + -n₁ ≠ 0), ite_eq_left rfl, ite_eq_right h0]
      apply Complex.ext <;> simp <;> ring
  · rw [ite_eq_right (by
      omega : n₁ + n₂ ≠ 0), ite_eq_right (by
        omega : n₁ + -n₂ ≠ 0), ite_eq_right (by omega : -n₁ + n₂ ≠ 0),
      ite_eq_right (by omega : -n₁ + -n₂ ≠ 0), ite_eq_right h12]
    simp

end PDE.Analysis
