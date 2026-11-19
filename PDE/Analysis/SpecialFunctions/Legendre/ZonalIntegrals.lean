/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Legendre.VectorHarmonics
public import CAS.Polynomial.CoefficientList
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Exact integrals of products of zonal harmonics and trigonometric modes

The zonal harmonic `S_l (θ) = P_l (cos θ)`, its polar derivative `S_l' (θ) = -sin θ P_l' (cos θ)`
and the modes `cos (n θ) = T_n (cos θ)`, `sin ((n + 1) θ) = sin θ U_n (cos θ)` are powers of
`sin θ` times polynomials in `cos θ`. Their rational coefficient lists are computable:
`legendreCoeffs l` (from the coefficients `(-1)^k C(l, k) C(l + k, l)` of the shifted Legendre
polynomial in `(1 - x) / 2`), `coeffDeriv` of it, and `chebyshevTCoeffs n`, `chebyshevUCoeffs n`
(the three-term recurrences).

A product `sin θ ^ N · p (cos θ)` integrates against `sin θ` exactly: for even `N` the factor
`sin θ ^ N = (1 - cos² θ) ^ (N / 2)` is a polynomial in `cos θ` and the integral is the rational
`∫₋₁¹ p (x) (1 - x²) ^ (N / 2) dx`; for odd `N` it is `π` times the rational
`∫₀^π p (cos θ) (1 - cos² θ) ^ ((N + 1) / 2) dθ / π` (`integral_sin_pow_mul_coeffEval_cos`).
-/

@[expose] public section

namespace PDE.Analysis.SpecialFunctions

open CAS.Analysis.SpecialFunctions
open Polynomial Set
open CAS.Polynomial
open scoped BigOperators

/-- The polynomial `∑ₖ cₖ ((1 - x) / 2) ^ k` from the coefficients `c` in `(1 - x) / 2`. -/
def coeffHornerHalfReflect : List ℚ → List ℚ
  | [] => []
  | c :: l => coeffAdd [c] (coeffMul [1 / 2, -1 / 2] (coeffHornerHalfReflect l))

theorem coeffEval_coeffHornerHalfReflect (l : List ℚ) (x : ℝ) :
    coeffEval (coeffHornerHalfReflect l) x =
      ∑ k ∈ Finset.range l.length, (l.getD k 0 : ℝ) * ((1 - x) / 2) ^ k := by
  induction l with
  | nil => simp [coeffHornerHalfReflect]
  | cons c l ih =>
    rw [coeffHornerHalfReflect, coeffEval_coeffAdd, coeffEval_coeffMul, ih, List.length_cons,
      Finset.sum_range_succ']
    simp only [coeffEval_cons, coeffEval_nil, List.getD_cons_zero, List.getD_cons_succ,
      pow_succ, pow_zero, ← mul_assoc, ← Finset.sum_mul]
    push_cast
    ring

/-- The coefficients of the Legendre polynomial `P_l`. -/
def legendreCoeffs (l : ℕ) : List ℚ :=
  coeffHornerHalfReflect ((List.range (l + 1)).map fun k ↦
    ((-1) ^ k * (l.choose k : ℤ) * ((l + k).choose l : ℤ) : ℤ))

theorem coeffEval_legendreCoeffs (l : ℕ) (x : ℝ) :
    coeffEval (legendreCoeffs l) x = (legendre l).eval x := by
  rw [legendreCoeffs, coeffEval_coeffHornerHalfReflect, legendre_eval,
    aeval_eq_sum_range' (n := l + 1) (by simp), List.length_map, List.length_range]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' := Finset.mem_range.mp hk
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk', Option.map_some,
    Option.getD_some, coeff_shiftedLegendre, zsmul_eq_mul]
  push_cast
  ring

/-- The coefficients of the derivative `P_l'`. -/
def legendreDerivCoeffs (l : ℕ) : List ℚ := coeffDeriv (legendreCoeffs l)

theorem coeffEval_legendreDerivCoeffs (l : ℕ) (x : ℝ) :
    coeffEval (legendreDerivCoeffs l) x = (derivative (legendre l)).eval x := by
  have h1 := hasDerivAt_coeffEval (legendreCoeffs l) x
  have heq : coeffEval (legendreCoeffs l) = fun y ↦ (legendre l).eval y :=
    funext fun y ↦ coeffEval_legendreCoeffs l y
  rw [heq] at h1
  exact h1.unique ((legendre l).hasDerivAt x)

/-- `S_l (θ) = P_l (cos θ)` through the coefficient list. -/
theorem zonalHarmonic_eq_coeffEval (l : ℕ) (θ : ℝ) :
    zonalHarmonic l θ = coeffEval (legendreCoeffs l) (Real.cos θ) :=
  (coeffEval_legendreCoeffs l _).symm

/-- `S_l' (θ) = -sin θ P_l' (cos θ)` through the coefficient list. -/
theorem zonalHarmonicDeriv_eq_coeffEval (l : ℕ) (θ : ℝ) :
    zonalHarmonicDeriv l θ =
      Real.sin θ * coeffEval (coeffScale (-1) (legendreDerivCoeffs l)) (Real.cos θ) := by
  rw [zonalHarmonicDeriv, coeffEval_coeffScale, coeffEval_legendreDerivCoeffs]
  push_cast
  ring

/-- The coefficient lists of the Chebyshev polynomials `(T_n, T_{n+1})`. -/
def chebyshevTPair : ℕ → List ℚ × List ℚ
  | 0 => ([1], [0, 1])
  | n + 1 =>
    let p := chebyshevTPair n
    (p.2, coeffAdd (0 :: coeffScale 2 p.2) (coeffScale (-1) p.1))

/-- The coefficients of the Chebyshev polynomial `T_n` with `T_n (cos θ) = cos (n θ)`. -/
def chebyshevTCoeffs (n : ℕ) : List ℚ := (chebyshevTPair n).1

theorem coeffEval_chebyshevTPair (n : ℕ) (θ : ℝ) :
    coeffEval (chebyshevTPair n).1 (Real.cos θ) = Real.cos (n * θ) ∧
      coeffEval (chebyshevTPair n).2 (Real.cos θ) = Real.cos ((n + 1) * θ) := by
  induction n with
  | zero => simp [chebyshevTPair]
  | succ n ih =>
    refine ⟨?_, ?_⟩
    · change coeffEval (chebyshevTPair n).2 (Real.cos θ) = _
      push_cast
      exact ih.2
    simp only [chebyshevTPair, coeffEval_coeffAdd, coeffEval_cons, coeffEval_coeffScale, ih.1,
      ih.2]
    push_cast
    have h1 : Real.cos ((n + 1 + 1) * θ) = Real.cos ((n + 1) * θ + θ) := by ring_nf
    have h2 : Real.cos (n * θ) = Real.cos ((n + 1) * θ - θ) := by ring_nf
    rw [h1, h2, Real.cos_add, Real.cos_sub]
    ring

theorem coeffEval_chebyshevTCoeffs (n : ℕ) (θ : ℝ) :
    coeffEval (chebyshevTCoeffs n) (Real.cos θ) = Real.cos (n * θ) :=
  (coeffEval_chebyshevTPair n θ).1

/-- The coefficient lists of the Chebyshev polynomials `(U_n, U_{n+1})`. -/
def chebyshevUPair : ℕ → List ℚ × List ℚ
  | 0 => ([1], [0, 2])
  | n + 1 =>
    let p := chebyshevUPair n
    (p.2, coeffAdd (0 :: coeffScale 2 p.2) (coeffScale (-1) p.1))

/-- The coefficients of the Chebyshev polynomial `U_n` with `sin θ U_n (cos θ) = sin ((n+1) θ)`. -/
def chebyshevUCoeffs (n : ℕ) : List ℚ := (chebyshevUPair n).1

theorem coeffEval_chebyshevUPair (n : ℕ) (θ : ℝ) :
    Real.sin θ * coeffEval (chebyshevUPair n).1 (Real.cos θ) = Real.sin ((n + 1) * θ) ∧
      Real.sin θ * coeffEval (chebyshevUPair n).2 (Real.cos θ) = Real.sin ((n + 2) * θ) := by
  induction n with
  | zero =>
    simp only [chebyshevUPair, coeffEval_cons, coeffEval_nil]
    push_cast
    refine ⟨by ring_nf, ?_⟩
    rw [show (0 + 2 : ℝ) * θ = 2 * θ by ring, Real.sin_two_mul]
    ring
  | succ n ih =>
    refine ⟨?_, ?_⟩
    · change Real.sin θ * coeffEval (chebyshevUPair n).2 (Real.cos θ) = _
      rw [ih.2]
      push_cast
      ring_nf
    simp only [chebyshevUPair, coeffEval_coeffAdd, coeffEval_cons, coeffEval_coeffScale]
    push_cast
    have e : Real.sin θ * ((0 : ℝ) + Real.cos θ * (2 * coeffEval (chebyshevUPair n).2
        (Real.cos θ)) + -1 * coeffEval (chebyshevUPair n).1 (Real.cos θ)) =
        2 * Real.cos θ * (Real.sin θ * coeffEval (chebyshevUPair n).2 (Real.cos θ)) -
          Real.sin θ * coeffEval (chebyshevUPair n).1 (Real.cos θ) := by ring
    rw [e, ih.1, ih.2]
    have h1 : Real.sin ((n + 1 + 2) * θ) = Real.sin ((n + 2) * θ + θ) := by ring_nf
    have h2 : Real.sin ((n + 1) * θ) = Real.sin ((n + 2) * θ - θ) := by ring_nf
    rw [h1, h2, Real.sin_add, Real.sin_sub]
    ring

theorem sin_mul_coeffEval_chebyshevUCoeffs (n : ℕ) (θ : ℝ) :
    Real.sin θ * coeffEval (chebyshevUCoeffs n) (Real.cos θ) = Real.sin ((n + 1) * θ) :=
  (coeffEval_chebyshevUPair n θ).1

/-- The coefficients of `1 - x²`, the square of the sine as a polynomial in the cosine. -/
def sinSqCoeffs : List ℚ := [1, 0, -1]

theorem coeffEval_sinSqCoeffs_cos (θ : ℝ) :
    coeffEval sinSqCoeffs (Real.cos θ) = Real.sin θ ^ 2 := by
  simp only [sinSqCoeffs, coeffEval_cons, coeffEval_nil]
  push_cast
  linear_combination -(Real.sin_sq_add_cos_sq θ)

/-- The exact integral of `sin θ ^ N p (cos θ)` against `sin θ` on `(0, π)`: a rational for even
`N`, `π` times a rational for odd `N`. -/
def sinPowCoeffIntegral (N : ℕ) (l : List ℚ) : ℚ :=
  if N % 2 = 0 then coeffIntegralFrom 0 (coeffMul l (coeffPow sinSqCoeffs (N / 2)))
  else coeffCosIntegralFrom 0 (coeffMul l (coeffPow sinSqCoeffs ((N + 1) / 2)))

/-- `∫₀^π sin θ ^ N p (cos θ) sin θ dθ` is `sinPowCoeffIntegral N l` for even `N` and `π` times it
for odd `N`. -/
theorem integral_sin_pow_mul_coeffEval_cos (N : ℕ) (l : List ℚ) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ N * coeffEval l (Real.cos θ) * Real.sin θ =
      (if N % 2 = 0 then 1 else Real.pi) * sinPowCoeffIntegral N l := by
  rcases Nat.mod_two_eq_zero_or_one N with h | h
  · obtain ⟨m, rfl⟩ : ∃ m, N = 2 * m := ⟨N / 2, by omega⟩
    have hm : 2 * m / 2 = m := by omega
    simp only [sinPowCoeffIntegral, h, ↓reduceIte, hm, one_mul]
    rw [← integral_coeffEval_cos_mul_sin]
    refine intervalIntegral.integral_congr fun θ _ ↦ ?_
    simp only [coeffEval_coeffMul, coeffEval_coeffPow, coeffEval_sinSqCoeffs_cos, pow_mul]
    ring
  · obtain ⟨m, rfl⟩ : ∃ m, N = 2 * m + 1 := ⟨N / 2, by omega⟩
    have hm : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    have hne : ¬ (2 * m + 1) % 2 = 0 := by omega
    simp only [sinPowCoeffIntegral, hne, ↓reduceIte, hm]
    rw [← integral_coeffEval_cos]
    refine intervalIntegral.integral_congr fun θ _ ↦ ?_
    simp only [coeffEval_coeffMul, coeffEval_coeffPow, coeffEval_sinSqCoeffs_cos]
    ring

end PDE.Analysis.SpecialFunctions
