/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Legendre.CosineSeriesInteger

/-!
# Integer cosine coefficients of the Legendre polynomials

With `halfCentralBinomial n = C(2n, n) / 4 ^ n` (`halfCentralBinomial_eq`), the cosine
coefficients of `P_l (cos θ)` of both parities become natural numbers after multiplication by
`4 ^ l`:
`4 ^ (2N) · evenCosineCoefficient N j = (1 or 2) C(2(N + j), N + j) C(2(N - j), N - j)` and
`4 ^ (2N + 1) · oddCosineCoefficient N j = 2 C(2(N + j + 1), N + j + 1) C(2(N - j), N - j)`
(`evenCosineInt`, `oddCosineInt` with `evenCosineCoefficient_eq`, `oddCosineCoefficient_eq`).
Products of such series can so be computed in natural-number arithmetic.
-/

@[expose] public section

namespace PDE.Analysis

open Nat

/-- The integer `4 ^ (2N)` times the coefficient of `cos (2jθ)` in `P_{2N} (cos θ)`. -/
def evenCosineInt (N j : ℕ) : ℕ :=
  if j ≤ N then (if j = 0 then 1 else 2) * centralBinom (N + j) * centralBinom (N - j) else 0

/-- The integer `4 ^ (2N + 1)` times the coefficient of `cos ((2j + 1)θ)` in
`P_{2N+1} (cos θ)`. -/
def oddCosineInt (N j : ℕ) : ℕ :=
  if j ≤ N then 2 * centralBinom (N + j + 1) * centralBinom (N - j) else 0

theorem evenCosineCoefficient_eq (N j : ℕ) :
    evenCosineCoefficient N j = (evenCosineInt N j : ℚ) / 4 ^ (2 * N) := by
  unfold evenCosineCoefficient evenCosineInt
  split_ifs with h h0
  · rw [halfCentralBinomial_eq, halfCentralBinomial_eq]
    subst h0
    push_cast
    simp only [Nat.add_zero, Nat.sub_zero, one_mul]
    rw [show 2 * N = N + N by ring, pow_add]
    field_simp
  · rw [halfCentralBinomial_eq, halfCentralBinomial_eq]
    push_cast
    have h4 : (4 : ℚ) ^ (2 * N) = 4 ^ (N + j) * 4 ^ (N - j) := by
      rw [← pow_add]; congr 1; omega
    rw [h4]
    field_simp
  · simp

theorem oddCosineCoefficient_eq (N j : ℕ) :
    oddCosineCoefficient N j = (oddCosineInt N j : ℚ) / 4 ^ (2 * N + 1) := by
  unfold oddCosineCoefficient oddCosineInt
  split_ifs with h
  · rw [halfCentralBinomial_eq, halfCentralBinomial_eq]
    push_cast
    have h4 : (4 : ℚ) ^ (2 * N + 1) = 4 ^ (N + j + 1) * 4 ^ (N - j) := by
      rw [← pow_add]; congr 1; omega
    rw [h4]
    field_simp
  · simp

end PDE.Analysis
