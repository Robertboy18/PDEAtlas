/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Legendre.CosineSeries
public import Mathlib.Data.Nat.Choose.Central

/-!
# Integer numerators of the Legendre cosine coefficients

The normalized double factorial is a central binomial coefficient over a power of four,
`(2n choose n) / 4 ^ n` (`halfCentralBinomial_eq`), so the coefficient of `cos (2jθ)` in
`P_{2N} (cos θ)` is the integer `c_j (2(N+j) choose N+j) (2(N-j) choose N-j)`, with `c_0 = 1` and
`c_j = 2` otherwise, over `2 ^ (4N)` (`evenCosineCoefficient_eq_centralBinom`). Certificates read
the coefficients through these numerators; `centralBinomRec` computes the central binomial
coefficients by the recurrence `(n + 1) C(n + 1) = 2 (2n + 1) C(n)` with natural-number
operations only (`centralBinomRec_eq`).
-/

@[expose] public section

namespace PDE.Analysis

/-- The normalized double factorial is the central binomial coefficient over `4 ^ n`. -/
theorem halfCentralBinomial_eq (n : ℕ) :
    halfCentralBinomial n = (Nat.centralBinom n : ℚ) / 4 ^ n := by
  induction n with
  | zero => simp [halfCentralBinomial]
  | succ n ih =>
    have h := Nat.succ_mul_centralBinom_succ n
    have h' : ((n : ℚ) + 1) * (Nat.centralBinom (n + 1) : ℚ) =
        2 * (2 * n + 1) * (Nat.centralBinom n : ℚ) := by exact_mod_cast h
    rw [halfCentralBinomial_succ, ih]
    have hn : (n : ℚ) + 1 ≠ 0 := by positivity
    have hcb : (Nat.centralBinom (n + 1) : ℚ) =
        2 * (2 * n + 1) * (Nat.centralBinom n : ℚ) / ((n : ℚ) + 1) := by
      rw [eq_div_iff hn, mul_comm]
      exact h'
    rw [hcb]
    field_simp
    ring

/-- The coefficient of `cos (2jθ)` in `P_{2N} (cos θ)` as an integer over `2 ^ (4N)`. -/
theorem evenCosineCoefficient_eq_centralBinom (N j : ℕ) :
    evenCosineCoefficient N j = if j ≤ N then
      ((if j = 0 then 1 else 2) * Nat.centralBinom (N + j) * Nat.centralBinom (N - j) : ℚ) /
        2 ^ (4 * N) else 0 := by
  unfold evenCosineCoefficient
  by_cases hj : j ≤ N
  · simp only [hj, ↓reduceIte, halfCentralBinomial_eq]
    have h4 : (4 : ℚ) ^ (N + j) * 4 ^ (N - j) = 2 ^ (4 * N) := by
      rw [← pow_add, show N + j + (N - j) = 2 * N by omega, show (4 : ℚ) = 2 ^ 2 by norm_num,
        ← pow_mul]
      ring_nf
    rw [← h4]
    field_simp
  · simp only [hj, ↓reduceIte]

/-- The central binomial coefficients by the recurrence `(n + 1) C(n + 1) = 2 (2n + 1) C(n)`,
with natural-number operations only. -/
def centralBinomRec : ℕ → ℕ
  | 0 => 1
  | n + 1 => Nat.div (Nat.mul (Nat.mul 2 (Nat.add (Nat.mul 2 n) 1)) (centralBinomRec n))
      (Nat.add n 1)

theorem centralBinomRec_eq (n : ℕ) : centralBinomRec n = Nat.centralBinom n := by
  induction n with
  | zero => simp [centralBinomRec]
  | succ n ih =>
    have h := Nat.succ_mul_centralBinom_succ n
    simp only [centralBinomRec, ih, Nat.mul_eq, Nat.add_eq]
    rw [← h]
    exact Nat.mul_div_cancel_left _ (Nat.succ_pos n)

end PDE.Analysis
