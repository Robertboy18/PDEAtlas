/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.PSeries

/-!
# A weight that is closed under convolution

## Motivation

Which bound on the Taylor coefficients of a function survives products and powers without
losing a constant at every step?

## The idea

A geometric bound `c βʲ` does not: the `j`-th coefficient of a square is a sum of `j + 1`
products, so the bound picks up a factor `j + 1`. The weight `ψ j = 1 / (16 (j + 1)²)` repairs
this. In a product of indices `a + b = j` one of `a + 1`, `b + 1` is at least `(j + 2)/2`, which
pays for the factor `(j + 1)²`, and the remaining sum `∑ 1/(i + 1)²` is at most `2`. So
`∑_{a + b = j} ψ a ψ b ≤ ψ j`, and a power series with zero constant term whose coefficients
are at most `c βʲ ψ j` has `m`-th power, `m ≥ 1`, with coefficients at most `cᵐ βʲ ψ j`.

## Main results

* `sum_antidiagonal_convolutionWeight_mul_le`: `∑_{a + b = j} ψ a ψ b ≤ ψ j`, for all `j`.
* `coeff_pow_le_convolutionWeight`: for all real power series `p` with zero constant term and
  nonnegative coefficients, all `c ≥ 0`, `β ≥ 0` and all `m ≥ 1`, a bound `c βʲ ψ j` on the
  coefficients of index `1 ≤ j ≤ N` gives the bound `cᵐ βʲ ψ j` on the coefficients of `pᵐ` of
  index `j ≤ N`, and also of index `N + 1` when `m ≥ 2`.

## Relations

`convolutionWeight_mul_le` (`ψ a ψ b ≤ ψ (a + b)`) is one term of the first result. The second
result is used with `PDE.iteratedCoordinateNorm_comp_le` to bound derivatives of compositions.
The majorants of `PDE.Analysis.Analytic.PowerSeries.Majorization` compare two series
coefficientwise; here one side is an explicit weight.

## What stays open

The constant `16` is not optimal.
-/

@[expose] public noncomputable section

open Finset
open PowerSeries (coeff)

namespace PDE.Analysis

/-- The weight `ψ j = 1 / (16 (j + 1)²)`. Its convolution with itself is at most itself
(`sum_antidiagonal_convolutionWeight_mul_le`). -/
def convolutionWeight (j : ℕ) : ℝ := 1 / (16 * ((j : ℝ) + 1) ^ 2)

/-- The convolution weight is positive. -/
theorem convolutionWeight_pos (j : ℕ) : 0 < convolutionWeight j := by
  unfold convolutionWeight
  positivity

/-- The convolution weight is at most `1`. -/
theorem convolutionWeight_le_one (j : ℕ) : convolutionWeight j ≤ 1 := by
  unfold convolutionWeight
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  rw [div_le_one (by positivity)]
  nlinarith

/-- The convolution weight decreases. -/
theorem convolutionWeight_succ_le (j : ℕ) : convolutionWeight (j + 1) ≤ convolutionWeight j := by
  unfold convolutionWeight
  push_cast
  gcongr
  linarith

/-- The convolution weight is antitone. -/
theorem convolutionWeight_antitone : Antitone convolutionWeight :=
  antitone_nat_of_succ_le convolutionWeight_succ_le

/-- One step down costs at most a factor `4`: `ψ j ≤ 4 ψ (j + 1)`. -/
theorem convolutionWeight_le_four_mul_succ (j : ℕ) :
    convolutionWeight j ≤ 4 * convolutionWeight (j + 1) := by
  unfold convolutionWeight
  push_cast
  rw [div_le_iff₀ (by positivity)]
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  field_simp
  nlinarith

/-- For `j ≥ 1` one step down costs at most a factor `9/4`: `ψ j ≤ (9/4) ψ (j + 1)`. -/
theorem convolutionWeight_le_mul_succ {j : ℕ} (hj : 1 ≤ j) :
    convolutionWeight j ≤ 9 / 4 * convolutionWeight (j + 1) := by
  unfold convolutionWeight
  push_cast
  rw [div_le_iff₀ (by positivity)]
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  field_simp
  nlinarith

/-- The partial sums of `∑ 1/(i + 1)²` are at most `2`. This is Mathlib's `sum_Ioo_inv_sq_le`
with the index shifted by one. -/
theorem sum_range_inv_succ_sq_le_two (k : ℕ) :
    ∑ i ∈ range (k + 1), 1 / ((i : ℝ) + 1) ^ 2 ≤ 2 := by
  have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (k + 2)
  have e : ∑ i ∈ range (k + 1), 1 / ((i : ℝ) + 1) ^ 2 = ∑ j ∈ Ioo 0 (k + 2), ((j : ℝ) ^ 2)⁻¹ := by
    refine Finset.sum_nbij' (fun i ↦ i + 1) (fun j ↦ j - 1) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      simp only [mem_range] at hi
      simp only [mem_Ioo]
      omega
    · intro j hj
      simp only [mem_Ioo] at hj
      simp only [mem_range]
      omega
    · intro i _
      omega
    · intro j hj
      simp only [mem_Ioo] at hj
      omega
    · intro i _
      push_cast
      rw [one_div]
  rw [e]
  simpa using h

/-- **The weight is closed under convolution**: `∑_{a + b = j} ψ a ψ b ≤ ψ j`. -/
theorem sum_antidiagonal_convolutionWeight_mul_le (j : ℕ) :
    ∑ ab ∈ antidiagonal j, convolutionWeight ab.1 * convolutionWeight ab.2 ≤
      convolutionWeight j := by
  -- one of the two indices is at least half of `j`
  have hterm (ab : ℕ × ℕ) (hab : ab ∈ antidiagonal j) :
      convolutionWeight ab.1 * convolutionWeight ab.2 ≤
        1 / (64 * ((j : ℝ) + 1) ^ 2) *
          (1 / ((ab.1 : ℝ) + 1) ^ 2 + 1 / ((ab.2 : ℝ) + 1) ^ 2) := by
    have hj : (j : ℝ) = ab.1 + ab.2 := by exact_mod_cast (mem_antidiagonal.mp hab).symm
    have ha : (0 : ℝ) ≤ ab.1 := Nat.cast_nonneg _
    have hb : (0 : ℝ) ≤ ab.2 := Nat.cast_nonneg _
    unfold convolutionWeight
    rw [hj, div_mul_div_comm, one_mul, div_add_div _ _ (by positivity) (by positivity),
      div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg ha hb, sq_nonneg ((ab.1 : ℝ) - ab.2),
      mul_pos (by positivity : (0 : ℝ) < ((ab.1 : ℝ) + 1) ^ 2)
        (by positivity : (0 : ℝ) < ((ab.2 : ℝ) + 1) ^ 2)]
  have hsum : ∑ ab ∈ antidiagonal j, (1 / ((ab.1 : ℝ) + 1) ^ 2 + 1 / ((ab.2 : ℝ) + 1) ^ 2) =
      2 * ∑ i ∈ range (j + 1), 1 / ((i : ℝ) + 1) ^ 2 := by
    rw [sum_add_distrib, two_mul]
    congr 1
    · exact Nat.sum_antidiagonal_eq_sum_range_succ (fun a _ ↦ 1 / ((a : ℝ) + 1) ^ 2) j
    · rw [← Nat.sum_antidiagonal_swap]
      exact Nat.sum_antidiagonal_eq_sum_range_succ (fun a _ ↦ 1 / ((a : ℝ) + 1) ^ 2) j
  calc ∑ ab ∈ antidiagonal j, convolutionWeight ab.1 * convolutionWeight ab.2
      ≤ ∑ ab ∈ antidiagonal j, 1 / (64 * ((j : ℝ) + 1) ^ 2) *
          (1 / ((ab.1 : ℝ) + 1) ^ 2 + 1 / ((ab.2 : ℝ) + 1) ^ 2) := sum_le_sum hterm
    _ = 1 / (64 * ((j : ℝ) + 1) ^ 2) * (2 * ∑ i ∈ range (j + 1), 1 / ((i : ℝ) + 1) ^ 2) := by
        rw [← mul_sum, hsum]
    _ ≤ 1 / (64 * ((j : ℝ) + 1) ^ 2) * (2 * 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (sum_range_inv_succ_sq_le_two j) zero_le_two)
          (by positivity)
    _ = convolutionWeight j := by
        unfold convolutionWeight
        field_simp
        ring

/-- The weight is submultiplicative: `ψ a ψ b ≤ ψ (a + b)`. -/
theorem convolutionWeight_mul_le (a b : ℕ) :
    convolutionWeight a * convolutionWeight b ≤ convolutionWeight (a + b) := by
  have hmem : (a, b) ∈ antidiagonal (a + b) := mem_antidiagonal.mpr rfl
  have h := single_le_sum (s := antidiagonal (a + b))
    (f := fun ab : ℕ × ℕ ↦ convolutionWeight ab.1 * convolutionWeight ab.2)
    (fun ab _ ↦ mul_nonneg (convolutionWeight_pos ab.1).le (convolutionWeight_pos ab.2).le)
    (a := (a, b)) hmem
  exact h.trans (sum_antidiagonal_convolutionWeight_mul_le (a + b))

-- From here on the weight is used only through the lemmas above.
attribute [irreducible] convolutionWeight

/-- **Powers of a weighted series.** Let `p` be a real power series with zero constant term and
nonnegative coefficients, and suppose `[tʲ] p ≤ c βʲ ψ j` for `1 ≤ j ≤ N`. Then
`[tʲ] pᵐ ≤ cᵐ βʲ ψ j` for all `m ≥ 1` and `j ≤ N`, and also for `j = N + 1` when `m ≥ 2`: a
product of at least two factors of total index `N + 1` only sees indices up to `N`. -/
theorem coeff_pow_le_convolutionWeight {p : PowerSeries ℝ} (hp0 : coeff 0 p = 0)
    (hp : ∀ j, 0 ≤ coeff j p) {c β : ℝ} (hc : 0 ≤ c) (hβ : 0 ≤ β) {N : ℕ}
    (hN : ∀ j, 1 ≤ j → j ≤ N → coeff j p ≤ c * β ^ j * convolutionWeight j)
    {m : ℕ} (hm : 1 ≤ m) {j : ℕ} (hj : j ≤ N ∨ j = N + 1 ∧ 2 ≤ m) :
    coeff j (p ^ m) ≤ c ^ m * β ^ j * convolutionWeight j := by
  -- the coefficients of `p` of index at most `N` obey the bound, the constant one included
  have hN0 : ∀ j, j ≤ N → coeff j p ≤ c * β ^ j * convolutionWeight j := by
    intro j hjN
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · rw [hp0]
      exact mul_nonneg (mul_nonneg hc (pow_nonneg hβ _)) (convolutionWeight_pos _).le
    · exact hN j hpos hjN
  have hpow0 : ∀ m, 1 ≤ m → coeff 0 (p ^ m) = 0 := by
    intro m hm
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hp0, zero_pow (by omega)]
  -- the bound for indices at most `N`, by induction on the power
  have hle : ∀ m, 1 ≤ m → ∀ j, j ≤ N → coeff j (p ^ m) ≤ c ^ m * β ^ j * convolutionWeight j := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => intro j hjN; simpa using hN0 j hjN
    | succ m hm ih =>
      intro j hjN
      rw [pow_succ, PowerSeries.coeff_mul]
      calc ∑ ab ∈ antidiagonal j, coeff ab.1 (p ^ m) * coeff ab.2 p
          ≤ ∑ ab ∈ antidiagonal j, c ^ (m + 1) * β ^ j *
              (convolutionWeight ab.1 * convolutionWeight ab.2) := by
            refine sum_le_sum fun ab hab ↦ ?_
            have hsum : ab.1 + ab.2 = j := mem_antidiagonal.mp hab
            calc coeff ab.1 (p ^ m) * coeff ab.2 p
                ≤ (c ^ m * β ^ ab.1 * convolutionWeight ab.1) *
                    (c * β ^ ab.2 * convolutionWeight ab.2) :=
                  mul_le_mul (ih ab.1 (by omega)) (hN0 ab.2 (by omega)) (hp _)
                    (mul_nonneg (mul_nonneg (pow_nonneg hc _) (pow_nonneg hβ _))
                      (convolutionWeight_pos _).le)
              _ = c ^ (m + 1) * β ^ j * (convolutionWeight ab.1 * convolutionWeight ab.2) := by
                  rw [← hsum, pow_add, pow_succ]; ring
        _ = c ^ (m + 1) * β ^ j *
              ∑ ab ∈ antidiagonal j, convolutionWeight ab.1 * convolutionWeight ab.2 := by
            rw [mul_sum]
        _ ≤ c ^ (m + 1) * β ^ j * convolutionWeight j :=
            mul_le_mul_of_nonneg_left (sum_antidiagonal_convolutionWeight_mul_le j)
              (mul_nonneg (pow_nonneg hc _) (pow_nonneg hβ _))
  rcases hj with hjN | ⟨rfl, hm2⟩
  · exact hle m hm j hjN
  -- index `N + 1` with at least two factors: both factors have index at most `N`
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hm1 : 1 ≤ m := by omega
  rw [pow_succ, PowerSeries.coeff_mul]
  calc ∑ ab ∈ antidiagonal (N + 1), coeff ab.1 (p ^ m) * coeff ab.2 p
      ≤ ∑ ab ∈ antidiagonal (N + 1), c ^ (m + 1) * β ^ (N + 1) *
          (convolutionWeight ab.1 * convolutionWeight ab.2) := by
        refine sum_le_sum fun ab hab ↦ ?_
        have hsum : ab.1 + ab.2 = N + 1 := mem_antidiagonal.mp hab
        have hnn : 0 ≤ c ^ (m + 1) * β ^ (N + 1) *
            (convolutionWeight ab.1 * convolutionWeight ab.2) :=
          mul_nonneg (mul_nonneg (pow_nonneg hc _) (pow_nonneg hβ _))
            (mul_nonneg (convolutionWeight_pos _).le (convolutionWeight_pos _).le)
        rcases Nat.eq_zero_or_pos ab.1 with h1 | h1
        · rw [h1, hpow0 m hm1, zero_mul]; rwa [h1] at hnn
        rcases Nat.eq_zero_or_pos ab.2 with h2 | h2
        · rw [h2, hp0, mul_zero]; rwa [h2] at hnn
        calc coeff ab.1 (p ^ m) * coeff ab.2 p
            ≤ (c ^ m * β ^ ab.1 * convolutionWeight ab.1) *
                (c * β ^ ab.2 * convolutionWeight ab.2) :=
              mul_le_mul (hle m hm1 ab.1 (by omega)) (hN0 ab.2 (by omega)) (hp _)
                (mul_nonneg (mul_nonneg (pow_nonneg hc _) (pow_nonneg hβ _))
                  (convolutionWeight_pos _).le)
          _ = c ^ (m + 1) * β ^ (N + 1) *
                (convolutionWeight ab.1 * convolutionWeight ab.2) := by
              rw [← hsum, pow_add, pow_succ]; ring
    _ = c ^ (m + 1) * β ^ (N + 1) *
          ∑ ab ∈ antidiagonal (N + 1), convolutionWeight ab.1 * convolutionWeight ab.2 := by
        rw [mul_sum]
    _ ≤ c ^ (m + 1) * β ^ (N + 1) * convolutionWeight (N + 1) :=
        mul_le_mul_of_nonneg_left (sum_antidiagonal_convolutionWeight_mul_le (N + 1))
          (mul_nonneg (pow_nonneg hc _) (pow_nonneg hβ _))

end PDE.Analysis
