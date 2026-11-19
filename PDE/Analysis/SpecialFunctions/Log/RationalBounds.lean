/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import PDE.Analysis.Scalar.RationalRounding

/-!
# Rational bounds of the logarithm near `1`

For `x ≥ 1`, `2 (x - 1)/(x + 1) ≤ log x ≤ (x - 1/x)/2` (`two_mul_sub_div_add_le_log`,
`log_le_half_sub_inv`). Both bounds are exact to third order at `x = 1`: writing `x = e^t`, they
read `2 tanh (t/2) ≤ t ≤ sinh t`.

For full precision, `log ((1 + y)/(1 - y)) = ∑ 2 y^(2k+1)/(2k+1)` is enclosed between its partial
sums and the partial sums plus the geometric tail `2 y^(2n+1)/((2n+1)(1 - y²))`
(`sum_le_log_div`, `log_div_le_sum_add`). The rational bounds `logLow x ≤ log x ≤ logHigh x`
(`logLow_le`, `le_logHigh`) write `x = 2^j m`, evaluate the series at `y = (m - 1)/(m + 1)` rounded
outward, and take `log 2` from the series at `y = 1/3`.

## Main definitions

* `logSeriesRat`: the partial sum `∑_{k<n} 2 y^(2k+1)/(2k+1)` over the rationals.
* `logTwoLow`: a rational lower bound of `log 2`; `logTwoHigh` is an upper bound.
* `logLow`: a rational lower bound of `log x` for `x > 0`; `logHigh` is an upper bound.

## Main results

* `two_mul_sub_div_add_le_log`: `2 (x - 1)/(x + 1) ≤ log x` for `x ≥ 1`.
* `log_le_half_sub_inv`: `log x ≤ (x - 1/x)/2` for `x ≥ 1`.
* `sum_le_log_div`: the partial sums of `∑ 2 y^(2k+1)/(2k+1)` are lower bounds of
  `log ((1 + y)/(1 - y))` for `0 ≤ y < 1`.
* `log_div_le_sum_add`: the tail after `n` terms is at most `2 y^(2n+1)/((2n+1)(1 - y²))`.
* `logTwoLow_le`: `logTwoLow ≤ log 2`, and `log 2 ≤ logTwoHigh` (`le_logTwoHigh`).
* `logLow_le`: `logLow x ≤ log x` for `x > 0`.
* `le_logHigh`: `log x ≤ logHigh x` for `x > 0`.
-/

@[expose] public section

namespace Real

/-- `log x ≤ (x - 1/x)/2` for `x ≥ 1`. -/
theorem log_le_half_sub_inv {x : ℝ} (hx : 1 ≤ x) : log x ≤ (x - x⁻¹) / 2 := by
  have hx0 : 0 < x := by linarith
  have h := self_le_sinh_iff.2 (log_nonneg hx)
  rw [sinh_eq, exp_log hx0, exp_neg, exp_log hx0] at h
  exact h

/-- `2 (x - 1)/(x + 1) ≤ log x` for `x ≥ 1`. -/
theorem two_mul_sub_div_add_le_log {x : ℝ} (hx : 1 ≤ x) : 2 * (x - 1) / (x + 1) ≤ log x := by
  set u := (x - 1) / (x + 1)
  have hx1 : 0 < x + 1 := by linarith
  have hu0 : 0 ≤ u := div_nonneg (by linarith) hx1.le
  have hu1 : u < 1 := by rw [div_lt_one hx1]; linarith
  have hs := hasSum_log_sub_log_of_abs_lt_one (show |u| < 1 by rwa [abs_of_nonneg hu0])
  have h0 : (2 : ℝ) * (1 / (2 * (0 : ℕ) + 1)) * u ^ (2 * 0 + 1) ≤
      log (1 + u) - log (1 - u) :=
    le_hasSum hs 0 fun k _ ↦ by positivity
  have hlog : log (1 + u) - log (1 - u) = log x := by
    rw [← log_div (by linarith) (by linarith)]
    congr 1
    simp only [u]
    field_simp
    ring
  rw [hlog] at h0
  simpa [u, mul_div_assoc] using h0

/-- The partial sums of `log ((1 + y)/(1 - y)) = ∑ 2 y^(2k+1)/(2k+1)` are lower bounds for
`0 ≤ y < 1`. -/
theorem sum_le_log_div {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) (n : ℕ) :
    ∑ k ∈ Finset.range n, 2 * (1 / (2 * (k : ℝ) + 1)) * y ^ (2 * k + 1) ≤
      log ((1 + y) / (1 - y)) := by
  have hs := hasSum_log_sub_log_of_abs_lt_one (show |y| < 1 by rwa [abs_of_nonneg h0])
  rw [log_div (by linarith) (by linarith)]
  exact sum_le_hasSum (Finset.range n) (fun k _ ↦ by positivity) hs

/-- The tail of `∑ 2 y^(2k+1)/(2k+1)` after `n` terms is at most
`2 y^(2n+1)/((2n+1)(1 - y²))` for `0 ≤ y < 1`. -/
theorem log_div_le_sum_add {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) (n : ℕ) :
    log ((1 + y) / (1 - y)) ≤
      ∑ k ∈ Finset.range n, 2 * (1 / (2 * (k : ℝ) + 1)) * y ^ (2 * k + 1) +
        2 * y ^ (2 * n + 1) / ((2 * n + 1) * (1 - y ^ 2)) := by
  have hs := hasSum_log_sub_log_of_abs_lt_one (show |y| < 1 by rwa [abs_of_nonneg h0])
  rw [log_div (by linarith) (by linarith)]
  set f : ℕ → ℝ := fun k ↦ 2 * (1 / (2 * (k : ℝ) + 1)) * y ^ (2 * k + 1)
  have hy2 : y ^ 2 < 1 := by nlinarith
  have hy20 : 0 ≤ y ^ 2 := sq_nonneg y
  have hg : HasSum (fun i : ℕ ↦ 2 * y ^ (2 * n + 1) / (2 * n + 1) * (y ^ 2) ^ i)
      (2 * y ^ (2 * n + 1) / (2 * n + 1) * (1 - y ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one hy20 hy2).mul_left _
  have htail : HasSum (fun i ↦ f (i + n)) (log (1 + y) - log (1 - y) -
      ∑ k ∈ Finset.range n, f k) := (hasSum_nat_add_iff' n).2 hs
  have hle : ∀ i, f (i + n) ≤ 2 * y ^ (2 * n + 1) / (2 * n + 1) * (y ^ 2) ^ i := by
    intro i
    simp only [f]
    have hp : y ^ (2 * (i + n) + 1) = y ^ (2 * n + 1) * (y ^ 2) ^ i := by
      rw [← pow_mul, ← pow_add]
      ring_nf
    have hd : 1 / (2 * ((i + n : ℕ) : ℝ) + 1) ≤ 1 / (2 * (n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    rw [hp]
    have : 0 ≤ y ^ (2 * n + 1) * (y ^ 2) ^ i := by positivity
    calc 2 * (1 / (2 * ((i + n : ℕ) : ℝ) + 1)) * (y ^ (2 * n + 1) * (y ^ 2) ^ i)
        ≤ 2 * (1 / (2 * (n : ℝ) + 1)) * (y ^ (2 * n + 1) * (y ^ 2) ^ i) := by gcongr
      _ = _ := by ring
  have := hasSum_le hle htail hg
  have e : 2 * y ^ (2 * n + 1) / (2 * n + 1) * (1 - y ^ 2)⁻¹ =
      2 * y ^ (2 * n + 1) / ((2 * n + 1) * (1 - y ^ 2)) := by
    field_simp
  linarith

/-- `log ((1 + y)/(1 - y))` is monotone on `(-1, 1)`. -/
theorem log_div_le_log_div {y y' : ℝ} (h : -1 < y) (hy : y ≤ y') (h' : y' < 1) :
    log ((1 + y) / (1 - y)) ≤ log ((1 + y') / (1 - y')) := by
  refine log_le_log (div_pos (by linarith) (by linarith)) ?_
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

end Real

namespace PDE.Analysis

open FloatLib.Numerics.Enclosure (logScale)

/-- The partial sum `∑_{k<n} 2 y^(2k+1)/(2k+1)` over the rationals. -/
def logSeriesRat (n : ℕ) (y : ℚ) : ℚ :=
  ∑ k ∈ Finset.range n, 2 * (1 / (2 * (k : ℚ) + 1)) * y ^ (2 * k + 1)

/-- The real cast of `logSeriesRat n y` is the partial sum `∑_{k<n} 2 y^(2k+1)/(2k+1)` at the real
`y`. -/
theorem cast_logSeriesRat (n : ℕ) (y : ℚ) :
    ((logSeriesRat n y : ℚ) : ℝ) =
      ∑ k ∈ Finset.range n, 2 * (1 / (2 * (k : ℝ) + 1)) * (y : ℝ) ^ (2 * k + 1) := by
  simp only [logSeriesRat]
  push_cast
  rfl

/-- The tail bound `2 y^(2n+1)/((2n+1)(1 - y²))` over the rationals. -/
def logTailRat (n : ℕ) (y : ℚ) : ℚ := 2 * y ^ (2 * n + 1) / ((2 * n + 1) * (1 - y ^ 2))

/-- The number of terms for about fifty bits at `0 ≤ y ≤ 1/3`. -/
def logTerms (y : ℚ) : ℕ :=
  if y ≤ 1 / 1024 then 4 else if y ≤ 1 / 16 then 7 else if y ≤ 1 / 4 then 13 else 18

/-- A rational lower bound of `log 2`. -/
def logTwoLow : ℚ := logSeriesRat 24 (1 / 3)

/-- A rational upper bound of `log 2`. -/
def logTwoHigh : ℚ := logSeriesRat 24 (1 / 3) + logTailRat 24 (1 / 3)

/-- `log 2 = log ((1 + y)/(1 - y))` at `y = 1/3`. -/
theorem log_two_eq : Real.log 2 = Real.log ((1 + 1 / 3) / (1 - 1 / 3)) := by norm_num

/-- `logTwoLow ≤ log 2`. -/
theorem logTwoLow_le : (logTwoLow : ℝ) ≤ Real.log 2 := by
  have h := Real.sum_le_log_div (y := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 24
  rw [log_two_eq, logTwoLow, cast_logSeriesRat]
  push_cast
  exact h

/-- `log 2 ≤ logTwoHigh`. -/
theorem le_logTwoHigh : Real.log 2 ≤ (logTwoHigh : ℝ) := by
  have h := Real.log_div_le_sum_add (y := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 24
  rw [log_two_eq, logTwoHigh, Rat.cast_add, cast_logSeriesRat]
  simp only [logTailRat]
  push_cast
  exact h

/-- The lower bound of `log x` for `x ≥ 1`: `j log 2 + log m` with `m = x / 2^j`, the logarithm
of `m` from the series at `y = (m - 1)/(m + 1)` rounded down. -/
def logReducedLow (x : ℚ) : ℚ :=
  let j := logScale x
  let m := x / (2 : ℚ) ^ j
  let y := roundDownRel ((m - 1) / (m + 1))
  if 0 ≤ y then j * logTwoLow + logSeriesRat (logTerms y) y else 0

/-- The upper bound of `log x` for `x ≥ 1`, with `y` rounded up. -/
def logReducedHigh (x : ℚ) : ℚ :=
  let j := logScale x
  let m := x / (2 : ℚ) ^ j
  let y := roundUpRel ((m - 1) / (m + 1))
  if 0 ≤ y ∧ y < 1 then j * logTwoHigh + logSeriesRat (logTerms y) y + logTailRat (logTerms y) y
  else x - 1

/-- `log x = j log 2 + log ((1 + y)/(1 - y))` with `m = x / 2^j` and `y = (m - 1)/(m + 1)`. -/
theorem log_eq_reduced {x : ℚ} (hx : 0 < x) (j : ℕ) :
    Real.log x = j * Real.log 2 + Real.log ((1 + (((x / 2 ^ j - 1) / (x / 2 ^ j + 1) : ℚ) : ℝ)) /
      (1 - (((x / 2 ^ j - 1) / (x / 2 ^ j + 1) : ℚ) : ℝ))) := by
  have hx' : (0 : ℝ) < x := by exact_mod_cast hx
  have hm : (0 : ℝ) < x / 2 ^ j := by positivity
  have e : (1 + (((x / 2 ^ j - 1) / (x / 2 ^ j + 1) : ℚ) : ℝ)) /
      (1 - (((x / 2 ^ j - 1) / (x / 2 ^ j + 1) : ℚ) : ℝ)) = (x : ℝ) / 2 ^ j := by
    push_cast
    field_simp
    ring
  rw [e, Real.log_div hx'.ne' (by positivity), Real.log_pow]
  ring

/-- For `x ≥ 1`, `logReducedLow x ≤ log x`. -/
theorem logReducedLow_le {x : ℚ} (hx : 1 ≤ x) : (logReducedLow x : ℝ) ≤ Real.log x := by
  have hx0 : 0 < x := by linarith
  have hx' : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have key := log_eq_reduced hx0 (logScale x)
  unfold logReducedLow
  set j := logScale x
  set yq : ℚ := (x / 2 ^ j - 1) / (x / 2 ^ j + 1)
  dsimp only
  split_ifs with hy
  · have hm : 0 < x / 2 ^ j := by positivity
    have hyq1 : yq < 1 := by
      simp only [yq]
      rw [div_lt_one (by linarith)]
      linarith
    have hy' : (0 : ℝ) ≤ roundDownRel yq := Rat.cast_nonneg.2 hy
    have hr' : (roundDownRel yq : ℝ) ≤ yq := by exact_mod_cast roundDownRel_le yq
    have hyq1' : (yq : ℝ) < 1 := by exact_mod_cast hyq1
    have h1 := Real.sum_le_log_div hy' (hr'.trans_lt hyq1') (logTerms (roundDownRel yq))
    have h2 := Real.log_div_le_log_div (by linarith) hr' hyq1'
    have h3 : (j : ℝ) * logTwoLow ≤ j * Real.log 2 :=
      mul_le_mul_of_nonneg_left logTwoLow_le (Nat.cast_nonneg j)
    rw [key, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, cast_logSeriesRat]
    linarith
  · push_cast
    exact Real.log_nonneg hx'

/-- For `x ≥ 1`, `log x ≤ logReducedHigh x`. -/
theorem le_logReducedHigh {x : ℚ} (hx : 1 ≤ x) : Real.log x ≤ (logReducedHigh x : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hx' : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have key := log_eq_reduced hx0 (logScale x)
  unfold logReducedHigh
  set j := logScale x
  set yq : ℚ := (x / 2 ^ j - 1) / (x / 2 ^ j + 1)
  dsimp only
  split_ifs with hy
  · have hm : 0 < x / 2 ^ j := by positivity
    have hyq0 : -1 < yq := by
      simp only [yq]
      rw [lt_div_iff₀ (by linarith)]
      linarith
    have hy0 : (0 : ℝ) ≤ roundUpRel yq := Rat.cast_nonneg.2 hy.1
    have hy1 : (roundUpRel yq : ℝ) < 1 := by
      have h := (Rat.cast_lt (K := ℝ)).2 hy.2
      rwa [Rat.cast_one] at h
    have hr' : (yq : ℝ) ≤ roundUpRel yq := by exact_mod_cast le_roundUpRel yq
    have hyq0' : (-1 : ℝ) < yq := by exact_mod_cast hyq0
    have h1 := Real.log_div_le_sum_add hy0 hy1 (logTerms (roundUpRel yq))
    have h2 := Real.log_div_le_log_div hyq0' hr' hy1
    have h3 : (j : ℝ) * Real.log 2 ≤ j * logTwoHigh :=
      mul_le_mul_of_nonneg_left le_logTwoHigh (Nat.cast_nonneg j)
    rw [key, Rat.cast_add, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, cast_logSeriesRat]
    simp only [logTailRat]
    push_cast
    linarith
  · push_cast
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < x by linarith)]

/-- A rational lower bound of `log x` for `x > 0`. -/
def logLow (x : ℚ) : ℚ := if 1 ≤ x then logReducedLow x else -logReducedHigh x⁻¹

/-- A rational upper bound of `log x` for `x > 0`. -/
def logHigh (x : ℚ) : ℚ := if 1 ≤ x then logReducedHigh x else -logReducedLow x⁻¹

/-- For `x > 0`, `logLow x ≤ log x`. -/
theorem logLow_le {x : ℚ} (hx : 0 < x) : (logLow x : ℝ) ≤ Real.log x := by
  unfold logLow
  split_ifs with h
  · exact logReducedLow_le h
  · have h1 : 1 ≤ x⁻¹ := (one_le_inv₀ hx).2 (not_le.1 h).le
    have := le_logReducedHigh h1
    push_cast at this ⊢
    rw [Real.log_inv] at this
    linarith

/-- For `x > 0`, `log x ≤ logHigh x`. -/
theorem le_logHigh {x : ℚ} (hx : 0 < x) : Real.log x ≤ (logHigh x : ℝ) := by
  unfold logHigh
  split_ifs with h
  · exact le_logReducedHigh h
  · have h1 : 1 ≤ x⁻¹ := (one_le_inv₀ hx).2 (not_le.1 h).le
    have := logReducedLow_le h1
    push_cast at this ⊢
    rw [Real.log_inv] at this
    linarith

end PDE.Analysis
