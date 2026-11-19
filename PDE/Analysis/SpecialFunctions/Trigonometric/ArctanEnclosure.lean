/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.SpecialFunctions.Trigonometric.ArctanSeriesBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import PDE.Analysis.Scalar.RationalRounding

/-!
# Rational enclosures of the arctangent

`atanLow n x ≤ arctan x ≤ atanHigh n x` for rationals `x` (`atanLow_le`, `le_atanHigh`), from
`n` terms of the arctangent series with its remainder (`Real.abs_arctan_sub_arctanPartialSum_le`).
Negative arguments are reflected by oddness; for `x ≥ 0` the reductions
`arctan x = π/2 - arctan (1/x)` for `x ≥ 2` and `arctan x = π/4 + arctan ((x - 1)/(x + 1))` for
`1/2 < x < 2` make the series run at arguments of size at most `1/2`. The constant `π` enters
through twenty-digit bounds.
`atanLowAt` and `atanHighAt` first round the argument outward to the grid `2^-64`, and `atanPair`
to about fifty significant bits with a number of terms adapted to the size of the argument, which
keeps the rationals small.

## Main definitions

* `atanLow`: a rational lower bound of `arctan x` from `n` terms of the series after the argument
  reduction; `atanHigh` is the upper bound.
* `atanLowAt`: `atanLow` at the argument rounded down to the grid `2^-64`; `atanHighAt` rounds up.
* `atanPair`: both bounds, at the outward roundings of `x` to about fifty bits.

## Main results

* `abs_arctan_sub_arctanPartialSum_le'`: `|arctan x - S_n(x)| ≤ |x|^(2n+1)/(2n+1)` for every real
  `x`.
* `arctan_eq_pi_div_four_add`: `arctan x = π/4 + arctan ((x - 1)/(x + 1))` for `x > -1`.
* `atanLow_le`: `atanLow n x ≤ arctan x` for every rational `x`.
* `le_atanHigh`: `arctan x ≤ atanHigh n x` for every rational `x`.
* `atanLowAt_le`: `atanLowAt n x ≤ arctan x`, and `arctan x ≤ atanHighAt n x` (`le_atanHighAt`).
* `atanPair_fst_le`: `(atanPair x).1 ≤ arctan x`, and `arctan x ≤ (atanPair x).2`
  (`le_atanPair_snd`).
-/

@[expose] public section

open Real FloatLib.Numerics.Enclosure
open CAS.Continuum.RationalInterval (piLower piUpper piLower_le_pi pi_le_piUpper)

namespace PDE.Analysis

/-- The arctangent partial sums are odd: `S_n(-x) = -S_n(x)`. -/
theorem arctanPartialSum_neg (n : ℕ) (x : ℝ) :
    arctanPartialSum n (-x) = -arctanPartialSum n x := by
  simp only [arctanPartialSum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Odd.neg_pow ⟨k, rfl⟩]
  ring

/-- The series bound for every real `x`: `|arctan x - S_n(x)| ≤ |x|^(2n+1)/(2n+1)`. -/
theorem abs_arctan_sub_arctanPartialSum_le' (x : ℝ) (n : ℕ) :
    |arctan x - arctanPartialSum n x| ≤ |x| ^ (2 * n + 1) / (2 * n + 1) := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact abs_arctan_sub_arctanPartialSum_le hx n
  · have h := abs_arctan_sub_arctanPartialSum_le (neg_nonneg.2 hx) n
    rw [arctan_neg, arctanPartialSum_neg, ← abs_neg] at h
    rw [abs_of_nonpos hx]
    convert h using 2
    ring

/-- The series lower bound `S_n(x) - |x|^(2n+1)/(2n+1)`. -/
def atanSeriesLow (n : ℕ) (x : ℚ) : ℚ := atanTaylor x n - |x| ^ (2 * n + 1) / (2 * n + 1)

/-- The series upper bound `S_n(x) + |x|^(2n+1)/(2n+1)`. -/
def atanSeriesHigh (n : ℕ) (x : ℚ) : ℚ := atanTaylor x n + |x| ^ (2 * n + 1) / (2 * n + 1)

/-- `atanSeriesLow n x ≤ arctan x` for every rational `x`. -/
theorem atanSeriesLow_le (n : ℕ) (x : ℚ) : (atanSeriesLow n x : ℝ) ≤ arctan x := by
  have h := abs_arctan_sub_arctanPartialSum_le' (x : ℝ) n
  rw [abs_le] at h
  simp only [atanSeriesLow]
  push_cast
  rw [cast_atanTaylor]
  unfold arctanPartialSum at h
  linarith [h.2]

/-- `arctan x ≤ atanSeriesHigh n x` for every rational `x`. -/
theorem le_atanSeriesHigh (n : ℕ) (x : ℚ) : arctan x ≤ (atanSeriesHigh n x : ℝ) := by
  have h := abs_arctan_sub_arctanPartialSum_le' (x : ℝ) n
  rw [abs_le] at h
  simp only [atanSeriesHigh]
  push_cast
  rw [cast_atanTaylor]
  unfold arctanPartialSum at h
  linarith [h.1]

/-- `arctan x = π/4 + arctan ((x - 1)/(x + 1))` for `x > -1`. -/
theorem arctan_eq_pi_div_four_add {x : ℝ} (hx : -1 < x) :
    arctan x = π / 4 + arctan ((x - 1) / (x + 1)) := by
  have hx1 : 0 < x + 1 := by linarith
  have hlt : 1 * ((x - 1) / (x + 1)) < 1 := by
    rw [one_mul, div_lt_one hx1]
    linarith
  rw [← arctan_one, arctan_add hlt]
  congr 1
  field_simp
  ring

/-- `arctan a - arctan b = arctan ((a - b)/(1 + a b))` for `a b ≥ 0`. -/
theorem arctan_sub_arctan {a b : ℝ} (h : 0 ≤ a * b) :
    arctan a - arctan b = arctan ((a - b) / (1 + a * b)) := by
  have hlt : a * -b < 1 := by linarith
  rw [sub_eq_add_neg, ← arctan_neg, arctan_add hlt]
  congr 1
  ring_nf

/-- The lower bound of `arctan x` after the argument reduction for `x ≥ 0`. -/
def atanReducedLow (n : ℕ) (x : ℚ) : ℚ :=
  if x ≤ 1 / 2 then atanSeriesLow n x
  else if 2 ≤ x then piLower / 2 - atanSeriesHigh n (1 / x)
  else piLower / 4 + atanSeriesLow n ((x - 1) / (x + 1))

/-- The upper bound of `arctan x` after the argument reduction for `x ≥ 0`. -/
def atanReducedHigh (n : ℕ) (x : ℚ) : ℚ :=
  if x ≤ 1 / 2 then atanSeriesHigh n x
  else if 2 ≤ x then piUpper / 2 - atanSeriesLow n (1 / x)
  else piUpper / 4 + atanSeriesHigh n ((x - 1) / (x + 1))

/-- `atanReducedLow n x ≤ arctan x` for every rational `x`. -/
theorem atanReducedLow_le (n : ℕ) (x : ℚ) : (atanReducedLow n x : ℝ) ≤ arctan x := by
  unfold atanReducedLow
  split_ifs with h₁ h₂
  · exact atanSeriesLow_le n x
  · have hx0 : (0 : ℝ) < x := by exact_mod_cast (show (0 : ℚ) < x by linarith)
    have hinv := arctan_inv_of_pos hx0
    rw [← one_div] at hinv
    have := le_atanSeriesHigh n (1 / x)
    push_cast at this ⊢
    linarith [piLower_le_pi]
  · have hx1 : (-1 : ℝ) < x := by
      have : (-1 : ℚ) < x := by linarith
      exact_mod_cast this
    rw [arctan_eq_pi_div_four_add hx1]
    have := atanSeriesLow_le n ((x - 1) / (x + 1))
    push_cast at this ⊢
    linarith [piLower_le_pi]

/-- `arctan x ≤ atanReducedHigh n x` for every rational `x`. -/
theorem le_atanReducedHigh (n : ℕ) (x : ℚ) : arctan x ≤ (atanReducedHigh n x : ℝ) := by
  unfold atanReducedHigh
  split_ifs with h₁ h₂
  · exact le_atanSeriesHigh n x
  · have hx0 : (0 : ℝ) < x := by exact_mod_cast (show (0 : ℚ) < x by linarith)
    have hinv := arctan_inv_of_pos hx0
    rw [← one_div] at hinv
    have := atanSeriesLow_le n (1 / x)
    push_cast at this ⊢
    linarith [pi_le_piUpper]
  · have hx1 : (-1 : ℝ) < x := by
      have : (-1 : ℚ) < x := by linarith
      exact_mod_cast this
    rw [arctan_eq_pi_div_four_add hx1]
    have := le_atanSeriesHigh n ((x - 1) / (x + 1))
    push_cast at this ⊢
    linarith [pi_le_piUpper]

/-- A rational lower bound of `arctan x`. -/
def atanLow (n : ℕ) (x : ℚ) : ℚ :=
  if 0 ≤ x then atanReducedLow n x else -atanReducedHigh n (-x)

/-- A rational upper bound of `arctan x`. -/
def atanHigh (n : ℕ) (x : ℚ) : ℚ :=
  if 0 ≤ x then atanReducedHigh n x else -atanReducedLow n (-x)

/-- `atanLow n x ≤ arctan x` for every rational `x`. -/
theorem atanLow_le (n : ℕ) (x : ℚ) : (atanLow n x : ℝ) ≤ arctan x := by
  unfold atanLow
  split_ifs
  · exact atanReducedLow_le n x
  · have := le_atanReducedHigh n (-x)
    push_cast at this ⊢
    rw [arctan_neg] at this
    linarith

/-- `arctan x ≤ atanHigh n x` for every rational `x`. -/
theorem le_atanHigh (n : ℕ) (x : ℚ) : arctan x ≤ (atanHigh n x : ℝ) := by
  unfold atanHigh
  split_ifs
  · exact le_atanReducedHigh n x
  · have := atanReducedLow_le n (-x)
    push_cast at this ⊢
    rw [arctan_neg] at this
    linarith

/-- Rounding down to the grid `2^-64`. -/
def roundDown64 (x : ℚ) : ℚ := (⌊x * 2 ^ 64⌋ : ℚ) / 2 ^ 64

/-- Rounding up to the grid `2^-64`. -/
def roundUp64 (x : ℚ) : ℚ := (⌈x * 2 ^ 64⌉ : ℚ) / 2 ^ 64

/-- Rounding down to the grid `2^-64` does not increase `x`. -/
theorem roundDown64_le (x : ℚ) : roundDown64 x ≤ x := by
  rw [roundDown64, div_le_iff₀ (by positivity)]
  exact Int.floor_le _

/-- Rounding up to the grid `2^-64` does not decrease `x`. -/
theorem le_roundUp64 (x : ℚ) : x ≤ roundUp64 x := by
  rw [roundUp64, le_div_iff₀ (by positivity)]
  exact Int.le_ceil _

/-- A lower bound of `arctan x`, after rounding `x` down to the grid `2^-64`. -/
def atanLowAt (n : ℕ) (x : ℚ) : ℚ := atanLow n (roundDown64 x)

/-- An upper bound of `arctan x`, after rounding `x` up to the grid `2^-64`. -/
def atanHighAt (n : ℕ) (x : ℚ) : ℚ := atanHigh n (roundUp64 x)

/-- `atanLowAt n x ≤ arctan x` for every rational `x`. -/
theorem atanLowAt_le (n : ℕ) (x : ℚ) : (atanLowAt n x : ℝ) ≤ arctan x :=
  (atanLow_le n _).trans (arctan_mono (by exact_mod_cast roundDown64_le x))

/-- `arctan x ≤ atanHighAt n x` for every rational `x`. -/
theorem le_atanHighAt (n : ℕ) (x : ℚ) : arctan x ≤ (atanHighAt n x : ℝ) :=
  (arctan_mono (by exact_mod_cast le_roundUp64 x)).trans (le_atanHigh n _)

/-- Bounds of `arctan x`: the series with a number of terms adapted to `|x|`, at the outward
roundings of `x` to about fifty bits. -/
def atanPair (x : ℚ) : ℚ × ℚ :=
  let n := if |x| ≤ 1 / 64 then 6 else if |x| ≤ 1 / 8 then 10 else 20
  (atanLow n (roundDownRel x), atanHigh n (roundUpRel x))

/-- The first component of `atanPair x` is at most `arctan x`. -/
theorem atanPair_fst_le (x : ℚ) : ((atanPair x).1 : ℝ) ≤ arctan x :=
  (atanLow_le _ _).trans (arctan_mono (by exact_mod_cast roundDownRel_le x))

/-- The second component of `atanPair x` is at least `arctan x`. -/
theorem le_atanPair_snd (x : ℚ) : arctan x ≤ ((atanPair x).2 : ℝ) :=
  (arctan_mono (by exact_mod_cast le_roundUpRel x)).trans (le_atanHigh _ _)

end PDE.Analysis
