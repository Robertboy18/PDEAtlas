/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Bounds of the nodal polynomials of low-order interpolation

The interpolation errors on a mesh cell are a derivative bound times a nodal polynomial; these are
the maxima of the nodal polynomials that occur (Chen and Hou, Part II, Supplementary Lemma 8.1,
(8.67)-(8.72)), together with the two Hermite-derivative combinations `(3t² - 2t, 3t² - 4t + 1)`.

## Main results

* `abs_sub_mul_sub_le`: `|(t - a)(t - b)| ≤ (b - a)² / 4` on `[a, b]` (8.67).
* `abs_add_abs_hermiteSlopes_le`: `|3t² - 2t| + |3t² - 4t + 1| ≤ 1` on `[0, 1]` (8.68).
* `abs_cubicNodal_le`: `|t (t - 1) (t - 2)| ≤ 2 / (3 √3)` on `[0, 2]` (8.69).
* `mul_sub_one_sq_le`: `t (t - 1)² ≤ 4 / 27` on `[0, 1]` (8.70).
* `abs_quarticNodal_le`: `|t (t - 1) (t - 2) (t - 3)| ≤ 1` on `[0, 3]` (8.71).
* `abs_quinticNodal_le`: `|t² (t - 1)² (t - 2)| ≤ 1 / 10` on `[0, 1]` (8.72).

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Supplementary
  material II (in the same PDF), Section 8.6, Lemma 8.1. <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

namespace PDE.Analysis.Approximation

/-- **Supp II (8.67).** `|(t - a)(t - b)| ≤ (b - a)² / 4` on `[a, b]`. -/
theorem abs_sub_mul_sub_le {a b t : ℝ} (ht : t ∈ Set.Icc a b) :
    |(t - a) * (t - b)| ≤ (b - a) ^ 2 / 4 := by
  rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by linarith [ht.1]) (by linarith [ht.2]))]
  nlinarith [sq_nonneg (t - (a + b) / 2)]

/-- **Supp II (8.68).** `|3t² - 2t| + |3t² - 4t + 1| ≤ 1` on `[0, 1]`. -/
theorem abs_add_abs_hermiteSlopes_le {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |3 * t ^ 2 - 2 * t| + |3 * t ^ 2 - 4 * t + 1| ≤ 1 := by
  obtain ⟨h0, h1⟩ := ht
  rcases abs_cases (3 * t ^ 2 - 2 * t) with ⟨h, -⟩ | ⟨h, -⟩ <;>
    rcases abs_cases (3 * t ^ 2 - 4 * t + 1) with ⟨h', -⟩ | ⟨h', -⟩ <;>
    rw [h, h'] <;> nlinarith

/-- **Supp II (8.69).** `|t (t - 1) (t - 2)| ≤ 2 / (3 √3)` on `[0, 2]`. -/
theorem abs_cubicNodal_le {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 2) :
    |t * (t - 1) * (t - 2)| ≤ 2 / (3 * Real.sqrt 3) := by
  have hsq : (t * (t - 1) * (t - 2)) ^ 2 ≤ 4 / 27 := by
    -- with `q = (t - 1)²`, the square is `q (1 - q)²`
    have hq0 : 0 ≤ (t - 1) ^ 2 := sq_nonneg _
    have hq1 : (t - 1) ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    have hid : (t * (t - 1) * (t - 2)) ^ 2 = (t - 1) ^ 2 * (1 - (t - 1) ^ 2) ^ 2 := by ring
    rw [hid]
    nlinarith [mul_nonneg (sq_nonneg (1 - 3 * (t - 1) ^ 2)) (by linarith : 0 ≤ 4 - 3 * (t - 1) ^ 2)]
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hc : 0 < 2 / (3 * Real.sqrt 3) := by positivity
  rw [← abs_of_pos hc]
  apply sq_le_sq.mp
  have hval : (2 / (3 * Real.sqrt 3)) ^ 2 = 4 / 27 := by
    rw [div_pow, mul_pow, hs3]
    norm_num
  rw [hval]
  exact hsq

/-- **Supp II (8.70).** `t (t - 1)² ≤ 4 / 27` on `[0, 1]`. -/
theorem mul_sub_one_sq_le {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : t * (t - 1) ^ 2 ≤ 4 / 27 := by
  nlinarith [mul_nonneg (sq_nonneg (3 * t - 1)) (by linarith [ht.2] : 0 ≤ 4 - 3 * t)]

/-- **Supp II (8.71).** `|t (t - 1) (t - 2) (t - 3)| ≤ 1` on `[0, 3]`. -/
theorem abs_quarticNodal_le {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 3) :
    |t * (t - 1) * (t - 2) * (t - 3)| ≤ 1 := by
  -- with `s = t (3 - t) ∈ [0, 9/4]` the product is `s (s - 2) = (s - 1)² - 1`
  have hs0 : 0 ≤ t * (3 - t) := mul_nonneg ht.1 (by linarith [ht.2])
  have hs1 : t * (3 - t) ≤ 9 / 4 := by nlinarith [sq_nonneg (t - 3 / 2)]
  have hid : t * (t - 1) * (t - 2) * (t - 3) = (t * (3 - t) - 1) ^ 2 - 1 := by ring
  rw [hid, abs_le]
  constructor <;> nlinarith [sq_nonneg (t * (3 - t) - 1)]

/-- **Supp II (8.72).** `|t² (t - 1)² (t - 2)| ≤ 1 / 10` on `[0, 1]`. -/
theorem abs_quinticNodal_le {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |t ^ 2 * (t - 1) ^ 2 * (t - 2)| ≤ 1 / 10 := by
  have h1 : |t * (t - 1)| ≤ 1 / 4 := by
    simpa using abs_sub_mul_sub_le (a := 0) (b := 1) ht
  have h2 := abs_cubicNodal_le (t := t) ⟨ht.1, by linarith [ht.2]⟩
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs3 : (5 : ℝ) / 3 < Real.sqrt 3 := by
    rw [show (5 : ℝ) / 3 = Real.sqrt (25 / 9) by
      rw [show (25 : ℝ) / 9 = (5 / 3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hid : t ^ 2 * (t - 1) ^ 2 * (t - 2) = (t * (t - 1)) * (t * (t - 1) * (t - 2)) := by ring
  rw [hid, abs_mul]
  calc |t * (t - 1)| * |t * (t - 1) * (t - 2)| ≤ 1 / 4 * (2 / (3 * Real.sqrt 3)) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ ≤ 1 / 10 := by
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith

end PDE.Analysis.Approximation
