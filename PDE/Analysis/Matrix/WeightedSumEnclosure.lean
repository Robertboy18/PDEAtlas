/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

/-!
# Enclosures of weighted sums of products

A quadrature node sum `∑ w x y` of products of two tables of values, with weights `w`, is
computed from approximations `ŵ`, `x̂`, `ŷ` within `η`, `e_x`, `e_y`; the difference is at most
`∑ (|ŵ| (|x̂| e_y + |ŷ| e_x + e_x e_y) + η (|x̂| + e_x) (|ŷ| + e_y))`
(`abs_sum_mul_mul_sub_le`). The bound is a finite sum of the approximations and the error
radii, so a certificate evaluates it exactly. For a tensor rule the weights are products
`w_j w'_n`, with radius `|ŵ_j| η'_n + |ŵ'_n| η_j + η_j η'_n` (`abs_mul_sub_mul_le`).
-/

@[expose] public section

open Finset

namespace PDE.Analysis.Matrix

/-- A product of two approximated numbers. -/
theorem abs_mul_sub_mul_le {a b a' b' ea eb : ℝ} (ha : |a - a'| ≤ ea) (hb : |b - b'| ≤ eb) :
    |a * b - a' * b'| ≤ |a'| * eb + |b'| * ea + ea * eb := by
  have hea : 0 ≤ ea := (abs_nonneg _).trans ha
  have heb : 0 ≤ eb := (abs_nonneg _).trans hb
  have h : a * b - a' * b' = a' * (b - b') + b' * (a - a') + (a - a') * (b - b') := by ring
  rw [h]
  calc |a' * (b - b') + b' * (a - a') + (a - a') * (b - b')| ≤
        |a' * (b - b')| + |b' * (a - a')| + |(a - a') * (b - b')| := abs_add_three _ _ _
    _ = |a'| * |b - b'| + |b'| * |a - a'| + |a - a'| * |b - b'| := by
        rw [abs_mul, abs_mul, abs_mul]
    _ ≤ |a'| * eb + |b'| * ea + ea * eb := by
        gcongr

/-- **Weighted sums of products.** -/
theorem abs_sum_mul_mul_sub_le {ι : Type*} (s : Finset ι) {w w' x x' y y' η ex ey : ι → ℝ}
    (hw : ∀ i ∈ s, |w i - w' i| ≤ η i) (hx : ∀ i ∈ s, |x i - x' i| ≤ ex i)
    (hy : ∀ i ∈ s, |y i - y' i| ≤ ey i) :
    |∑ i ∈ s, w i * (x i * y i) - ∑ i ∈ s, w' i * (x' i * y' i)| ≤
      ∑ i ∈ s, (|w' i| * (|x' i| * ey i + |y' i| * ex i + ex i * ey i) +
        η i * ((|x' i| + ex i) * (|y' i| + ey i))) := by
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi ↦ ?_)
  have hxy := abs_mul_sub_mul_le (hx i hi) (hy i hi)
  have hex : 0 ≤ ex i := (abs_nonneg _).trans (hx i hi)
  have hey : 0 ≤ ey i := (abs_nonneg _).trans (hy i hi)
  have hη : 0 ≤ η i := (abs_nonneg _).trans (hw i hi)
  have hxb : |x i| ≤ |x' i| + ex i := by
    have := abs_sub_abs_le_abs_sub (x i) (x' i)
    linarith [hx i hi]
  have hyb : |y i| ≤ |y' i| + ey i := by
    have := abs_sub_abs_le_abs_sub (y i) (y' i)
    linarith [hy i hi]
  have h : w i * (x i * y i) - w' i * (x' i * y' i) =
      w' i * (x i * y i - x' i * y' i) + (w i - w' i) * (x i * y i) := by ring
  rw [h]
  calc |w' i * (x i * y i - x' i * y' i) + (w i - w' i) * (x i * y i)| ≤
        |w' i| * |x i * y i - x' i * y' i| + |w i - w' i| * (|x i| * |y i|) := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_mul, abs_mul]
    _ ≤ |w' i| * (|x' i| * ey i + |y' i| * ex i + ex i * ey i) +
        η i * ((|x' i| + ex i) * (|y' i| + ey i)) := by
        have h1 := mul_le_mul_of_nonneg_left hxy (abs_nonneg (w' i))
        have h2 : |w i - w' i| * (|x i| * |y i|) ≤ η i * ((|x' i| + ex i) * (|y' i| + ey i)) :=
          mul_le_mul (hw i hi) (mul_le_mul hxb hyb (abs_nonneg _) (by positivity))
            (by positivity) hη
        linarith

end PDE.Analysis.Matrix
