/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/
module

public import Mathlib.Algebra.Order.Ring.Abs

/-!
# The absolute value of a product of bounded factors

`PDE.Analysis.abs_mul_le_of_le` states `|a * b| ≤ A * B` when `|a| ≤ A` and `|b| ≤ B`, and
`PDE.Analysis.abs_mul_mul_le_of_le` states the same for three factors, in every linearly ordered
ring. The absolute value is multiplicative, and a bound `|a| ≤ A` makes `A` nonnegative, so the
product of the bounds is a product of nonnegative numbers; three factors are two factors twice.
Mathlib has the statement for norms in a normed ring, `norm_mul_le_of_le`, and no form with the
absolute value of an ordered ring.
-/

public section

namespace PDE.Analysis

variable {α : Type*} [Ring α] [LinearOrder α] [IsOrderedRing α]

/-- The absolute value of a product is at most the product of bounds for the factors:
`|a * b| ≤ A * B` when `|a| ≤ A` and `|b| ≤ B`, in every linearly ordered ring. -/
theorem abs_mul_le_of_le {a b A B : α} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

/-- The absolute value of a product of three factors is at most the product of bounds for the
factors: `|a * b * c| ≤ A * B * C` when `|a| ≤ A`, `|b| ≤ B` and `|c| ≤ C`, in every linearly
ordered ring. It is `abs_mul_le_of_le` for the factors `a * b` and `c`. -/
theorem abs_mul_mul_le_of_le {a b c A B C : α} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) :
    |a * b * c| ≤ A * B * C :=
  abs_mul_le_of_le (abs_mul_le_of_le ha hb) hc

end PDE.Analysis
