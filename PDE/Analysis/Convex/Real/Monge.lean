/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Basic.Real.Basic
import CAS.ExactTactic

/-!
# Strict crossing inequality for a real convex cost

For a strictly convex cost of displacement, exchanging two crossed footpoints
strictly decreases the sum of the costs. Both exchanged displacements are
interior convex combinations of the original ones, with complementary weights.
This comparison does not involve an initial potential.
-/

@[expose] public section

open Set

namespace PDE.Analysis

/-- Uncrossing two displacements strictly decreases their total convex cost.
The positive time rescales displacement and need not be bounded away from zero. -/
theorem _root_.StrictConvexOn.crossing_sum_lt {L : ℝ → ℝ}
    (hL : StrictConvexOn ℝ univ L) {t x₁ x₂ y₁ y₂ : ℝ}
    (ht : 0 < t) (hx : x₁ < x₂) (hy : y₂ < y₁) :
    L ((x₂ - y₁) / t) + L ((x₁ - y₂) / t) <
      L ((x₁ - y₁) / t) + L ((x₂ - y₂) / t) := by
  let d := x₂ - x₁ + y₁ - y₂
  have hd : 0 < d := by dsimp [d]; linarith
  let a := (y₁ - y₂) / d
  have ha : 0 < a := div_pos (sub_pos.mpr hy) hd
  have ha₁ : a < 1 := by
    apply (div_lt_one hd).mpr
    dsimp [d]
    linarith
  have hab : (x₁ - y₁) / t ≠ (x₂ - y₂) / t :=
    ne_of_lt ((div_lt_div_iff_of_pos_right ht).2 (by linarith))
  have hfirst := hL.2 (mem_univ _) (mem_univ _) hab ha (sub_pos.mpr ha₁)
    (show a + (1 - a) = 1 by linarith)
  have hsecond := hL.2 (mem_univ _) (mem_univ _) hab (sub_pos.mpr ha₁) ha
    (show (1 - a) + a = 1 by linarith)
  have heq₁ : a * ((x₁ - y₁) / t) + (1 - a) * ((x₂ - y₂) / t) =
      (x₂ - y₁) / t := by
    dsimp [a, d]
    have hden : x₂ - x₁ + y₁ - y₂ ≠ 0 := hd.ne'
    cas using hden
  have heq₂ : (1 - a) * ((x₁ - y₁) / t) + a * ((x₂ - y₂) / t) =
      (x₁ - y₂) / t := by
    dsimp [a, d]
    have hden : x₂ - x₁ + y₁ - y₂ ≠ 0 := hd.ne'
    cas using hden
  simp only [smul_eq_mul, heq₁, heq₂] at hfirst hsecond
  nlinarith only [hfirst, hsecond]

end PDE.Analysis
