/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The two-point rearrangement inequality for convex functions

For a convex function `j` on the line, pairing the larger of `a, b` with the larger of `c, d`
gives the smaller sum:

`j (max a b - max c d) + j (min a b - min c d) ≤ j (a - c) + j (b - d)`.

This is the rearrangement inequality for two points. It is why the two-point rearrangement of
a function does not increase its difference energies
(`PDE.Analysis.Rearrangement.diffEnergy_polarize_le`), where `j` is the convex cost
`s ↦ |c s|^p`. The inequality for `n` points, that `∑ j (a i - c (π i))` is smallest for the
permutation `π` that sorts both families the same way, is not proved here.

## Main results

* `ConvexOn.map_add_map_add_sub_le`: `j m + j (P + Q - m) ≤ j P + j Q` for a convex `j` on a
  convex set of reals and `P ≤ m ≤ Q` with `P`, `Q` in the set.
* `ConvexOn.map_max_sub_max_add_map_min_sub_min_le`: the two-point inequality above, for a convex
  `j` on a convex set of reals that contains `a - c` and `b - d`.
* `Real.convexOn_abs_mul_rpow`: `s ↦ |c s|^p` is convex on the line, for every real `c` and every
  `p ≥ 1`.

## How it works

A point `m` between `P` and `Q` and its mirror image `P + Q - m` are convex combinations of `P`
and `Q` with the weights swapped. Adding the two convexity inequalities gives
`j m + j (P + Q - m) ≤ j P + j Q`: two points with a given midpoint have the smaller sum of
values the closer they are. When `a, b` and `c, d` are sorted the same way, both sides of the
two-point inequality agree. Otherwise, say `a ≤ b` and `d ≤ c`, the differences `a - c` and
`b - d` are the far points and `b - c`, `a - d` the near ones, with the same midpoint.

## References

* G. H. Hardy, J. E. Littlewood and G. Pólya, *Inequalities*, 2nd ed., Cambridge University
  Press, 1952, Chapter X (rearrangements).
-/

@[expose] public noncomputable section

open Set

namespace ConvexOn

variable {s : Set ℝ} {j : ℝ → ℝ}

/-- For a convex function, a point between `P` and `Q` and its mirror image in the midpoint
have a smaller sum of values than `P` and `Q`: `j m + j (P + Q - m) ≤ j P + j Q` for
`P ≤ m ≤ Q`. -/
theorem map_add_map_add_sub_le (hj : ConvexOn ℝ s j) {P Q m : ℝ} (hP : P ∈ s) (hQ : Q ∈ s)
    (h₁ : P ≤ m) (h₂ : m ≤ Q) : j m + j (P + Q - m) ≤ j P + j Q := by
  rcases eq_or_lt_of_le (h₁.trans h₂) with rfl | hPQ
  · obtain rfl : m = P := le_antisymm h₂ h₁
    simp
  have hQP : 0 < Q - P := sub_pos.mpr hPQ
  set θ := (m - P) / (Q - P) with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (sub_nonneg.mpr h₁) hQP.le
  have hθ1 : θ ≤ 1 := (div_le_one hQP).mpr (by linarith)
  have e₁ : (1 - θ) • P + θ • Q = m := by
    simp only [smul_eq_mul, hθ]
    field_simp
    ring
  have e₂ : θ • P + (1 - θ) • Q = P + Q - m := by
    simp only [smul_eq_mul, hθ]
    field_simp
    ring
  have i₁ := hj.2 hP hQ (sub_nonneg.mpr hθ1) hθ0 (by ring)
  have i₂ := hj.2 hP hQ hθ0 (sub_nonneg.mpr hθ1) (by ring)
  rw [e₁] at i₁
  rw [e₂] at i₂
  simp only [smul_eq_mul] at i₁ i₂
  linarith

/-- **The two-point rearrangement inequality.** For a convex `j`, pairing the larger of
`a, b` with the larger of `c, d` gives the smaller sum:
`j (max a b - max c d) + j (min a b - min c d) ≤ j (a - c) + j (b - d)`. -/
theorem map_max_sub_max_add_map_min_sub_min_le (hj : ConvexOn ℝ s j) {a b c d : ℝ}
    (hac : a - c ∈ s) (hbd : b - d ∈ s) :
    j (max a b - max c d) + j (min a b - min c d) ≤ j (a - c) + j (b - d) := by
  rcases le_total a b with hab | hab <;> rcases le_total c d with hcd | hcd
  · rw [max_eq_right hab, max_eq_right hcd, min_eq_left hab, min_eq_left hcd, add_comm]
  · rw [max_eq_right hab, max_eq_left hcd, min_eq_left hab, min_eq_right hcd]
    have h := hj.map_add_map_add_sub_le hac hbd (m := b - c) (by linarith) (by linarith)
    have e : a - c + (b - d) - (b - c) = a - d := by ring
    rwa [e] at h
  · rw [max_eq_left hab, max_eq_right hcd, min_eq_right hab, min_eq_left hcd]
    have h := hj.map_add_map_add_sub_le hbd hac (m := a - d) (by linarith) (by linarith)
    have e : b - d + (a - c) - (a - d) = b - c := by ring
    rw [e] at h
    linarith
  · rw [max_eq_left hab, max_eq_left hcd, min_eq_right hab, min_eq_right hcd]

end ConvexOn

/-- For `p ≥ 1` the function `s ↦ |c s|^p` is convex on the real line: `|c s|` is convex, and
`x ↦ x^p` is convex and increasing on `[0, ∞)`. -/
theorem Real.convexOn_abs_mul_rpow (c : ℝ) {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ univ fun s : ℝ ↦ |c * s| ^ p := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  have h1 : |c * (a • x + b • y)| ≤ a • |c * x| + b • |c * y| := by
    simp only [smul_eq_mul]
    calc |c * (a * x + b * y)| = |a * (c * x) + b * (c * y)| := by ring_nf
      _ ≤ |a * (c * x)| + |b * (c * y)| := abs_add_le _ _
      _ = a * |c * x| + b * |c * y| := by
        rw [abs_mul a, abs_mul b, abs_of_nonneg ha, abs_of_nonneg hb]
  calc |c * (a • x + b • y)| ^ p ≤ (a • |c * x| + b • |c * y|) ^ p :=
        Real.rpow_le_rpow (abs_nonneg _) h1 (by linarith)
    _ ≤ a • |c * x| ^ p + b • |c * y| ^ p :=
        (convexOn_rpow hp).2 (abs_nonneg _) (abs_nonneg _) ha hb hab
