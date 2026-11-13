/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.PiecewiseSlope
public import CAS.Numerics.MatrixPositivity

/-!
# Cells of a one-dimensional mesh and the gaps between distant cells

A mesh `y₀ ≤ y₁ ≤ ⋯ ≤ yₙ` divides the half-line `[y₀, ∞)` into the cells `[y_k, y_{k+1}]`, `k < n`,
and the outer cell `[yₙ, ∞)` (`cell y n k`, with `k = n` for the outer one). Chen and Hou verify
their two-point inequalities on pairs of such cells (Part I, Section 5.4.5, "Verifying the stability
conditions", and Appendix D.1.2, (D.16)): the mesh `{y_i}` of Part I, Section 7.2, in each
coordinate, pairs of cells within a window of indices checked one by one, and pairs further apart
reduced to pointwise bounds through a lower bound of their distance ((D.15) and Supplementary
material I, Section 8.8).

This file supplies the one-dimensional facts. Every point of `[y₀, ∞)` lies in a cell
(`exists_mem_cell`), and two ordered points lie in ordered cells (`exists_mem_cell_le`). If the
cell index of `t` exceeds that of `s` by at least `W ≥ 1`, then `t - s` is at least the gap
`y_{a+W} - y_{a+1}` to the right of the cell `a` of `s` (`rightGap`) and at least the gap
`y_c - y_{c+1-W}` to the left of the cell `c` of `t` (`leftGap`); both depend on one cell only,
so the far pairs cost one check per cell instead of one per pair (`rightGap_le_sub`,
`leftGap_le_sub`). The outer cell lets the same statements cover unbounded domains such as the
quadrant. It only settles the geometric covering: two points of the outer cell can be arbitrarily
far apart, and a bound on the outer cell is an assertion over an unbounded set, which the
far-field asymptotics have to supply.

The last section turns certificate loops into statements over index ranges: a `natAll` loop over
a flat index `k < A * B` decoded as `(k / B, k % B)` (`natAll_div_mod_spec`), and the gluing of
consecutive ranges (`forall_lt_add`), so pairs are enumerated by index arithmetic and never
stored.

## Main definitions

* `cell`: cell `k` of the mesh, `[y_k, y_{k+1}]` for `k < n` and `[yₙ, ∞)` for `k = n`.
* `rightGap`, `leftGap`: the gaps `y_{k+W} - y_{k+1}` and `y_k - y_{k+1-W}` between cell `k`
  and the cells `W` or more indices to its right or left.

## Main results

* `exists_mem_cell`: every point of `[y₀, ∞)` lies in one of the cells `0, …, n`.
* `exists_mem_cell_le`: two ordered points of `[y₀, ∞)` lie in ordered cells.
* `rightGap_le_sub`, `leftGap_le_sub`: if the cell `c` of `t` lies `W ≥ 1` or more cells to the
  right of the cell `a` of `s`, then `t - s` is at least the right gap of `a` and the left gap
  of `c`.
* `gap_le_abs_sub`: the two gap bounds in absolute value, for points in either order.
* `rightGap_pos`, `leftGap_pos`: the gaps of a strictly increasing mesh are positive.
* `natAll_div_mod_spec`: a `natAll` loop over `k < A * B`, decoded as `(k / B, k % B)`, checks
  every pair `a < A`, `b < B`.
* `forall_lt_add`: statements over `[0, A)` and `[A, A + B)` give one over `[0, A + B)`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 5.4.5,
  Section 7.2, Appendix D.1.2, (D.15)-(D.16), and Supplementary material I, Section 8.8.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

namespace CAS.Numerics.CellPairs

open Set

/-- Cell `k` of the mesh `y₀ ≤ y₁ ≤ ⋯ ≤ yₙ`: the interval `[y_k, y_{k+1}]` for `k < n`, and the
outer half-line `[yₙ, ∞)` for `k = n`. -/
def cell (y : ℕ → ℝ) (n k : ℕ) : Set ℝ := {t | y k ≤ t ∧ (k < n → t ≤ y (k + 1))}

/-- The gap `y_{k+W} - y_{k+1}` between cell `k` and the cells `W` or more indices to its
right. -/
def rightGap (y : ℕ → ℝ) (W k : ℕ) : ℝ := y (k + W) - y (k + 1)

/-- The gap `y_k - y_{k+1-W}` between cell `k` and the cells `W` or more indices to its left. -/
def leftGap (y : ℕ → ℝ) (W k : ℕ) : ℝ := y k - y (k + 1 - W)

variable {y : ℕ → ℝ} {n W a c k : ℕ} {s t : ℝ}

/-- A point `t` lies in cell `k` of `y` when `y k ≤ t`, and also `t ≤ y (k + 1)` if `k < n`. -/
theorem mem_cell_iff : t ∈ cell y n k ↔ y k ≤ t ∧ (k < n → t ≤ y (k + 1)) := Iff.rfl

/-- The left end of a cell is a lower bound. -/
theorem le_of_mem_cell (h : t ∈ cell y n k) : y k ≤ t := h.1

/-- The right end of an inner cell is an upper bound. -/
theorem le_succ_of_mem_cell (h : t ∈ cell y n k) (hk : k < n) : t ≤ y (k + 1) := h.2 hk

/-- An inner cell is the closed interval between consecutive mesh points. -/
theorem cell_eq_Icc (hk : k < n) : cell y n k = Icc (y k) (y (k + 1)) := by
  ext t
  simp [cell, hk]

/-- The outer cell is the half-line from the last mesh point. -/
theorem cell_self : cell y n n = Ici (y n) := by
  ext t
  simp [cell]

/-- Every point of `[y₀, ∞)` lies in one of the cells `0, …, n`. -/
theorem exists_mem_cell (ht : y 0 ≤ t) : ∃ k ≤ n, t ∈ cell y n k := by
  rcases le_or_gt (y n) t with hn | hn
  · exact ⟨n, le_rfl, hn, fun h ↦ absurd h (lt_irrefl n)⟩
  · have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h
        exact absurd ht (not_le.2 hn)
      · exact h
    obtain ⟨i, hi, hti⟩ := PDE.Analysis.Approximation.exists_mem_mesh_piece hn0
      (show t ∈ Icc (y 0) (y n) from ⟨ht, hn.le⟩)
    exact ⟨i, hi.le, hti.1, fun _ ↦ hti.2⟩

/-- Two ordered points of `[y₀, ∞)` lie in ordered cells. -/
theorem exists_mem_cell_le (hy : Monotone y) (hs : y 0 ≤ s) (hst : s ≤ t) :
    ∃ a c, a ≤ c ∧ c ≤ n ∧ s ∈ cell y n a ∧ t ∈ cell y n c := by
  obtain ⟨a, han, ha⟩ := exists_mem_cell (n := n) hs
  obtain ⟨c, hcn, hc⟩ := exists_mem_cell (n := n) (hs.trans hst)
  rcases le_or_gt a c with hac | hca
  · exact ⟨a, c, hac, hcn, ha, hc⟩
  · -- the cells are in the wrong order only when `s = t` is the common knot `y (c + 1)`
    have hcn' : c < n := lt_of_lt_of_le hca han
    have h1 : t ≤ y (c + 1) := hc.2 hcn'
    have h2 : y (c + 1) ≤ y a := hy (by omega)
    have hts : t ≤ s := h1.trans (h2.trans ha.1)
    have hst' : s = t := le_antisymm hst hts
    subst hst'
    exact ⟨c, c, le_rfl, hcn, hc, hc⟩

/-- The distance between points of two cells `a < c` is at least `y_c - y_{a+1}`. -/
theorem sub_le_sub_of_mem_cell (hac : a < c) (hcn : c ≤ n) (hs : s ∈ cell y n a)
    (ht : t ∈ cell y n c) : y c - y (a + 1) ≤ t - s := by
  have := hs.2 (lt_of_lt_of_le hac hcn)
  linarith [ht.1]

/-- If the cell `c` of `t` lies `W ≥ 1` or more cells to the right of the cell `a` of `s`, then
`t - s` is at least the right gap of `a`. -/
theorem rightGap_le_sub (hy : Monotone y) (hW : 1 ≤ W) (hac : a + W ≤ c) (hcn : c ≤ n)
    (hs : s ∈ cell y n a) (ht : t ∈ cell y n c) : rightGap y W a ≤ t - s := by
  have h := sub_le_sub_of_mem_cell (by omega) hcn hs ht
  have : y (a + W) ≤ y c := hy hac
  unfold rightGap
  linarith

/-- If the cell `c` of `t` lies `W ≥ 1` or more cells to the right of the cell `a` of `s`, then
`t - s` is at least the left gap of `c`. -/
theorem leftGap_le_sub (hy : Monotone y) (hW : 1 ≤ W) (hac : a + W ≤ c) (hcn : c ≤ n)
    (hs : s ∈ cell y n a) (ht : t ∈ cell y n c) : leftGap y W c ≤ t - s := by
  have h := sub_le_sub_of_mem_cell (by omega) hcn hs ht
  have : y (a + 1) ≤ y (c + 1 - W) := hy (by omega)
  unfold leftGap
  linarith

/-- The two gap bounds in absolute value, for points in either order. -/
theorem gap_le_abs_sub (hy : Monotone y) (hW : 1 ≤ W) (hac : a + W ≤ c) (hcn : c ≤ n)
    (hs : s ∈ cell y n a) (ht : t ∈ cell y n c) :
    rightGap y W a ≤ |s - t| ∧ leftGap y W c ≤ |s - t| := by
  rw [abs_sub_comm]
  exact ⟨(rightGap_le_sub hy hW hac hcn hs ht).trans (le_abs_self _),
    (leftGap_le_sub hy hW hac hcn hs ht).trans (le_abs_self _)⟩

/-- The gaps of a monotone mesh are nonnegative for `W ≥ 1`. -/
theorem rightGap_nonneg (hy : Monotone y) (hW : 1 ≤ W) : 0 ≤ rightGap y W k :=
  sub_nonneg.2 (hy (by omega))

/-- The left gaps of a monotone mesh are nonnegative for `W ≥ 1`. -/
theorem leftGap_nonneg (hy : Monotone y) (hW : 1 ≤ W) : 0 ≤ leftGap y W k :=
  sub_nonneg.2 (hy (by omega))

/-- The gaps of a strictly increasing mesh are positive for `W ≥ 2` (the right gap) and for
`W ≥ 2`, `W ≤ k + 1` (the left gap). -/
theorem rightGap_pos (hy : StrictMono y) (hW : 2 ≤ W) : 0 < rightGap y W k :=
  sub_pos.2 (hy (by omega))

/-- The left gap of a strictly increasing mesh is positive for `2 ≤ W ≤ k + 1`. -/
theorem leftGap_pos (hy : StrictMono y) (hW : 2 ≤ W) (hk : W ≤ k + 1) : 0 < leftGap y W k :=
  sub_pos.2 (hy (by omega))

/-! ### Index arithmetic for certificate loops -/

/-- A `natAll` loop over the flat index `k < A * B`, decoded as `(k / B, k % B)`, checks every
pair `a < A`, `b < B`. -/
theorem natAll_div_mod_spec {A B : ℕ} {p : ℕ → ℕ → Bool}
    (h : natAll (A * B) (fun k ↦ p (k / B) (k % B)) = true) {a b : ℕ} (ha : a < A)
    (hb : b < B) : p a b = true := by
  have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le b) hb
  have hk : a * B + b < A * B := by
    calc a * B + b < a * B + B := by omega
      _ = (a + 1) * B := by ring
      _ ≤ A * B := Nat.mul_le_mul_right B ha
  have := natAll_spec h hk
  have hdiv : (a * B + b) / B = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hb, Nat.zero_add]
  have hmod : (a * B + b) % B = b := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  rwa [hdiv, hmod] at this

/-- Statements over consecutive index ranges glue: certificates over `[0, A)` and `[A, A + B)`
(for instance `natAll` loops in different modules) give one over `[0, A + B)`. -/
theorem forall_lt_add {p : ℕ → Prop} {A B : ℕ} (h₁ : ∀ k < A, p k) (h₂ : ∀ k < B, p (A + k)) :
    ∀ k < A + B, p k := by
  intro k hk
  rcases lt_or_ge k A with h | h
  · exact h₁ k h
  · have := h₂ (k - A) (by omega)
    rwa [Nat.add_sub_cancel' h] at this

/-- A `natAll` loop over an offset range gives the statement on that range. -/
theorem forall_of_natAll {p : ℕ → Bool} {start count : ℕ}
    (h : natAll count (fun k ↦ p (start + k)) = true) : ∀ k < count, p (start + k) = true :=
  fun _ hk ↦ natAll_spec h hk

end CAS.Numerics.CellPairs
