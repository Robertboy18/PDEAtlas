/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.CellPairs.Mesh
public import PDE.Common.Euclidean

/-!
# Zero-homogeneous functions of the increment on ratio pieces

The coefficients of Chen and Hou's two-point inequality (D.16) depend on the increment `h = x - z`
through functions that are homogeneous of degree zero, such as `g(h) |h_k|^{1/2}`,
`h_k ∂_i g(h) / g(h)` and `g_{i₁}(h) / g_{i₂}(h)` for the `(-1/2)`-homogeneous Hölder weights `g`
(Part I, Appendix D.2, and the paragraph "Verifying the stability conditions" of Section 5.4.5).
Such a function `F` that depends on `|h₁|, |h₂|` only is determined by its two edge functions

`F(h) = F(1, |h₂| / |h₁|)` for `h₁ ≠ 0`, and `F(h) = F(|h₁| / |h₂|, 1)` for `h₂ ≠ 0`

(`eq_edge_zero`, `eq_edge_one`); the verification partitions the edges `{1} × [0, 1]` and
`[0, 1] × {1}` into pieces and uses the monotonicity of the edge functions on each piece. For
a pair of cells the ratio `|h₂| / |h₁|` lies in an interval computed from the cell ends
(`div_mem_Icc_of_bounds`, `abs_sub_mem_Icc_of_mem_cell`); on the pieces that meet it, the
monotone edge functions are bounded by their values at the piece ends
(`le_of_antitoneOn_edge_zero`, `le_of_monotoneOn_edge_zero` and the reverse bounds; the same on
the other edge), and so are quotients of two of them (`div_le_of_antitoneOn_edge_zero`). Pieces
that do not meet the ratio interval of a cell pair need no check.

The reduction needs `F(h) = F(|h₁|, |h₂|)`. Signed factors such as `h_k ∂_i g(h) / g(h)` with
`k ≠ i` change sign with `h_k` and are handled on each sign sector separately; a zero
increment and the two axes `h₁ = 0`, `h₂ = 0` are separate cases of the caller.

## Main results

* `eq_edge_zero`, `eq_edge_one`: a zero-homogeneous function of `(|h₁|, |h₂|)` equals its edge
  function at `|h₂| / |h₁|` when `h₁ ≠ 0`, and at `|h₁| / |h₂|` when `h₂ ≠ 0`.
* `div_mem_Icc_of_bounds`: bounds of a ratio `v / u` from bounds `0 < A ≤ u ≤ A'` and
  `0 ≤ B ≤ v ≤ B'`.
* `abs_sub_mem_Icc_of_mem_cell`: for cells `a < c` the distance of their points lies in
  `[y_c - y_{a+1}, y_{c+1} - y_a]` when `c` is an inner cell.
* `le_of_antitoneOn_edge_zero`: on a ratio piece `[p, q]` where the first edge function is
  antitone, `F(h) ≤ F(1, p)`; the companions `ge_of_antitoneOn_edge_zero`,
  `le_of_monotoneOn_edge_zero`, `ge_of_monotoneOn_edge_zero` and their edge-one versions give
  the other bounds.
* `div_le_of_antitoneOn_edge_zero`: `F₁(h) / F₂(h) ≤ F₁(1, p) / F₂(1, q)` for two such functions
  with antitone first edge functions on `[p, q]`, the denominator positive.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 5.4.5,
  Appendix D.1.2, (D.16), and Appendix D.2.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open Set

namespace CAS.Numerics.CellPairs

variable {F : ℝ^2 → ℝ} {h : ℝ^2}

/-- A zero-homogeneous function of `(|h₁|, |h₂|)` equals its first edge function at the ratio
`|h₂| / |h₁|` when `h₁ ≠ 0`. -/
theorem eq_edge_zero (hF : ∀ t : ℝ, 0 < t → ∀ h, F (t • h) = F h)
    (habs : ∀ h, F h = F !₂[|h 0|, |h 1|]) (h0 : h 0 ≠ 0) :
    F h = F !₂[1, |h 1| / |h 0|] := by
  have hpos : 0 < |h 0| := abs_pos.2 h0
  rw [habs h, ← hF (|h 0|) hpos !₂[1, |h 1| / |h 0|]]
  congr 1
  ext j
  fin_cases j
  · simp
  · simp [mul_div_cancel₀ _ hpos.ne']

/-- A zero-homogeneous function of `(|h₁|, |h₂|)` equals its second edge function at the ratio
`|h₁| / |h₂|` when `h₂ ≠ 0`. -/
theorem eq_edge_one (hF : ∀ t : ℝ, 0 < t → ∀ h, F (t • h) = F h)
    (habs : ∀ h, F h = F !₂[|h 0|, |h 1|]) (h1 : h 1 ≠ 0) :
    F h = F !₂[|h 0| / |h 1|, 1] := by
  have hpos : 0 < |h 1| := abs_pos.2 h1
  rw [habs h, ← hF (|h 1|) hpos !₂[|h 0| / |h 1|, 1]]
  congr 1
  ext j
  fin_cases j
  · simp [mul_div_cancel₀ _ hpos.ne']
  · simp

/-- Bounds of a ratio `v / u` from bounds `0 < A ≤ u ≤ A'` and `0 ≤ B ≤ v ≤ B'`. -/
theorem div_mem_Icc_of_bounds {A A' B B' u v : ℝ} (hA : 0 < A) (hu : A ≤ u) (hu' : u ≤ A')
    (hB : 0 ≤ B) (hv : B ≤ v) (hv' : v ≤ B') : v / u ∈ Icc (B / A') (B' / A) := by
  have hu0 : 0 < u := hA.trans_le hu
  have hv0 : 0 ≤ v := hB.trans hv
  constructor
  · calc B / A' ≤ v / A' := div_le_div_of_nonneg_right hv (hu0.le.trans hu')
      _ ≤ v / u := div_le_div_of_nonneg_left hv0 hu0 hu'
  · calc v / u ≤ B' / u := div_le_div_of_nonneg_right hv' hu0.le
      _ ≤ B' / A := div_le_div_of_nonneg_left (hv0.trans hv') hA hu

/-- The distance between points of the cells `a ≤ c` of a monotone mesh lies between
`y_c - y_{a+1}` (if `a < c`) and `y_{c+1} - y_a` (if `c` is an inner cell). -/
theorem abs_sub_le_of_mem_cell {y : ℕ → ℝ} {n a c : ℕ} {s t : ℝ} (hy : Monotone y)
    (hac : a ≤ c) (hcn : c < n) (hs : s ∈ cell y n a) (ht : t ∈ cell y n c) :
    |t - s| ≤ y (c + 1) - y a := by
  have h₁ := hs.1
  have h₂ := ht.2 hcn
  have h₃ := hs.2 (lt_of_le_of_lt hac hcn)
  have h₄ := ht.1
  have : y a ≤ y c := hy hac
  have : y (a + 1) ≤ y (c + 1) := hy (by omega)
  rw [abs_le]
  constructor <;> linarith

/-- For cells `a < c` the distance of their points lies in `[y_c - y_{a+1}, y_{c+1} - y_a]`
when `c` is an inner cell. -/
theorem abs_sub_mem_Icc_of_mem_cell {y : ℕ → ℝ} {n a c : ℕ} {s t : ℝ} (hy : Monotone y)
    (hac : a < c) (hcn : c < n) (hs : s ∈ cell y n a) (ht : t ∈ cell y n c) :
    |t - s| ∈ Icc (y c - y (a + 1)) (y (c + 1) - y a) := by
  have hlow := sub_le_sub_of_mem_cell hac hcn.le hs ht
  exact ⟨hlow.trans (le_abs_self _), abs_sub_le_of_mem_cell hy hac.le hcn hs ht⟩

/-! ### Bounds on ratio pieces from monotone edge functions -/

section Edges

variable (hF : ∀ t : ℝ, 0 < t → ∀ h, F (t • h) = F h) (habs : ∀ h, F h = F !₂[|h 0|, |h 1|])
  {p q : ℝ}
include hF habs

/-- On a ratio piece `[p, q]` where the first edge function is antitone, `F(h) ≤ F(1, p)`. -/
theorem le_of_antitoneOn_edge_zero (hanti : AntitoneOn (fun t ↦ F !₂[1, t]) (Icc p q))
    (h0 : h 0 ≠ 0) (hr : |h 1| / |h 0| ∈ Icc p q) : F h ≤ F !₂[1, p] := by
  rw [eq_edge_zero hF habs h0]
  exact hanti ⟨le_rfl, hr.1.trans hr.2⟩ hr hr.1

/-- On a ratio piece `[p, q]` where the first edge function is antitone, `F(1, q) ≤ F(h)`. -/
theorem ge_of_antitoneOn_edge_zero (hanti : AntitoneOn (fun t ↦ F !₂[1, t]) (Icc p q))
    (h0 : h 0 ≠ 0) (hr : |h 1| / |h 0| ∈ Icc p q) : F !₂[1, q] ≤ F h := by
  rw [eq_edge_zero hF habs h0]
  exact hanti hr ⟨hr.1.trans hr.2, le_rfl⟩ hr.2

/-- On a ratio piece `[p, q]` where the first edge function is monotone, `F(h) ≤ F(1, q)`. -/
theorem le_of_monotoneOn_edge_zero (hmono : MonotoneOn (fun t ↦ F !₂[1, t]) (Icc p q))
    (h0 : h 0 ≠ 0) (hr : |h 1| / |h 0| ∈ Icc p q) : F h ≤ F !₂[1, q] := by
  rw [eq_edge_zero hF habs h0]
  exact hmono hr ⟨hr.1.trans hr.2, le_rfl⟩ hr.2

/-- On a ratio piece `[p, q]` where the first edge function is monotone, `F(1, p) ≤ F(h)`. -/
theorem ge_of_monotoneOn_edge_zero (hmono : MonotoneOn (fun t ↦ F !₂[1, t]) (Icc p q))
    (h0 : h 0 ≠ 0) (hr : |h 1| / |h 0| ∈ Icc p q) : F !₂[1, p] ≤ F h := by
  rw [eq_edge_zero hF habs h0]
  exact hmono ⟨le_rfl, hr.1.trans hr.2⟩ hr hr.1

/-- On a ratio piece `[p, q]` of the second edge where the edge function is antitone,
`F(h) ≤ F(p, 1)`. -/
theorem le_of_antitoneOn_edge_one (hanti : AntitoneOn (fun s ↦ F !₂[s, 1]) (Icc p q))
    (h1 : h 1 ≠ 0) (hr : |h 0| / |h 1| ∈ Icc p q) : F h ≤ F !₂[p, 1] := by
  rw [eq_edge_one hF habs h1]
  exact hanti ⟨le_rfl, hr.1.trans hr.2⟩ hr hr.1

/-- On a ratio piece `[p, q]` of the second edge where the edge function is antitone,
`F(q, 1) ≤ F(h)`. -/
theorem ge_of_antitoneOn_edge_one (hanti : AntitoneOn (fun s ↦ F !₂[s, 1]) (Icc p q))
    (h1 : h 1 ≠ 0) (hr : |h 0| / |h 1| ∈ Icc p q) : F !₂[q, 1] ≤ F h := by
  rw [eq_edge_one hF habs h1]
  exact hanti hr ⟨hr.1.trans hr.2, le_rfl⟩ hr.2

/-- On a ratio piece `[p, q]` of the second edge where the edge function is monotone,
`F(h) ≤ F(q, 1)`. -/
theorem le_of_monotoneOn_edge_one (hmono : MonotoneOn (fun s ↦ F !₂[s, 1]) (Icc p q))
    (h1 : h 1 ≠ 0) (hr : |h 0| / |h 1| ∈ Icc p q) : F h ≤ F !₂[q, 1] := by
  rw [eq_edge_one hF habs h1]
  exact hmono hr ⟨hr.1.trans hr.2, le_rfl⟩ hr.2

/-- On a ratio piece `[p, q]` of the second edge where the edge function is monotone,
`F(p, 1) ≤ F(h)`. -/
theorem ge_of_monotoneOn_edge_one (hmono : MonotoneOn (fun s ↦ F !₂[s, 1]) (Icc p q))
    (h1 : h 1 ≠ 0) (hr : |h 0| / |h 1| ∈ Icc p q) : F !₂[p, 1] ≤ F h := by
  rw [eq_edge_one hF habs h1]
  exact hmono ⟨le_rfl, hr.1.trans hr.2⟩ hr hr.1

end Edges

/-- A quotient of two zero-homogeneous functions of `(|h₁|, |h₂|)` with antitone first edge
functions on the ratio piece `[p, q]`, the denominator positive there:
`F₁(h) / F₂(h) ≤ F₁(1, p) / F₂(1, q)` when `F₁(1, p) ≥ 0`. For two Hölder weights of degree
`-1/2` take `F_k(h) = g_k(h) |h₁|^{1/2}`, which are zero-homogeneous with the same quotient where
`h₁ ≠ 0`. -/
theorem div_le_of_antitoneOn_edge_zero {F₁ F₂ : ℝ^2 → ℝ} {p q : ℝ}
    (hF₁ : ∀ t : ℝ, 0 < t → ∀ h, F₁ (t • h) = F₁ h) (habs₁ : ∀ h, F₁ h = F₁ !₂[|h 0|, |h 1|])
    (hF₂ : ∀ t : ℝ, 0 < t → ∀ h, F₂ (t • h) = F₂ h) (habs₂ : ∀ h, F₂ h = F₂ !₂[|h 0|, |h 1|])
    (hanti₁ : AntitoneOn (fun t ↦ F₁ !₂[1, t]) (Icc p q))
    (hanti₂ : AntitoneOn (fun t ↦ F₂ !₂[1, t]) (Icc p q))
    (hpos : 0 < F₂ !₂[1, q]) (hnn : 0 ≤ F₁ !₂[1, p]) (h0 : h 0 ≠ 0)
    (hr : |h 1| / |h 0| ∈ Icc p q) : F₁ h / F₂ h ≤ F₁ !₂[1, p] / F₂ !₂[1, q] := by
  have e₁ := le_of_antitoneOn_edge_zero hF₁ habs₁ hanti₁ h0 hr
  have e₂ := ge_of_antitoneOn_edge_zero hF₂ habs₂ hanti₂ h0 hr
  have hF₂pos : 0 < F₂ h := hpos.trans_le e₂
  calc F₁ h / F₂ h ≤ F₁ !₂[1, p] / F₂ h := div_le_div_of_nonneg_right e₁ hF₂pos.le
    _ ≤ F₁ !₂[1, p] / F₂ !₂[1, q] := div_le_div_of_nonneg_left hnn hpos e₂

end CAS.Numerics.CellPairs
