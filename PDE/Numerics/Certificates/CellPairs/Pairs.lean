/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.CellPairs.Mesh
public import PDE.Spaces.Holder.Directional

/-!
# Hölder bounds and two-point inequalities from cell pairs

Chen and Hou verify their weighted Hölder estimates on pairs of mesh cells (Part I, Section 5.4.5,
"Verifying the stability conditions", and Appendix D.1.2, (D.16)): for `x ∈ Q_p` and `z ∈ Q_q` with
the cell indices `p, q` within a window of `W` cells, a check on the cell pair; for cells further
apart, the large-distance reduction (D.15) and Supplementary material I, Section 8.8: the difference
`f(x) - f(z)` is bounded by `|f(x)| + |f(z)|` and the distance from below,

`|f(x) - f(z)| / |x - z|^α ≤ (|f(x)| + |f(z)|) / |x - z|^α ≤ 2 ‖f‖ / |x - z|^α`.

Here the cells are those of two meshes `y` (first coordinate) and `y'` (second coordinate),
each with an outer half-line cell (`CellPairs.cell`), so the closed quadrant `[y₀, ∞) × [y'₀, ∞)`
is covered. The far reduction is refined per cell: a cell `a` contributes its sup bound divided by
its own gap to the cells `W` indices away (`rightGap`, `leftGap`), so the far pairs need one check
per cell and the near pairs one check per cell pair of the window. The pairs are enumerated by
index arithmetic (cell, offset), never stored.

## Main results

* `HolderSpace.directionalSeminorm_le_of_cellPairs`: the directional seminorm
  `[f]_{C^α_{x_i}(D)} ≤ C` from near pairs `(a, a + d)`, `d < W`, of each row and per-cell sup
  bounds `M` with `M ≤ R · rightGap^α`, `M ≤ L · leftGap^α`, `R + L ≤ C`.
* `CellPairs.forall_of_cellPairs`: a two-point statement `Φ x z` on all pairs `x₀ ≤ z₀` of `D`
  from the near cell pairs `(a, b), (a + d, b ± e)`, `d, e < W`, and from the far pairs, which are
  given their cells and satisfy `a + W ≤ c`, `b + W ≤ d` or `d + W ≤ b`. This is the shape of the
  stability condition (D.16), stated for `x₁ ≤ z₁`.
* `HolderSpace.weightedSeminorm_le_of_cellPairs`: the weighted seminorm `[f]_{C_g(D)} ≤ C` for an
  even weight with the `0`-homogeneous axis bounds `g(h) |h_j|^α ≤ G_j`, from near cell pairs and
  per-cell far budgets; `HolderSpace.weightedSeminorm_le_of_forall_le` gives it from any covering
  of the ordered pairs, for instance by block pairs.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 5.4.5,
  Appendix D.1.2, (D.15)-(D.16), (C.1b), and Supplementary material I, Section 8.8.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open Set
open scoped ENNReal NNReal

namespace CAS.Numerics.CellPairs

/-- The cell `(a, b)` of the product mesh: `x₀` in cell `a` of `y` and `x₁` in cell `b` of
`y'`. -/
def box (y y' : ℕ → ℝ) (n m a b : ℕ) : Set (ℝ^2) := {x | x 0 ∈ cell y n a ∧ x 1 ∈ cell y' m b}

/-- A point lies in the cell `(a, b)` of the product mesh when `x₀` lies in cell `a` of `y` and `x₁`
in cell `b` of `y'`. -/
theorem mem_box_iff {y y' : ℕ → ℝ} {n m a b : ℕ} {x : ℝ^2} :
    x ∈ box y y' n m a b ↔ x 0 ∈ cell y n a ∧ x 1 ∈ cell y' m b := Iff.rfl

/-- **Covering by cell pairs.** A two-point statement `Φ x z` holds for all `x, z ∈ D` with
`x₀ ≤ z₀` if it holds on the near cell pairs, `z` in the cell `(a + d, b + e)` or
`(a + d, b - e)` of the cell `(a, b)` of `x` with `d, e < W`, and on the far pairs, whose cells
`(a, b)`, `(c, d)` satisfy `a + W ≤ c`, `b + W ≤ d` or `d + W ≤ b`. Chen and Hou's (D.16) has this
shape; the far hypothesis receives the cells, so the gap lemmas (`gap_le_abs_sub`) bound the
distance from below. -/
theorem forall_of_cellPairs {y y' : ℕ → ℝ} {n m W : ℕ} (hy : Monotone y) {D : Set (ℝ^2)}
    (hD : ∀ x ∈ D, y 0 ≤ x 0 ∧ y' 0 ≤ x 1) {Φ : ℝ^2 → ℝ^2 → Prop}
    (nearUp : ∀ a ≤ n, ∀ b ≤ m, ∀ d < W, ∀ e < W, a + d ≤ n → b + e ≤ m →
      ∀ x ∈ D, ∀ z ∈ D, x 0 ≤ z 0 → x ∈ box y y' n m a b → z ∈ box y y' n m (a + d) (b + e) →
        Φ x z)
    (nearDown : ∀ a ≤ n, ∀ b ≤ m, ∀ d < W, ∀ e < W, a + d ≤ n → e ≤ b →
      ∀ x ∈ D, ∀ z ∈ D, x 0 ≤ z 0 → x ∈ box y y' n m a b → z ∈ box y y' n m (a + d) (b - e) →
        Φ x z)
    (far : ∀ a c, a ≤ c → c ≤ n → ∀ b ≤ m, ∀ d ≤ m, (a + W ≤ c ∨ b + W ≤ d ∨ d + W ≤ b) →
      ∀ x ∈ D, ∀ z ∈ D, x 0 ≤ z 0 → x ∈ box y y' n m a b → z ∈ box y y' n m c d → Φ x z) :
    ∀ x ∈ D, ∀ z ∈ D, x 0 ≤ z 0 → Φ x z := by
  intro x hx z hz hxz
  obtain ⟨a, c, hac, hcn, ha, hc⟩ := exists_mem_cell_le (n := n) hy (hD x hx).1 hxz
  obtain ⟨b, hbm, hb⟩ := exists_mem_cell (n := m) (y := y') (hD x hx).2
  obtain ⟨d, hdm, hd⟩ := exists_mem_cell (n := m) (y := y') (hD z hz).2
  by_cases hfar : a + W ≤ c ∨ b + W ≤ d ∨ d + W ≤ b
  · exact far a c hac hcn b hbm d hdm hfar x hx z hz hxz ⟨ha, hb⟩ ⟨hc, hd⟩
  · push Not at hfar
    obtain ⟨h₁, h₂, h₃⟩ := hfar
    rcases le_total b d with hbd | hdb
    · have hc' : c = a + (c - a) := by omega
      have hd' : d = b + (d - b) := by omega
      rw [hc'] at hc
      rw [hd'] at hd
      exact nearUp a (by omega) b hbm (c - a) (by omega) (d - b) (by omega) (by omega)
        (by omega) x hx z hz hxz ⟨ha, hb⟩ ⟨hc, hd⟩
    · have hc' : c = a + (c - a) := by omega
      have hd' : d = b - (b - d) := by omega
      rw [hc'] at hc
      rw [hd'] at hd
      exact nearDown a (by omega) b hbm (c - a) (by omega) (b - d) (by omega) (by omega)
        (by omega) x hx z hz hxz ⟨ha, hb⟩ ⟨hc, hd⟩

end CAS.Numerics.CellPairs

namespace HolderSpace

open CAS.Numerics.CellPairs

variable {E : Type*} [SeminormedAddCommGroup E]

/-- A real bound `‖f x - f z‖ ≤ C |x_i - z_i|^α` in the extended form of the directional
seminorm. -/
theorem edist_le_ofReal_mul_of_norm_sub_le {f : ℝ^2 → E} {x z : ℝ^2} {i : Fin 2} {α : ℝ≥0}
    {C : ℝ} (hC : 0 ≤ C) (h : ‖f x - f z‖ ≤ C * |x i - z i| ^ (α : ℝ)) :
    edist (f x) (f z) ≤ ENNReal.ofReal C * edist (x i) (z i) ^ (α : ℝ) := by
  rw [edist_dist, dist_eq_norm, edist_dist, Real.dist_eq,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (NNReal.coe_nonneg α), ← ENNReal.ofReal_mul hC]
  exact ENNReal.ofReal_le_ofReal h

/-- The far-pair reduction on a line: if `|f| ≤ M_a` and `|f| ≤ M_c` at the two points and
`M_a ≤ R r^α`, `M_c ≤ L l^α` for gaps `0 ≤ r, l ≤ |s - t|`, then
`‖f x - f z‖ ≤ (R + L) |s - t|^α`. -/
theorem norm_sub_le_of_gaps {f : ℝ^2 → E} {x z : ℝ^2} {α : ℝ} (hα : 0 ≤ α)
    {Ma Mc R L r l d : ℝ} (hx : ‖f x‖ ≤ Ma) (hz : ‖f z‖ ≤ Mc) (hMa : Ma ≤ R * r ^ α)
    (hMc : Mc ≤ L * l ^ α) (hR : 0 ≤ R) (hL : 0 ≤ L) (hr : 0 ≤ r) (hl : 0 ≤ l) (hrd : r ≤ d)
    (hld : l ≤ d) : ‖f x - f z‖ ≤ (R + L) * d ^ α := by
  have h₁ : r ^ α ≤ d ^ α := Real.rpow_le_rpow hr hrd hα
  have h₂ : l ^ α ≤ d ^ α := Real.rpow_le_rpow hl hld hα
  calc ‖f x - f z‖ ≤ ‖f x‖ + ‖f z‖ := norm_sub_le _ _
    _ ≤ R * r ^ α + L * l ^ α := by linarith
    _ ≤ R * d ^ α + L * d ^ α := by gcongr
    _ = (R + L) * d ^ α := by ring

/-- **Directional Hölder seminorm from cell pairs** (Chen and Hou, Part I, Appendix D.1.2,
and Supplementary material I, Section 8.8). Let `i ≠ j`, `y` a monotone mesh with `n` cells in the
direction `i` and `y'` a mesh with `m` cells in the direction `j` (each with its outer cell), and
`D` a set in `[y₀, ∞)` in the coordinate `i` and in `[y'₀, ∞)` in the coordinate `j`. Suppose

* near pairs: on each row `b` and for cells `a` and `a + d`, `d < W`, every pair `x, z ∈ D` on a
  line `x_j = z_j` satisfies `‖f x - f z‖ ≤ C |x_i - z_i|^α`;
* sup bounds: `‖f x‖ ≤ M b a` on the cell `(a, b)`;
* far budgets: `M b a ≤ R · rightGap^α` for cells with `a + W ≤ n` and `M b c ≤ L · leftGap^α`
  for cells with `W ≤ c`, where `R, L ≥ 0` and `R + L ≤ C`.

Then `[f]_{C^α_{x_i}(D)} ≤ C`. A pair `a + W ≤ c` is far: `|f(x) - f(z)| ≤ M_a + M_c ≤
(R + L) |x_i - z_i|^α`, the reduction (D.15) with the distance from below by the gaps. -/
theorem directionalSeminorm_le_of_cellPairs {i j : Fin 2} (hij : i ≠ j) {y y' : ℕ → ℝ}
    {n m W : ℕ} (hy : Monotone y) (hW : 1 ≤ W) {α : ℝ≥0} {D : Set (ℝ^2)}
    (hD : ∀ x ∈ D, y 0 ≤ x i ∧ y' 0 ≤ x j) {f : ℝ^2 → E} {C R L : ℝ} {M : ℕ → ℕ → ℝ}
    (near : ∀ b ≤ m, ∀ a ≤ n, ∀ d < W, a + d ≤ n → ∀ x ∈ D, ∀ z ∈ D, x j = z j →
      x j ∈ cell y' m b → x i ∈ cell y n a → z i ∈ cell y n (a + d) →
        ‖f x - f z‖ ≤ C * |x i - z i| ^ (α : ℝ))
    (sup : ∀ b ≤ m, ∀ a ≤ n, ∀ x ∈ D, x j ∈ cell y' m b → x i ∈ cell y n a → ‖f x‖ ≤ M b a)
    (right : ∀ b ≤ m, ∀ a, a + W ≤ n → M b a ≤ R * rightGap y W a ^ (α : ℝ))
    (left : ∀ b ≤ m, ∀ c ≤ n, W ≤ c → M b c ≤ L * leftGap y W c ^ (α : ℝ))
    (hR : 0 ≤ R) (hL : 0 ≤ L) (hRL : R + L ≤ C) :
    directionalSeminorm i α D f ≤ ENNReal.ofReal C := by
  have hC : 0 ≤ C := by linarith
  -- the ordered case on a line
  have key : ∀ x ∈ D, ∀ z ∈ D, x j = z j → x i ≤ z i →
      ‖f x - f z‖ ≤ C * |x i - z i| ^ (α : ℝ) := by
    intro x hx z hz hjz hxz
    obtain ⟨a, c, hac, hcn, ha, hc⟩ := exists_mem_cell_le (n := n) hy (hD x hx).1 hxz
    obtain ⟨b, hbm, hb⟩ := exists_mem_cell (n := m) (y := y') (hD x hx).2
    rcases lt_or_ge c (a + W) with hnear | hfar
    · have hc' : c = a + (c - a) := by omega
      rw [hc'] at hc
      exact near b hbm a (by omega) (c - a) (by omega) (by omega) x hx z hz hjz hb ha hc
    · have hgap := gap_le_abs_sub hy hW hfar hcn ha hc
      have hzb : z j ∈ cell y' m b := hjz ▸ hb
      have := norm_sub_le_of_gaps (f := f) (x := x) (z := z) α.2
        (sup b hbm a (by omega) x hx hb ha) (sup b hbm c hcn z hz hzb hc)
        (right b hbm a (by omega)) (left b hbm c hcn (by omega)) hR hL
        (rightGap_nonneg hy hW) (leftGap_nonneg hy hW) hgap.1 hgap.2
      exact this.trans (mul_le_mul_of_nonneg_right hRL (by positivity))
  refine directionalSeminorm_le_iff.2 fun x hx z hz hl ↦ ?_
  have hjz : x j = z j := hl j hij.symm
  refine edist_le_ofReal_mul_of_norm_sub_le hC ?_
  rcases le_total (x i) (z i) with h | h
  · exact key x hx z hz hjz h
  · rw [norm_sub_rev, abs_sub_comm]
    exact key z hz x hx hjz.symm h

/-- The weighted far-pair reduction: if `‖f x‖ ≤ M`, `M ≥ 0`, the `0`-homogeneous bound
`g(h) |h_j|^α ≤ G` holds at `h = x - z`, and `M G ≤ R r^α` with `0 < r ≤ |h_j|`, then
`‖f x‖ g(h) ≤ R`. -/
theorem norm_mul_le_of_gap {F : Type*} [SeminormedAddCommGroup F] {u : F} {h : ℝ^2} {j : Fin 2}
    {g : ℝ^2 → ℝ} {α M G R r : ℝ} (hα : 0 ≤ α) (hg : 0 ≤ g h) (hu : ‖u‖ ≤ M)
    (hgG : g h * |h j| ^ α ≤ G) (hMG : M * G ≤ R * r ^ α) (hr : 0 < r) (hrh : r ≤ |h j|) :
    ‖u‖ * g h ≤ R := by
  have hM : 0 ≤ M := (norm_nonneg u).trans hu
  have hpos : 0 < |h j| ^ α := Real.rpow_pos_of_pos (hr.trans_le hrh) α
  have hle : r ^ α ≤ |h j| ^ α := Real.rpow_le_rpow hr.le hrh hα
  have hR : 0 ≤ R := by
    have : 0 ≤ R * r ^ α := (mul_nonneg hM ((mul_nonneg hg hpos.le).trans hgG)).trans hMG
    exact nonneg_of_mul_nonneg_left this (Real.rpow_pos_of_pos hr α)
  have : ‖u‖ * g h * |h j| ^ α ≤ R * |h j| ^ α := by
    calc ‖u‖ * g h * |h j| ^ α = ‖u‖ * (g h * |h j| ^ α) := by ring
      _ ≤ M * G := mul_le_mul hu hgG (mul_nonneg hg hpos.le) hM
      _ ≤ R * r ^ α := hMG
      _ ≤ R * |h j| ^ α := mul_le_mul_of_nonneg_left hle hR
  exact le_of_mul_le_mul_right this hpos

/-- The weighted seminorm of an even weight from the real bound on ordered pairs:
if `‖f x - f z‖ g(x - z) ≤ C` for all `x, z ∈ D` with `x₀ ≤ z₀`, then `[f]_{C_g(D)} ≤ C`. Any
covering of the ordered pairs (`forall_of_cellPairs`, `forall_of_blockPairs`) supplies the
hypothesis. -/
theorem weightedSeminorm_le_of_forall_le {D : Set (ℝ^2)} {f : ℝ^2 → E} {g : ℝ^2 → ℝ}
    (hg : ∀ h, g (-h) = g h) {C : ℝ}
    (h : ∀ x ∈ D, ∀ z ∈ D, x 0 ≤ z 0 → ‖f x - f z‖ * g (x - z) ≤ C) :
    weightedSeminorm g D f ≤ ENNReal.ofReal C := by
  refine weightedSeminorm_le_iff.2 fun x hx z hz ↦ ?_
  have hreal : ‖f x - f z‖ * g (x - z) ≤ C := by
    rcases le_total (x 0) (z 0) with hxz | hzx
    · exact h x hx z hz hxz
    · have := h z hz x hx hzx
      have e : z - x = -(x - z) := (neg_sub x z).symm
      rwa [norm_sub_rev, e, hg] at this
  rcases le_or_gt (g (x - z)) 0 with hg0 | hg0
  · rw [ENNReal.ofReal_of_nonpos hg0, mul_zero]
    exact bot_le
  · rw [edist_dist, dist_eq_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hreal

/-- **Weighted Hölder seminorm from cell pairs.** Let `g` be an even weight with the `0`-homogeneous
axis bounds `g(h) |h_j|^α ≤ G_j` (for the Hölder weights `g_i` of Chen and Hou, Part I, (C.1b),
`G = (1, g_i(0, 1))`). Suppose `‖f x - f z‖ g(x - z) ≤ C` on the near cell pairs of the window `W`
(`z` in the cell `(a + d, b ± e)` of the cell `(a, b)` of `x`, `x₀ ≤ z₀`), `‖f‖ ≤ M a b` on the
cells, and the far budgets: in each coordinate, `M · G_j ≤ R · gap^α` with the positive right gap
and `M · G_j ≤ L · gap^α` with the positive left gap, wherever there is a cell `W` indices away,
with `R, L ≥ 0` and `R + L ≤ C`. Then `[f]_{C_g(D)} ≤ C`. -/
theorem weightedSeminorm_le_of_cellPairs {y y' : ℕ → ℝ} {n m W : ℕ} (hy : Monotone y)
    (hy' : Monotone y') (hW : 1 ≤ W) {α : ℝ} (hα : 0 ≤ α) {D : Set (ℝ^2)}
    (hD : ∀ x ∈ D, y 0 ≤ x 0 ∧ y' 0 ≤ x 1) {f : ℝ^2 → E} {g : ℝ^2 → ℝ}
    (hg : ∀ h, g (-h) = g h) {G : Fin 2 → ℝ} (hgG : ∀ h j, g h * |h j| ^ α ≤ G j)
    {C R L : ℝ} {M : ℕ → ℕ → ℝ}
    (nearUp : ∀ a ≤ n, ∀ b ≤ m, ∀ d < W, ∀ e < W, a + d ≤ n → b + e ≤ m →
      ∀ x ∈ D, ∀ z ∈ D, x 0 ≤ z 0 → x ∈ box y y' n m a b → z ∈ box y y' n m (a + d) (b + e) →
        ‖f x - f z‖ * g (x - z) ≤ C)
    (nearDown : ∀ a ≤ n, ∀ b ≤ m, ∀ d < W, ∀ e < W, a + d ≤ n → e ≤ b →
      ∀ x ∈ D, ∀ z ∈ D, x 0 ≤ z 0 → x ∈ box y y' n m a b → z ∈ box y y' n m (a + d) (b - e) →
        ‖f x - f z‖ * g (x - z) ≤ C)
    (sup : ∀ a ≤ n, ∀ b ≤ m, ∀ x ∈ D, x ∈ box y y' n m a b → ‖f x‖ ≤ M a b)
    (right₀ : ∀ a b, a + W ≤ n → b ≤ m →
      0 < rightGap y W a ∧ M a b * G 0 ≤ R * rightGap y W a ^ α)
    (left₀ : ∀ a b, W ≤ a → a ≤ n → b ≤ m →
      0 < leftGap y W a ∧ M a b * G 0 ≤ L * leftGap y W a ^ α)
    (right₁ : ∀ a b, a ≤ n → b + W ≤ m →
      0 < rightGap y' W b ∧ M a b * G 1 ≤ R * rightGap y' W b ^ α)
    (left₁ : ∀ a b, a ≤ n → W ≤ b → b ≤ m →
      0 < leftGap y' W b ∧ M a b * G 1 ≤ L * leftGap y' W b ^ α)
    (hR : 0 ≤ R) (hL : 0 ≤ L) (hRL : R + L ≤ C) :
    weightedSeminorm g D f ≤ ENNReal.ofReal C := by
  have hC : 0 ≤ C := by linarith
  -- the real inequality on ordered pairs
  have key := forall_of_cellPairs (Φ := fun x z ↦ ‖f x - f z‖ * g (x - z) ≤ C) hy hD nearUp
    nearDown (by
      intro a c hac hcn b hbm d hdm hfar x hx z hz hxz hxb hzb
      rcases le_or_gt (g (x - z)) 0 with hg0 | hg0
      · exact (mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) hg0).trans hC
      have hsplit : ‖f x - f z‖ * g (x - z) ≤ ‖f x‖ * g (x - z) + ‖f z‖ * g (x - z) := by
        rw [← add_mul]
        exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) hg0.le
      have hMx := sup a (hac.trans hcn) b hbm x hx hxb
      have hMz := sup c hcn d hdm z hz hzb
      refine hsplit.trans ?_
      rcases hfar with h | h | h
      · -- far in the first coordinate: `x` uses its right gap, `z` its left gap
        have hgap := gap_le_abs_sub hy hW h hcn hxb.1 hzb.1
        have e₁ := right₀ a b (h.trans hcn) hbm
        have e₂ := left₀ c d (by omega) hcn hdm
        have : ‖f x‖ * g (x - z) ≤ R := norm_mul_le_of_gap (j := 0) hα hg0.le hMx
          (hgG _ 0) e₁.2 e₁.1 (by simpa [abs_sub_comm] using hgap.1)
        have : ‖f z‖ * g (x - z) ≤ L := norm_mul_le_of_gap (j := 0) hα hg0.le hMz
          (hgG _ 0) e₂.2 e₂.1 (by simpa [abs_sub_comm] using hgap.2)
        linarith
      · -- far in the second coordinate, `z` above `x`
        have hgap := gap_le_abs_sub hy' hW h hdm hxb.2 hzb.2
        have e₁ := right₁ a b (hac.trans hcn) (h.trans hdm)
        have e₂ := left₁ c d hcn (by omega) hdm
        have : ‖f x‖ * g (x - z) ≤ R := norm_mul_le_of_gap (j := 1) hα hg0.le hMx
          (hgG _ 1) e₁.2 e₁.1 (by simpa [abs_sub_comm] using hgap.1)
        have : ‖f z‖ * g (x - z) ≤ L := norm_mul_le_of_gap (j := 1) hα hg0.le hMz
          (hgG _ 1) e₂.2 e₂.1 (by simpa [abs_sub_comm] using hgap.2)
        linarith
      · -- far in the second coordinate, `z` below `x`
        have hgap := gap_le_abs_sub hy' hW h hbm hzb.2 hxb.2
        have e₁ := right₁ c d hcn (h.trans hbm)
        have e₂ := left₁ a b (hac.trans hcn) (by omega) hbm
        have : ‖f z‖ * g (x - z) ≤ R := norm_mul_le_of_gap (j := 1) hα hg0.le hMz
          (hgG _ 1) e₁.2 e₁.1 (by simpa [abs_sub_comm] using hgap.1)
        have : ‖f x‖ * g (x - z) ≤ L := norm_mul_le_of_gap (j := 1) hα hg0.le hMx
          (hgG _ 1) e₂.2 e₂.1 (by simpa [abs_sub_comm] using hgap.2)
        linarith)
  exact weightedSeminorm_le_of_forall_le hg key

end HolderSpace
