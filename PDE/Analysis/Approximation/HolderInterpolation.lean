/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.BilinearInterpolation
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Hölder quotients of piecewise linear functions and of their interpolation sources

Chen and Hou, Part II, App E.1. For a function that is affine on `[x_l, x_u]` and on `[z_l, z_u]`,
`x_u ≤ z_l`, the Hölder quotient `|f(x) - f(z)| / |x - z|^α` over the two cells is maximal at a
pair of endpoints (Lemma E.1, `abs_linearInterpolant_sub_le`); the same holds for functions that are
bilinear on `[x_l, x_u] × I_y` and `[z_l, z_u] × I_y` (Lemma E.2,
`abs_bilinearInterpolant_sub_le`). Both are stated as division-free upper bounds
`|f(x) - f(z)| ≤ M (z - x)^α` for any `0 ≤ α ≤ 1` and any `M` bounding the endpoint pairs.
The interpolation step is Jensen's inequality for the concave `t ↦ t^α`
(`lerp_rpow_le`), and Lemma E.2 is used in the form
`|I(x, z, y)| ≤ max(|I(x, z, y_l)|, |I(x, z, y_u)|)`.

Comparing `f` with its bilinear interpolants on the two cells adds the interpolation errors
(`abs_sub_le_of_bilinear_cells`, the display after Lemma E.2):
`|f(x, y) - f(z, y)| ≤ (h_x² Mₓ + h_y² M_y) / 8 + (h_z² Mₓ' + h_y² M_y') / 8 + M (z - x)^α`.

The first approach of App E.1 bounds increments near the origin by weighted derivatives: if `f`
is continuous on `[x, y]`, `0 ≤ x < y`, with derivative `f'` on `(x, y)` and `|f'(z)| √z ≤ A`
there, then `|f(y) - f(x)| ≤ 2A (√y - √x)` (`abs_sub_le_two_mul_sqrt_sub`), so
`|f(y) - f(x)| / √(y - x) ≤ 2A √(y - x) / (√x + √y)`.

## Main results

* `lerp_rpow_le`: the two-point Jensen inequality for `t ↦ t^α`, `0 ≤ α ≤ 1`.
* `abs_linearInterpolant_sub_le`: Lemma E.1, for functions affine on two intervals, a bound
  `M (z_b - x_a)^α` at the four endpoint pairs gives `|P(x) - Q(z)| ≤ M (z - x)^α`.
* `abs_bilinearInterpolant_sub_le`: Lemma E.2, the same for bilinear interpolants on two cells
  with the eight vertex pairs.
* `abs_sub_le_of_bilinear_cells`: the second approach of App E.1, the Hölder bound of `f` from the
  vertex pairs plus the bilinear interpolation errors on the two cells.
* `abs_sub_le_two_mul_sqrt_sub`: the first approach of App E.1, for `f` continuous on `[x, y]`,
  `0 ≤ x < y`, with `|f'(z)| √z ≤ A` on `(x, y)`: `|f(y) - f(x)| ≤ 2A (√y - √x)`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Appendix E.1, with
  Lemmas E.1 and E.2 in Appendix E.1.1. <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

namespace PDE.Analysis.Approximation

open Set

/-- Two-point Jensen inequality for `t ↦ t^α`, `0 ≤ α ≤ 1`, with weights `1 - s` and `s`. -/
theorem lerp_rpow_le {u v s α : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : s ∈ Icc (0 : ℝ) 1)
    (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    (1 - s) * u ^ α + s * v ^ α ≤ ((1 - s) * u + s * v) ^ α := by
  have h := (Real.concaveOn_rpow hα₀ hα₁).2 (mem_Ici.mpr hu) (mem_Ici.mpr hv)
    (by linarith [hs.2] : 0 ≤ 1 - s) hs.1 (by ring)
  simpa [smul_eq_mul] using h

/-- The value of the linear interpolant at `x ∈ [a, b]` as a convex combination with weight
`s = (x - a) / (b - a)`. -/
theorem linearInterpolant_eq_lerp {a b fa fb x : ℝ} (hab : a < b) :
    linearInterpolant a b fa fb x = (1 - (x - a) / (b - a)) * fa + (x - a) / (b - a) * fb := by
  have hne : b - a ≠ 0 := (sub_pos.mpr hab).ne'
  unfold linearInterpolant
  field_simp
  ring

/-- **Part II, Lemma E.1.** Let `P` be affine on `[x_l, x_u]` with values `p_l`, `p_u` and `Q`
affine on `[z_l, z_u]` with values `q_l`, `q_u`, where `x_u ≤ z_l`. If
`|p_a - q_b| ≤ M (z_b - x_a)^α` for the four endpoint pairs, with `0 ≤ α ≤ 1`, then
`|P x - Q z| ≤ M (z - x)^α` for all `x ∈ [x_l, x_u]`, `z ∈ [z_l, z_u]`. (`M ≥ 0` follows from the
first endpoint bound, since `z_l - x_l > 0`.) -/
theorem abs_linearInterpolant_sub_le {xl xu zl zu pl pu ql qu M α : ℝ}
    (hx : xl < xu) (hz : zl < zu) (hxz : xu ≤ zl) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (hll : |pl - ql| ≤ M * (zl - xl) ^ α) (hlu : |pl - qu| ≤ M * (zu - xl) ^ α)
    (hul : |pu - ql| ≤ M * (zl - xu) ^ α) (huu : |pu - qu| ≤ M * (zu - xu) ^ α)
    {x z : ℝ} (hxm : x ∈ Icc xl xu) (hzm : z ∈ Icc zl zu) :
    |linearInterpolant xl xu pl pu x - linearInterpolant zl zu ql qu z| ≤ M * (z - x) ^ α := by
  have hM : 0 ≤ M := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans hll)
    (Real.rpow_pos_of_pos (by linarith) _)
  set s := (x - xl) / (xu - xl)
  set r := (z - zl) / (zu - zl)
  have hs : s ∈ Icc (0 : ℝ) 1 :=
    unitInterval.div_mem (sub_nonneg.2 hxm.1) (sub_pos.2 hx).le (sub_le_sub_right hxm.2 _)
  have hr : r ∈ Icc (0 : ℝ) 1 :=
    unitInterval.div_mem (sub_nonneg.2 hzm.1) (sub_pos.2 hz).le (sub_le_sub_right hzm.2 _)
  have hxs : x = (1 - s) * xl + s * xu := by
    simp only [s]
    field_simp [(sub_pos.mpr hx).ne']
    ring
  have hzr : z = (1 - r) * zl + r * zu := by
    simp only [r]
    field_simp [(sub_pos.mpr hz).ne']
    ring
  rw [linearInterpolant_eq_lerp hx, linearInterpolant_eq_lerp hz]
  -- the difference as a convex combination of the endpoint differences
  have hid : (1 - s) * pl + s * pu - ((1 - r) * ql + r * qu) =
      (1 - s) * ((1 - r) * (pl - ql) + r * (pl - qu)) +
        s * ((1 - r) * (pu - ql) + r * (pu - qu)) := by ring
  rw [hid]
  have h1s : 0 ≤ 1 - s := by linarith [hs.2]
  have h1r : 0 ≤ 1 - r := by linarith [hr.2]
  have hcomb {A B C D : ℝ} (hA : |A| ≤ C) (hB : |B| ≤ D) {w : ℝ} (hw : w ∈ Icc (0 : ℝ) 1) :
      |(1 - w) * A + w * B| ≤ (1 - w) * C + w * D := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [hw.2]), abs_of_nonneg hw.1]
    exact add_le_add (mul_le_mul_of_nonneg_left hA (by linarith [hw.2]))
      (mul_le_mul_of_nonneg_left hB hw.1)
  -- Jensen in `z` for each `x`-endpoint, then in `x`
  have hjl : (1 - r) * (M * (zl - xl) ^ α) + r * (M * (zu - xl) ^ α) ≤ M * (z - xl) ^ α := by
    have := lerp_rpow_le (u := zl - xl) (v := zu - xl) (by linarith) (by linarith) hr hα₀ hα₁
    have hz' : (1 - r) * (zl - xl) + r * (zu - xl) = z - xl := by rw [hzr]; ring
    rw [hz'] at this
    nlinarith
  have hju : (1 - r) * (M * (zl - xu) ^ α) + r * (M * (zu - xu) ^ α) ≤ M * (z - xu) ^ α := by
    have := lerp_rpow_le (u := zl - xu) (v := zu - xu) (by linarith) (by linarith) hr hα₀ hα₁
    have hz' : (1 - r) * (zl - xu) + r * (zu - xu) = z - xu := by rw [hzr]; ring
    rw [hz'] at this
    nlinarith
  have hjx : (1 - s) * (M * (z - xl) ^ α) + s * (M * (z - xu) ^ α) ≤ M * (z - x) ^ α := by
    have := lerp_rpow_le (u := z - xl) (v := z - xu) (by linarith [hzm.1]) (by linarith [hzm.1])
      hs hα₀ hα₁
    have hx' : (1 - s) * (z - xl) + s * (z - xu) = z - x := by rw [hxs]; ring
    rw [hx'] at this
    nlinarith
  calc _ ≤ (1 - s) * ((1 - r) * (M * (zl - xl) ^ α) + r * (M * (zu - xl) ^ α)) +
        s * ((1 - r) * (M * (zl - xu) ^ α) + r * (M * (zu - xu) ^ α)) :=
        hcomb (hcomb hll hlu hr) (hcomb hul huu hr) hs
    _ ≤ (1 - s) * (M * (z - xl) ^ α) + s * (M * (z - xu) ^ α) :=
        add_le_add (mul_le_mul_of_nonneg_left hjl h1s) (mul_le_mul_of_nonneg_left hju hs.1)
    _ ≤ M * (z - x) ^ α := hjx

/-- **Part II, Lemma E.2.** Let `F` be bilinear on `[x_l, x_u] × [y_l, y_u]` and `G` bilinear on
`[z_l, z_u] × [y_l, y_u]` (the bilinear interpolants of the vertex values), `x_u ≤ z_l`. If
`|F(x_a, y_c) - G(z_b, y_c)| ≤ M (z_b - x_a)^α` for the eight vertex pairs on common horizontal
lines, then `|F(x, y) - G(z, y)| ≤ M (z - x)^α` on the two cells. A degenerate `y`-range
`y_l = y_u` makes both interpolants `0` (division by zero), and an empty one is vacuous. -/
theorem abs_bilinearInterpolant_sub_le {F G : ℝ → ℝ → ℝ} {xl xu zl zu yl yu M α : ℝ}
    (hx : xl < xu) (hz : zl < zu) (hxz : xu ≤ zl)
    (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (hcorner : ∀ y ∈ ({yl, yu} : Set ℝ), |F xl y - G zl y| ≤ M * (zl - xl) ^ α ∧
      |F xl y - G zu y| ≤ M * (zu - xl) ^ α ∧ |F xu y - G zl y| ≤ M * (zl - xu) ^ α ∧
      |F xu y - G zu y| ≤ M * (zu - xu) ^ α)
    {x z y : ℝ} (hxm : x ∈ Icc xl xu) (hzm : z ∈ Icc zl zu) (hym : y ∈ Icc yl yu) :
    |bilinearInterpolant F xl xu yl yu x y - bilinearInterpolant G zl zu yl yu z y| ≤
      M * (z - x) ^ α := by
  have hM : 0 ≤ M := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hcorner yl (by simp)).1)
    (Real.rpow_pos_of_pos (by linarith) _)
  rcases lt_trichotomy yl yu with hy | rfl | hy
  rotate_left
  · simp only [bilinearInterpolant, linearInterpolant, sub_self, div_zero, zero_mul, add_zero,
      mul_zero, abs_zero]
    exact mul_nonneg hM (Real.rpow_nonneg (by linarith [hxm.2, hzm.1]) _)
  · exact absurd (hym.1.trans hym.2) (not_le.mpr hy)
  -- on each horizontal line `y_c` the difference is a Lemma E.1 difference
  have hline (c : ℝ) (hc : c ∈ ({yl, yu} : Set ℝ)) :
      |linearInterpolant xl xu (F xl c) (F xu c) x - linearInterpolant zl zu (G zl c) (G zu c) z|
        ≤ M * (z - x) ^ α := by
    obtain ⟨h1, h2, h3, h4⟩ := hcorner c hc
    exact abs_linearInterpolant_sub_le hx hz hxz hα₀ hα₁ h1 h2 h3 h4 hxm hzm
  -- the difference is affine in `y`
  set t := (y - yl) / (yu - yl)
  have ht : t ∈ Icc (0 : ℝ) 1 :=
    unitInterval.div_mem (sub_nonneg.2 hym.1) (sub_pos.2 hy).le (sub_le_sub_right hym.2 _)
  have hid : bilinearInterpolant F xl xu yl yu x y - bilinearInterpolant G zl zu yl yu z y =
      (1 - t) * (linearInterpolant xl xu (F xl yl) (F xu yl) x -
        linearInterpolant zl zu (G zl yl) (G zu yl) z) +
      t * (linearInterpolant xl xu (F xl yu) (F xu yu) x -
        linearInterpolant zl zu (G zl yu) (G zu yu) z) := by
    simp only [bilinearInterpolant, linearInterpolant_eq_lerp hx, linearInterpolant_eq_lerp hz,
      linearInterpolant_eq_lerp hy, t]
    ring
  rw [hid]
  have h0 := hline yl (by simp)
  have h1 := hline yu (by simp)
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [ht.2]), abs_of_nonneg ht.1]
  calc (1 - t) * |linearInterpolant xl xu (F xl yl) (F xu yl) x -
        linearInterpolant zl zu (G zl yl) (G zu yl) z| +
      t * |linearInterpolant xl xu (F xl yu) (F xu yu) x -
        linearInterpolant zl zu (G zl yu) (G zu yu) z| ≤
      (1 - t) * (M * (z - x) ^ α) + t * (M * (z - x) ^ α) :=
        add_le_add (mul_le_mul_of_nonneg_left h0 (by linarith [ht.2]))
          (mul_le_mul_of_nonneg_left h1 ht.1)
    _ = M * (z - x) ^ α := by ring

/-- **Part II, App E.1, second approach.** For `f` on two cells `[x_l, x_u] × [y_l, y_u]` and
`[z_l, z_u] × [y_l, y_u]`, `x_u ≤ z_l`, with pure second derivatives bounded by `Mₓ`, `M_y` on the
first and `Mₓ'`, `M_y'` on the second cell, and the vertex pairs bounded by `M (z_b - x_a)^α`,
`|f(x, y) - f(z, y)| ≤ ((x_u - x_l)² Mₓ + (y_u - y_l)² M_y) / 8 +
((z_u - z_l)² Mₓ' + (y_u - y_l)² M_y') / 8 + M (z - x)^α`. The regularity hypotheses are separate
for the two cells (derivative fields `fx, fxx, fy, fyy` and `gx, gxx, gy, gyy`), so `f` need not
be differentiable between them. Dividing by `(z - x)^α` for `x < z` bounds the Hölder quotient. -/
theorem abs_sub_le_of_bilinear_cells {f fx fxx fy fyy gx gxx gy gyy : ℝ → ℝ → ℝ}
    {xl xu zl zu yl yu Mx My Mx' My' M α : ℝ}
    (hx : xl < xu) (hz : zl < zu) (hy : yl < yu) (hxz : xu ≤ zl)
    (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (hcontX : ∀ v ∈ Icc yl yu, ContinuousOn (fun u ↦ f u v) (Icc xl xu))
    (hderivX : ∀ v ∈ Icc yl yu, ∀ u ∈ Ioo xl xu, HasDerivAt (fun w ↦ f w v) (fx u v) u)
    (hderivXX : ∀ v ∈ Icc yl yu, ∀ u ∈ Ioo xl xu, HasDerivAt (fun w ↦ fx w v) (fxx u v) u)
    (hboundX : ∀ v ∈ Icc yl yu, ∀ u ∈ Ioo xl xu, |fxx u v| ≤ Mx)
    (hcontY : ∀ u ∈ Icc xl xu, ContinuousOn (f u) (Icc yl yu))
    (hderivY : ∀ u ∈ Icc xl xu, ∀ v ∈ Ioo yl yu, HasDerivAt (f u) (fy u v) v)
    (hderivYY : ∀ u ∈ Icc xl xu, ∀ v ∈ Ioo yl yu, HasDerivAt (fy u) (fyy u v) v)
    (hboundY : ∀ u ∈ Icc xl xu, ∀ v ∈ Ioo yl yu, |fyy u v| ≤ My)
    (hcontX' : ∀ v ∈ Icc yl yu, ContinuousOn (fun u ↦ f u v) (Icc zl zu))
    (hderivX' : ∀ v ∈ Icc yl yu, ∀ u ∈ Ioo zl zu, HasDerivAt (fun w ↦ f w v) (gx u v) u)
    (hderivXX' : ∀ v ∈ Icc yl yu, ∀ u ∈ Ioo zl zu, HasDerivAt (fun w ↦ gx w v) (gxx u v) u)
    (hboundX' : ∀ v ∈ Icc yl yu, ∀ u ∈ Ioo zl zu, |gxx u v| ≤ Mx')
    (hcontY' : ∀ u ∈ Icc zl zu, ContinuousOn (f u) (Icc yl yu))
    (hderivY' : ∀ u ∈ Icc zl zu, ∀ v ∈ Ioo yl yu, HasDerivAt (f u) (gy u v) v)
    (hderivYY' : ∀ u ∈ Icc zl zu, ∀ v ∈ Ioo yl yu, HasDerivAt (gy u) (gyy u v) v)
    (hboundY' : ∀ u ∈ Icc zl zu, ∀ v ∈ Ioo yl yu, |gyy u v| ≤ My')
    (hcorner : ∀ y ∈ ({yl, yu} : Set ℝ), |f xl y - f zl y| ≤ M * (zl - xl) ^ α ∧
      |f xl y - f zu y| ≤ M * (zu - xl) ^ α ∧ |f xu y - f zl y| ≤ M * (zl - xu) ^ α ∧
      |f xu y - f zu y| ≤ M * (zu - xu) ^ α)
    {x z y : ℝ} (hxm : x ∈ Icc xl xu) (hzm : z ∈ Icc zl zu) (hym : y ∈ Icc yl yu) :
    |f x y - f z y| ≤ (Mx * (xu - xl) ^ 2 / 8 + My * (yu - yl) ^ 2 / 8) +
      (Mx' * (zu - zl) ^ 2 / 8 + My' * (yu - yl) ^ 2 / 8) + M * (z - x) ^ α := by
  have eX := abs_sub_bilinearInterpolant_le hx hy hcontX hderivX hderivXX hboundX
    hcontY hderivY hderivYY hboundY hxm hym
  have eZ := abs_sub_bilinearInterpolant_le hz hy hcontX' hderivX' hderivXX' hboundX'
    hcontY' hderivY' hderivYY' hboundY' hzm hym
  have hE2 := abs_bilinearInterpolant_sub_le (F := f) (G := f) hx hz hxz hα₀ hα₁ hcorner
    hxm hzm hym
  have hid : f x y - f z y = (f x y - bilinearInterpolant f xl xu yl yu x y) -
      (f z y - bilinearInterpolant f zl zu yl yu z y) +
      (bilinearInterpolant f xl xu yl yu x y - bilinearInterpolant f zl zu yl yu z y) := by ring
  rw [hid]
  refine (abs_add_le _ _).trans ?_
  have := abs_sub (f x y - bilinearInterpolant f xl xu yl yu x y)
    (f z y - bilinearInterpolant f zl zu yl yu z y)
  linarith

/-- **Part II, App E.1, first approach.** Let `0 ≤ x < y` and let `f` be continuous on `[x, y]`
with derivative `f'` on `(x, y)`. If `|f'(z)| √z ≤ A` on `(x, y)`, then
`|f(y) - f(x)| ≤ 2A (√y - √x)`. -/
theorem abs_sub_le_two_mul_sqrt_sub {f f' : ℝ → ℝ} {x y A : ℝ} (hx : 0 ≤ x) (hxy : x < y)
    (hcont : ContinuousOn f (Icc x y)) (hderiv : ∀ z ∈ Ioo x y, HasDerivAt f (f' z) z)
    (hbound : ∀ z ∈ Ioo x y, |f' z| * Real.sqrt z ≤ A) :
    |f y - f x| ≤ 2 * A * (Real.sqrt y - Real.sqrt x) := by
  obtain ⟨c, hc, hmvt⟩ := exists_ratio_hasDerivAt_eq_ratio_slope f f' hxy hcont hderiv
    Real.sqrt (fun z ↦ 1 / (2 * Real.sqrt z)) Real.continuous_sqrt.continuousOn
    (fun z hz ↦ by
      have hz0 : z ≠ 0 := (lt_of_le_of_lt hx hz.1).ne'
      simpa [one_div] using Real.hasDerivAt_sqrt hz0)
  have hc0 : 0 < c := lt_of_le_of_lt hx hc.1
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc0
  have hsq : 0 ≤ Real.sqrt y - Real.sqrt x := sub_nonneg.mpr (Real.sqrt_le_sqrt hxy.le)
  -- `f y - f x = 2 √c f'(c) (√y - √x)`
  have heq : f y - f x = 2 * Real.sqrt c * f' c * (Real.sqrt y - Real.sqrt x) := by
    field_simp at hmvt
    linarith
  rw [heq, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hsc,
    abs_of_nonneg hsq]
  have := hbound c hc
  nlinarith

/-- The identity behind the first approach: `2 (√y - √x) / √(y - x) = 2 √(y - x) / (√x + √y)`
for `0 ≤ x < y`. -/
theorem two_mul_sqrt_sub_div {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    2 * (Real.sqrt y - Real.sqrt x) / Real.sqrt (y - x) =
      2 * Real.sqrt (y - x) / (Real.sqrt x + Real.sqrt y) := by
  have hy : 0 < y := lt_of_le_of_lt hx hxy
  have hd : 0 < Real.sqrt (y - x) := Real.sqrt_pos.mpr (sub_pos.mpr hxy)
  have hs : 0 < Real.sqrt x + Real.sqrt y := by
    have := Real.sqrt_pos.mpr hy
    positivity
  rw [div_eq_div_iff hd.ne' hs.ne']
  have h1 : Real.sqrt (y - x) * Real.sqrt (y - x) = y - x := Real.mul_self_sqrt (by linarith)
  have h2 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx
  have h3 : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy.le
  nlinarith

end PDE.Analysis.Approximation
