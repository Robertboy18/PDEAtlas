/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.LinearInterpolation

/-!
# Bounds on intervals and cells from endpoint values and second derivatives

On an interval of length `h` a function continuous on the closed interval, with two derivatives
inside, is at most its endpoint bound plus `h² / 8` times a bound of its second derivative
(`abs_le_of_abs_endpoint_le`). This is the "second order method"
of Chen and Hou, Part II, (C.13), the same inequality as Part I, (C.19). Applied first in `y` on
the two vertical edges of a rectangle and then in `x`, it bounds a function on a cell
`[a, b] × [c, d]` by a bound of its four vertex values plus `Mₓ (b - a)² / 8 + M_y (d - c)² / 8`
(`abs_le_of_abs_corner_le`, Part II (C.14)); no mixed derivative enters.

For a family `F k l` of partial derivatives (`F (k + 1) l = ∂ₓ F k l`, `F k (l + 1) = ∂_y F k l`)
the one-step bound gives the recursion `A_{kl} ≥ B_{kl} + (h₁² A_{k+2,l} + h₂² A_{k,l+2}) / 8` of
Part II, App C.2.2: bounds `A` outside a box `k < K`, `l < L` (zero for a polynomial piece,
crude a priori bounds otherwise) and vertex bounds `B` inside it bound every member of the family
on the cell (`abs_le_of_cell_recursion`). The induction may take the indices in any order in
which `(k + 2, l)` and `(k, l + 2)` come first; the proof inducts on `(K - k) + (L - l)`.

## Main results

* `abs_le_of_abs_endpoint_le`: for `f` continuous on `[a, b]` with `f'`, `f''` on `(a, b)`, a
  bound `B` of the two endpoint values and a bound `M` of `|f''|` give `|f| ≤ B + M (b - a)² / 8`
  on `[a, b]`.
* `abs_le_of_abs_corner_le`: with the slices continuous on the closed intervals and twice
  differentiable inside, a bound `B` of the four vertex values and bounds `Mₓ`, `M_y` of the pure
  second derivatives give `|f| ≤ B + Mₓ (b - a)² / 8 + M_y (d - c)² / 8` on the cell.
* `abs_le_of_cell_recursion`: for a family `F k l` with the slice continuity and derivatives
  above, bounds satisfying the recursion of App C.2.2 bound every member of the family on the
  cell.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Appendix C.4, (C.19).
  <https://arxiv.org/abs/2210.07191v4>
* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Appendix C.2, (C.13)
  and (C.14), and Appendix C.2.2.
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

namespace PDE.Analysis.Approximation

open Set

/-- **Part II (C.13), Part I (C.19).** Let `f` be continuous on `[a, b]`, with derivative `f'` and
second derivative `f''` on `(a, b)`. A bound `B` of the two endpoint values and a bound `M` of
`|f''|` on `(a, b)` bound `f` on `[a, b]` by `B + M (b - a)² / 8`, for instance with
`B = max(|f a|, |f b|)` and `M = ‖f''‖_{L^∞}`. -/
theorem abs_le_of_abs_endpoint_le {f f' f'' : ℝ → ℝ} {a b x M B : ℝ}
    (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ y ∈ Ioo a b, HasDerivAt f (f' y) y)
    (hderiv' : ∀ y ∈ Ioo a b, HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Ioo a b, |f'' y| ≤ M) (ha : |f a| ≤ B) (hb : |f b| ≤ B)
    (hx : x ∈ Icc a b) : |f x| ≤ B + M * (b - a) ^ 2 / 8 := by
  rcases (hx.1.trans hx.2).eq_or_lt with hab | hab
  · have hxa : x = a := le_antisymm (hab ▸ hx.2) hx.1
    subst hxa
    rw [← hab, sub_self]
    simpa using ha
  · have herr := abs_sub_linearInterpolant_le_uniform hab hcont hderiv hderiv' hbound hx
    have hden : 0 < b - a := sub_pos.mpr hab
    have hw₀ : 0 ≤ (b - x) / (b - a) := div_nonneg (sub_nonneg.mpr hx.2) hden.le
    have hw₁ : 0 ≤ (x - a) / (b - a) := div_nonneg (sub_nonneg.mpr hx.1) hden.le
    have hsum : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by
      rw [← add_div, show b - x + (x - a) = b - a by ring, div_self hden.ne']
    have hL : |linearInterpolant a b (f a) (f b) x| ≤ B := by
      unfold linearInterpolant
      calc _ ≤ |(b - x) / (b - a) * f a| + |(x - a) / (b - a) * f b| := abs_add_le _ _
        _ = (b - x) / (b - a) * |f a| + (x - a) / (b - a) * |f b| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hw₀, abs_of_nonneg hw₁]
        _ ≤ (b - x) / (b - a) * B + (x - a) / (b - a) * B :=
          add_le_add (mul_le_mul_of_nonneg_left ha hw₀) (mul_le_mul_of_nonneg_left hb hw₁)
        _ = B := by rw [← add_mul, hsum, one_mul]
    calc |f x| = |(f x - linearInterpolant a b (f a) (f b) x) +
          linearInterpolant a b (f a) (f b) x| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ M * (b - a) ^ 2 / 8 + B := add_le_add herr hL
      _ = _ := add_comm _ _

/-- **Part II (C.14).** A bound `B` of the four vertex values of `f` on `[a, b] × [c, d]` and
bounds `Mₓ`, `M_y` of the pure second derivatives bound `f` on the cell by
`B + Mₓ (b - a)² / 8 + M_y (d - c)² / 8`. Each slice `u ↦ f u v`, `v ∈ [c, d]`, is continuous on
`[a, b]` with derivatives `fx`, `fxx` on `(a, b)`, and each slice `f u`, `u ∈ [a, b]`, is
continuous on `[c, d]` with derivatives `fy`, `fyy` on `(c, d)`; the mixed derivative does not
enter. -/
theorem abs_le_of_abs_corner_le {f fx fxx fy fyy : ℝ → ℝ → ℝ} {a b c d Mx My B x y : ℝ}
    (hcontX : ∀ v ∈ Icc c d, ContinuousOn (fun u ↦ f u v) (Icc a b))
    (hderivX : ∀ v ∈ Icc c d, ∀ u ∈ Ioo a b, HasDerivAt (fun z ↦ f z v) (fx u v) u)
    (hderivXX : ∀ v ∈ Icc c d, ∀ u ∈ Ioo a b, HasDerivAt (fun z ↦ fx z v) (fxx u v) u)
    (hboundX : ∀ v ∈ Icc c d, ∀ u ∈ Ioo a b, |fxx u v| ≤ Mx)
    (hcontY : ∀ u ∈ Icc a b, ContinuousOn (f u) (Icc c d))
    (hderivY : ∀ u ∈ Icc a b, ∀ v ∈ Ioo c d, HasDerivAt (f u) (fy u v) v)
    (hderivYY : ∀ u ∈ Icc a b, ∀ v ∈ Ioo c d, HasDerivAt (fy u) (fyy u v) v)
    (hboundY : ∀ u ∈ Icc a b, ∀ v ∈ Ioo c d, |fyy u v| ≤ My)
    (hac : |f a c| ≤ B) (had : |f a d| ≤ B) (hbc : |f b c| ≤ B) (hbd : |f b d| ≤ B)
    (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) :
    |f x y| ≤ B + Mx * (b - a) ^ 2 / 8 + My * (d - c) ^ 2 / 8 := by
  have hab : a ≤ b := hx.1.trans hx.2
  have hA : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hB : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hcolumn (u : ℝ) (hu : u ∈ Icc a b) (hc : |f u c| ≤ B) (hd : |f u d| ≤ B) :
      |f u y| ≤ B + My * (d - c) ^ 2 / 8 :=
    abs_le_of_abs_endpoint_le (hcontY u hu) (hderivY u hu) (hderivYY u hu) (hboundY u hu) hc hd hy
  have h := abs_le_of_abs_endpoint_le (hcontX y hy) (hderivX y hy) (hderivXX y hy) (hboundX y hy)
    (hcolumn a hA hac had) (hcolumn b hB hbc hbd) hx
  linarith

/-- **Part II, App C.2.2 (the recursion behind (C.14)).** Let `F k l` be a family of partial
derivatives on the cell `[a, b] × [c, d]`: for `k ≤ K`, `l < L` the slices `u ↦ F k l u v`,
`v ∈ [c, d]`, are continuous on `[a, b]` with derivative `F (k + 1) l` on `(a, b)`, and for
`k < K`, `l ≤ L` the slices `F k l u`, `u ∈ [a, b]`, are continuous on `[c, d]` with derivative
`F k (l + 1)` on `(c, d)`. Suppose `A k l` bounds `F k l` on the cell whenever `K ≤ k` or
`L ≤ l` (for a polynomial piece of degree at most `d` in each variable, `K = L = d + 1` and
`A = 0` there), `B k l` bounds the four vertex values of `F k l` inside the box, and
`B k l + ((b - a)² A (k + 2) l + (d - c)² A k (l + 2)) / 8 ≤ A k l` inside the box. Then `A k l`
bounds `F k l` on the cell for every `k`, `l`.

The recursion inequalities require no order of evaluation. -/
theorem abs_le_of_cell_recursion {F : ℕ → ℕ → ℝ → ℝ → ℝ} {a b c d : ℝ} {K L : ℕ}
    {A B : ℕ → ℕ → ℝ}
    (hcontX : ∀ k ≤ K, ∀ l < L, ∀ v ∈ Icc c d, ContinuousOn (fun u ↦ F k l u v) (Icc a b))
    (hderivX : ∀ k ≤ K, ∀ l < L, ∀ v ∈ Icc c d, ∀ u ∈ Ioo a b,
      HasDerivAt (fun z ↦ F k l z v) (F (k + 1) l u v) u)
    (hcontY : ∀ k < K, ∀ l ≤ L, ∀ u ∈ Icc a b, ContinuousOn (F k l u) (Icc c d))
    (hderivY : ∀ k < K, ∀ l ≤ L, ∀ u ∈ Icc a b, ∀ v ∈ Ioo c d,
      HasDerivAt (F k l u) (F k (l + 1) u v) v)
    (htop : ∀ k l, K ≤ k ∨ L ≤ l → ∀ u ∈ Icc a b, ∀ v ∈ Icc c d, |F k l u v| ≤ A k l)
    (hcorner : ∀ k < K, ∀ l < L, |F k l a c| ≤ B k l ∧ |F k l a d| ≤ B k l ∧
      |F k l b c| ≤ B k l ∧ |F k l b d| ≤ B k l)
    (hrec : ∀ k < K, ∀ l < L,
      B k l + ((b - a) ^ 2 * A (k + 2) l + (d - c) ^ 2 * A k (l + 2)) / 8 ≤ A k l)
    (k l : ℕ) {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc c d) : |F k l u v| ≤ A k l := by
  -- strong induction on the distance `(K - k) + (L - l)` to the outside of the box
  suffices H : ∀ m, ∀ k l, (K - k) + (L - l) ≤ m → ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      |F k l u v| ≤ A k l from H _ k l le_rfl u hu v hv
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro k l hkl u hu v hv
    by_cases hbox : K ≤ k ∨ L ≤ l
    · exact htop k l hbox u hu v hv
    push Not at hbox
    obtain ⟨hk, hl⟩ := hbox
    have hx2 : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d, |F (k + 2) l u v| ≤ A (k + 2) l := by
      intro u hu v hv
      by_cases hk2 : K ≤ k + 2
      · exact htop _ _ (Or.inl hk2) u hu v hv
      · exact ih ((K - (k + 2)) + (L - l)) (by omega) _ _ le_rfl u hu v hv
    have hy2 : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d, |F k (l + 2) u v| ≤ A k (l + 2) := by
      intro u hu v hv
      by_cases hl2 : L ≤ l + 2
      · exact htop _ _ (Or.inr hl2) u hu v hv
      · exact ih ((K - k) + (L - (l + 2))) (by omega) _ _ le_rfl u hu v hv
    obtain ⟨hac, had, hbc, hbd⟩ := hcorner k hk l hl
    have h := abs_le_of_abs_corner_le (f := F k l) (fx := F (k + 1) l) (fxx := F (k + 2) l)
      (fy := F k (l + 1)) (fyy := F k (l + 2)) (Mx := A (k + 2) l) (My := A k (l + 2))
      (hcontX k hk.le l hl) (hderivX k hk.le l hl) (hderivX (k + 1) hk l hl)
      (fun v hv u hu ↦ hx2 u (Ioo_subset_Icc_self hu) v hv)
      (hcontY k hk l hl.le) (hderivY k hk l hl.le) (hderivY k hk (l + 1) hl)
      (fun u hu v hv ↦ hy2 u hu v (Ioo_subset_Icc_self hv)) hac had hbc hbd hu hv
    have := hrec k hk l hl
    nlinarith

end PDE.Analysis.Approximation
