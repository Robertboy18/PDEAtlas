/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.HermiteBounds

/-!
# Slopes and value bounds from Hermite data on a cell

Continuation of `HermiteBounds` (Chen and Hou, Part II, Supplementary material II, Sections 8.3.3
and 8.3.4). The slope errors of the Hermite interpolants on `[x₀, x₁]`, `x₁ = x₀ + h`, are
`|f' - H₅'| ≤ L h⁴ / 96` for an `L`-Lipschitz fourth derivative on `[x₀, x₀ + 2h]` (8.27) and
`|f' - H₄'| ≤ 2 L h³ / 81` for an `L`-Lipschitz third derivative on `[x₀, x₁]` (8.36). Each
applies the remainder bound to the error of the slope, whose zeros are the nodes with prescribed
slope together with one Rolle point between consecutive interpolated values. Combined with the
bounds of the interpolants they bound `f` and `f'` on the cell by the data.

## Main results

* `abs_deriv_sub_hermiteQuartic_le_left`: `|f' - H₅'| ≤ L h⁴ / 96` on `[x₀, x₁]` for an
  `L`-Lipschitz fourth derivative on `[x₀, x₀ + 2h]` (8.27).
* `abs_deriv_sub_hermiteCubic_le_left`: `|f' - H₄'| ≤ 2 L h³ / 81` on `[x₀, x₁]` for an
  `L`-Lipschitz third derivative there (8.36).
* `abs_le_of_hermiteCubic`: `|f| ≤ hermiteCubicBound + L h⁴ / 384` on `[x₀, x₁]`.
* `abs_le_of_hermiteQuartic`: `|f| ≤ hermiteCubicBound + |l₂ - G₄(2)| / 64 + L h⁵ / 1200` on
  `[x₀, x₁]`.
* `abs_deriv_le_of_hermiteCubic`: `|f'| ≤ hermiteSlopeBound / h + 2 L h³ / 81` on `[x₀, x₁]`.
* `abs_deriv_le_of_hermiteQuartic`:
  `|f'| ≤ (hermiteSlopeBound + |l₂ - G₄(2)| / (12 √3)) / h + L h⁴ / 96` on `[x₀, x₁]`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Supplementary
  material II (in the same PDF), Sections 8.3.3 and 8.3.4, (8.27)-(8.36).
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

namespace PDE.Analysis.Approximation

open Set Polynomial

/-- `t (1 - t) (2 - t) max(t, 1 - t) ≤ 1/4` on `[0, 1]`, the nodal bound behind (8.27). -/
theorem quarticSlopeNodal_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t * (1 - t) * (2 - t) * max t (1 - t) ≤ 1 / 4 := by
  obtain ⟨h0, h1⟩ := ht
  rcases le_total t (1 - t) with hle | hle
  · rw [max_eq_right hle]
    -- `(2t - t²) (1 - t)² = (1 - q) q` with `q = (1 - t)²`
    have hid : t * (1 - t) * (2 - t) * (1 - t) = (1 - (1 - t) ^ 2) * (1 - t) ^ 2 := by ring
    rw [hid]
    nlinarith [sq_nonneg ((1 - t) ^ 2 - 1 / 2)]
  · rw [max_eq_left hle]
    have hA : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
    have hB : t * (2 - t) ≤ 1 := by nlinarith [sq_nonneg (t - 1)]
    have hid : t * (1 - t) * (2 - t) * t = (t * (1 - t)) * (t * (2 - t)) := by ring
    rw [hid]
    have hA0 : 0 ≤ t * (1 - t) := mul_nonneg h0 (by linarith)
    calc (t * (1 - t)) * (t * (2 - t)) ≤ 1 / 4 * 1 :=
          mul_le_mul hA hB (mul_nonneg h0 (by linarith)) (by norm_num)
      _ = 1 / 4 := by ring

/-- The slope error `Φ 1 - p'` of a polynomial of degree at most `n + 1` vanishing at the `n + 1`
distinct points of `s ⊆ [a, b]` is at most `L / (n + 1)! |∏_{z ∈ s} (x - z)|` on `[a, b]` when
`Φ (n + 1)` is `L`-Lipschitz there: the remainder bound applied to the chain
`Φ (k + 1) - p⁽ᵏ⁺¹⁾`. -/
private theorem abs_deriv_sub_eval_le_of_lipschitz {a b L : ℝ} {n : ℕ} (Φ : ℕ → ℝ → ℝ)
    (hcontinuous : ∀ j < n + 2, ContinuousOn (Φ j) (Icc a b))
    (hderiv : ∀ j < n + 1, ∀ z ∈ Ioo a b, HasDerivAt (Φ j) (Φ (j + 1) z) z)
    (hlip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |Φ (n + 1) x - Φ (n + 1) y| ≤ L * |x - y|)
    (p : ℝ[X]) (hp : p.natDegree ≤ n + 1) (s : Multiset ℝ) (hs : s.Nodup)
    (hcard : s.card = n + 1) (hmem : ∀ z ∈ s, z ∈ Icc a b)
    (hzero : ∀ z ∈ s, Φ 1 z = (derivative p).eval z) {x : ℝ} (hx : x ∈ Icc a b) :
    |Φ 1 x - (derivative p).eval x| ≤ L / (n + 1).factorial * |(s.map fun z ↦ x - z).prod| := by
  have hconst (u v : ℝ) : (derivative^[n + 1] p).eval u = (derivative^[n + 1] p).eval v := by
    have := natDegree_iterate_derivative p (n + 1)
    rw [eq_C_of_natDegree_eq_zero (by omega : (derivative^[n + 1] p).natDegree = 0), eval_C,
      eval_C]
  have hrem := abs_sub_eval_le_of_lipschitz (n := n)
    (fun k y ↦ Φ (k + 1) y - (derivative^[k + 1] p).eval y)
    (fun k hk ↦
      (hcontinuous (k + 1) (by omega)).sub (derivative^[k + 1] p).continuous.continuousOn)
    (fun k hk z hz ↦ by
      convert (hderiv (k + 1) (by omega) z hz).sub ((derivative^[k + 1] p).hasDerivAt z) using 1
      simp only [Function.iterate_succ_apply'])
    (fun u hu v hv ↦ by simpa only [hconst u v, sub_sub_sub_cancel_right] using hlip u hu v hv)
    0 (by simp) s hcard hmem
    (fun z hz k hk ↦ by
      obtain rfl : k = 0 := by have := Multiset.nodup_iff_count_le_one.mp hs z; omega
      simp [hzero z hz])
    hx
  simpa only [zero_add, Function.iterate_one, eval_zero, sub_zero] using hrem

/-- For `x - x₀ = t h` with `t ∈ [0, 1]` and `ξ ∈ (x₀, x₀ + h)`, the nodal product at `x₀`, `ξ` and
`x₀ + h` is at most `t (1 - t) max(t, 1 - t) h³`. -/
private theorem abs_nodal_mul_le {x₀ h x ξ t : ℝ} (hh : 0 < h) (ht : t ∈ Icc (0 : ℝ) 1)
    (hxt : x - x₀ = t * h) (hξ : ξ ∈ Ioo x₀ (x₀ + h)) :
    |(x - x₀) * (x - ξ) * (x - (x₀ + h))| ≤ t * (1 - t) * max t (1 - t) * h ^ 3 := by
  have hξx : |x - ξ| ≤ max t (1 - t) * h := by
    rw [max_mul_of_nonneg _ _ hh.le, abs_le]
    constructor <;> linarith [le_max_left (t * h) ((1 - t) * h),
      le_max_right (t * h) ((1 - t) * h), hξ.1, hξ.2]
  have hth : t * h ≤ h := mul_le_of_le_one_left hh.le ht.2
  rw [abs_mul, abs_mul, hxt, abs_of_nonneg (mul_nonneg ht.1 hh.le),
    abs_of_nonpos (by linarith : x - (x₀ + h) ≤ 0)]
  calc t * h * |x - ξ| * -(x - (x₀ + h)) ≤ t * h * (max t (1 - t) * h) * ((1 - t) * h) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hξx (mul_nonneg ht.1 hh.le)) (by linarith)
          (by linarith) (mul_nonneg (mul_nonneg ht.1 hh.le)
            (mul_nonneg (le_max_of_le_left ht.1) hh.le))
    _ = t * (1 - t) * max t (1 - t) * h ^ 3 := by ring

/-- **Supp II (8.27).** If the fourth derivative of `f = Φ 0` is `L`-Lipschitz on `[x₀, x₀ + 2h]`,
the slope of the quartic interpolant satisfies `|f' - H₅'| ≤ L h⁴ / 96` on `[x₀, x₁]`. The slope
of `H₅` is `(∂ₜG₄ + (l₂ - G₄(2)) t (t - 1) (t - 1/2)) / h` (Supp II (8.28)). The proof applies
the remainder bound to `f' - H₅'`, whose zeros are `x₀`, `x₁` and one Rolle point in each of
`(x₀, x₁)` and `(x₁, x₂)`. -/
theorem abs_deriv_sub_hermiteQuartic_le_left {x₀ h L : ℝ} (hh : 0 < h) (Φ : ℕ → ℝ → ℝ)
    (hcontinuous : ∀ j < 5, ContinuousOn (Φ j) (Icc x₀ (x₀ + 2 * h)))
    (hderiv : ∀ j < 4, ∀ z ∈ Ioo x₀ (x₀ + 2 * h), HasDerivAt (Φ j) (Φ (j + 1) z) z)
    (hlip : ∀ x ∈ Icc x₀ (x₀ + 2 * h), ∀ y ∈ Icc x₀ (x₀ + 2 * h),
      |Φ 4 x - Φ 4 y| ≤ L * |x - y|)
    {x : ℝ} (hx : x ∈ Icc x₀ (x₀ + h)) :
    |Φ 1 x - (hermiteCubicSlope (Φ 0 x₀) (Φ 0 (x₀ + h)) (h * Φ 1 x₀) (h * Φ 1 (x₀ + h))
      ((x - x₀) / h) + (Φ 0 (x₀ + 2 * h) - hermiteCubic (Φ 0 x₀) (Φ 0 (x₀ + h)) (h * Φ 1 x₀)
        (h * Φ 1 (x₀ + h)) 2) * ((x - x₀) / h * ((x - x₀) / h - 1) * ((x - x₀) / h - 1 / 2))) /
      h| ≤ L * h ^ 4 / 96 := by
  set p := hermiteQuarticPoly x₀ h (Φ 0 x₀) (Φ 0 (x₀ + h)) (Φ 0 (x₀ + 2 * h)) (h * Φ 1 x₀)
    (h * Φ 1 (x₀ + h)) with hp
  obtain ⟨e₀, e₁, e₂, d₀, d₁⟩ := hermiteQuarticPoly_interpolates (x₀ := x₀) hh.ne' (Φ 0 x₀)
    (Φ 0 (x₀ + h)) (Φ 0 (x₀ + 2 * h)) (h * Φ 1 x₀) (h * Φ 1 (x₀ + h))
  rw [← hp] at e₀ e₁ e₂ d₀ d₁
  rw [mul_div_cancel_left₀ _ hh.ne'] at d₀ d₁
  -- Rolle points of `f - H₅` in `(x₀, x₁)` and `(x₁, x₂)`
  obtain ⟨ξ, hξ, hξ0⟩ := exists_deriv_sub_eval_eq_zero (Φ₀ := Φ 0) (Φ₁ := Φ 1) (p := p)
    (by linarith : x₀ < x₀ + h)
    ((hcontinuous 0 (by omega)).mono (Icc_subset_Icc le_rfl (by linarith)))
    (fun z hz ↦ hderiv 0 (by omega) z ⟨hz.1, by linarith [hz.2]⟩) e₀.symm e₁.symm
  obtain ⟨η, hη, hη0⟩ := exists_deriv_sub_eval_eq_zero (Φ₀ := Φ 0) (Φ₁ := Φ 1) (p := p)
    (by linarith : x₀ + h < x₀ + 2 * h)
    ((hcontinuous 0 (by omega)).mono (Icc_subset_Icc (by linarith) le_rfl))
    (fun z hz ↦ hderiv 0 (by omega) z ⟨by linarith [hz.1], hz.2⟩) e₁.symm e₂.symm
  -- the slope error vanishes at `x₀`, `ξ`, `x₁` and `η`
  set s : Multiset ℝ := x₀ ::ₘ ξ ::ₘ (x₀ + h) ::ₘ η ::ₘ 0 with hs
  have hnodup : s.Nodup := by
    simp only [hs, Multiset.nodup_cons, Multiset.mem_cons, Multiset.notMem_zero, or_false,
      not_or, Multiset.nodup_zero, and_true]
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, not_false⟩ <;> intro heq <;>
      linarith [hξ.1, hξ.2, hη.1, hη.2]
  have hrem := abs_deriv_sub_eval_le_of_lipschitz (n := 3) Φ hcontinuous hderiv hlip p
    (hermiteQuarticPoly_natDegree_le _ _ _ _ _ _ _) s hnodup (by simp [hs])
    (fun z hz ↦ by
      simp only [hs, Multiset.mem_cons, Multiset.notMem_zero, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> constructor <;>
        linarith [hξ.1, hξ.2, hη.1, hη.2])
    (fun z hz ↦ by
      simp only [hs, Multiset.mem_cons, Multiset.notMem_zero, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl
      exacts [d₀.symm, hξ0, d₁.symm, hη0])
    (x := x) ⟨hx.1, by linarith [hx.2]⟩
  rw [hp, eval_derivative_hermiteQuarticPoly] at hrem
  refine hrem.trans ?_
  -- the nodal product is at most `h⁴ / 4`
  set t := (x - x₀) / h
  have ht : t ∈ Icc (0 : ℝ) 1 :=
    unitInterval.div_mem (sub_nonneg.2 hx.1) hh.le (sub_le_iff_le_add'.2 hx.2)
  have hxt : x - x₀ = t * h := (div_mul_cancel₀ _ hh.ne').symm
  have hη' : |x - η| ≤ (2 - t) * h := by
    rw [abs_of_nonpos (by linarith [hη.1, hx.2])]
    linarith [hη.2]
  have hprod : |(s.map fun z ↦ x - z).prod| ≤ h ^ 4 / 4 := by
    rw [show (s.map fun z ↦ x - z).prod = (x - x₀) * (x - ξ) * (x - (x₀ + h)) * (x - η) by
      simp only [hs, Multiset.map_cons, Multiset.map_zero, Multiset.prod_cons, Multiset.prod_zero]
      ring, abs_mul]
    calc _ ≤ t * (1 - t) * max t (1 - t) * h ^ 3 * ((2 - t) * h) :=
          mul_le_mul (abs_nodal_mul_le hh ht hxt hξ) hη' (abs_nonneg _)
            (mul_nonneg (mul_nonneg (mul_nonneg ht.1 (sub_nonneg.2 ht.2))
              (le_max_of_le_left ht.1)) (by positivity))
      _ = t * (1 - t) * (2 - t) * max t (1 - t) * h ^ 4 := by ring
      _ ≤ 1 / 4 * h ^ 4 := by gcongr; exact quarticSlopeNodal_le ht
      _ = h ^ 4 / 4 := by ring
  have hL := lipschitz_const_nonneg (by linarith : x₀ < x₀ + 2 * h) hlip
  have h24 : ((3 + 1).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [h24]
  calc L / 24 * |(s.map fun z ↦ x - z).prod| ≤ L / 24 * (h ^ 4 / 4) := by gcongr
    _ = L * h ^ 4 / 96 := by ring


/-- `t (1 - t) max(t, 1 - t) ≤ 4/27` on `[0, 1]`, the nodal bound behind (8.36). -/
theorem cubicSlopeNodal_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t * (1 - t) * max t (1 - t) ≤ 4 / 27 := by
  rcases le_total t (1 - t) with hle | hle
  · rw [max_eq_right hle]
    have := mul_sub_one_sq_le ht
    nlinarith
  · rw [max_eq_left hle]
    have := mul_sub_one_sq_le (t := 1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    nlinarith

/-- **Supp II (8.36).** If the third derivative of `f = Φ 0` is `L`-Lipschitz on
`[x₀, x₁]`, the slope `∂ₜG₄ / h` of the cubic Hermite interpolant satisfies
`|f' - H₄'| ≤ 2 L h³ / 81` on `[x₀, x₁]`. -/
theorem abs_deriv_sub_hermiteCubic_le_left {x₀ h L : ℝ} (hh : 0 < h) (Φ : ℕ → ℝ → ℝ)
    (hcontinuous : ∀ j < 4, ContinuousOn (Φ j) (Icc x₀ (x₀ + h)))
    (hderiv : ∀ j < 3, ∀ z ∈ Ioo x₀ (x₀ + h), HasDerivAt (Φ j) (Φ (j + 1) z) z)
    (hlip : ∀ x ∈ Icc x₀ (x₀ + h), ∀ y ∈ Icc x₀ (x₀ + h), |Φ 3 x - Φ 3 y| ≤ L * |x - y|)
    {x : ℝ} (hx : x ∈ Icc x₀ (x₀ + h)) :
    |Φ 1 x - hermiteCubicSlope (Φ 0 x₀) (Φ 0 (x₀ + h)) (h * Φ 1 x₀) (h * Φ 1 (x₀ + h))
      ((x - x₀) / h) / h| ≤ 2 * L * h ^ 3 / 81 := by
  set p := hermiteCubicPoly x₀ h (Φ 0 x₀) (Φ 0 (x₀ + h)) (h * Φ 1 x₀) (h * Φ 1 (x₀ + h)) with hp
  obtain ⟨e₀, e₁, d₀, d₁⟩ := hermiteCubicPoly_interpolates (x₀ := x₀) hh.ne' (Φ 0 x₀)
    (Φ 0 (x₀ + h)) (h * Φ 1 x₀) (h * Φ 1 (x₀ + h))
  rw [← hp] at e₀ e₁ d₀ d₁
  rw [mul_div_cancel_left₀ _ hh.ne'] at d₀ d₁
  obtain ⟨ξ, hξ, hξ0⟩ := exists_deriv_sub_eval_eq_zero (Φ₀ := Φ 0) (Φ₁ := Φ 1) (p := p)
    (by linarith : x₀ < x₀ + h) (hcontinuous 0 (by omega)) (hderiv 0 (by omega)) e₀.symm e₁.symm
  set s : Multiset ℝ := x₀ ::ₘ ξ ::ₘ (x₀ + h) ::ₘ 0 with hs
  have hnodup : s.Nodup := by
    simp only [hs, Multiset.nodup_cons, Multiset.mem_cons, Multiset.notMem_zero, or_false,
      not_or, Multiset.nodup_zero, and_true]
    refine ⟨⟨?_, ?_⟩, ?_, not_false⟩ <;> intro heq <;> linarith [hξ.1, hξ.2]
  have hrem := abs_deriv_sub_eval_le_of_lipschitz (n := 2) Φ hcontinuous hderiv hlip p
    (hermiteCubicPoly_natDegree_le _ _ _ _ _ _) s hnodup (by simp [hs])
    (fun z hz ↦ by
      simp only [hs, Multiset.mem_cons, Multiset.notMem_zero, or_false] at hz
      rcases hz with rfl | rfl | rfl <;> constructor <;> linarith [hξ.1, hξ.2])
    (fun z hz ↦ by
      simp only [hs, Multiset.mem_cons, Multiset.notMem_zero, or_false] at hz
      rcases hz with rfl | rfl | rfl
      exacts [d₀.symm, hξ0, d₁.symm])
    hx
  rw [hp, eval_derivative_hermiteCubicPoly] at hrem
  refine hrem.trans ?_
  set t := (x - x₀) / h
  have ht : t ∈ Icc (0 : ℝ) 1 :=
    unitInterval.div_mem (sub_nonneg.2 hx.1) hh.le (sub_le_iff_le_add'.2 hx.2)
  have hprod : |(s.map fun z ↦ x - z).prod| ≤ 4 / 27 * h ^ 3 := by
    rw [show (s.map fun z ↦ x - z).prod = (x - x₀) * (x - ξ) * (x - (x₀ + h)) by
      simp only [hs, Multiset.map_cons, Multiset.map_zero, Multiset.prod_cons, Multiset.prod_zero]
      ring]
    refine (abs_nodal_mul_le hh ht (div_mul_cancel₀ _ hh.ne').symm hξ).trans ?_
    gcongr
    exact cubicSlopeNodal_le ht
  have hL := lipschitz_const_nonneg (by linarith : x₀ < x₀ + h) hlip
  have h6 : ((2 + 1).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h6]
  calc L / 6 * |(s.map fun z ↦ x - z).prod| ≤ L / 6 * (4 / 27 * h ^ 3) := by gcongr
    _ = 2 * L * h ^ 3 / 81 := by ring

/-! ### Bounds of a function and its slope from Hermite data -/

/-- **Supp II Sec 8.3, fourth order.** Values and scaled slopes at `x₀`, `x₁` bound `f` on
`[x₀, x₁]` by `hermiteCubicBound + L h⁴ / 384` for an `L`-Lipschitz third derivative. -/
theorem abs_le_of_hermiteCubic {x₀ h L : ℝ} (hh : 0 < h) (Φ : ℕ → ℝ → ℝ)
    (hcontinuous : ∀ j < 3, ContinuousOn (Φ j) (Icc x₀ (x₀ + h)))
    (hderiv : ∀ j < 3, ∀ z ∈ Ioo x₀ (x₀ + h), HasDerivAt (Φ j) (Φ (j + 1) z) z)
    (hlip : ∀ x ∈ Icc x₀ (x₀ + h), ∀ y ∈ Icc x₀ (x₀ + h), |Φ 3 x - Φ 3 y| ≤ L * |x - y|)
    {x : ℝ} (hx : x ∈ Icc x₀ (x₀ + h)) :
    |Φ 0 x| ≤ hermiteCubicBound (Φ 0 x₀) (Φ 0 (x₀ + h)) (h * Φ 1 x₀) (h * Φ 1 (x₀ + h)) +
      L * h ^ 4 / 384 := by
  have herr := abs_sub_hermiteCubic_le_left hh Φ hcontinuous hderiv hlip hx
  have ht := unitInterval.div_mem (sub_nonneg.2 hx.1) hh.le (sub_le_iff_le_add'.2 hx.2)
  have hG := abs_hermiteCubic_le (l₀ := Φ 0 x₀) (l₁ := Φ 0 (x₀ + h)) (m₀ := h * Φ 1 x₀)
    (m₁ := h * Φ 1 (x₀ + h)) ht
  have := abs_sub_abs_le_abs_sub (Φ 0 x) (hermiteCubic (Φ 0 x₀) (Φ 0 (x₀ + h)) (h * Φ 1 x₀)
    (h * Φ 1 (x₀ + h)) ((x - x₀) / h))
  linarith

/-- **Supp II Sec 8.3, fifth order.** With the extra value `l₂ = f(x₀ + 2h)`,
`|f| ≤ hermiteCubicBound + |l₂ - G₄(2)| / 64 + L h⁵ / 1200` on `[x₀, x₁]` for an `L`-Lipschitz
fourth derivative on `[x₀, x₀ + 2h]` ((8.21), (8.24), (8.26)). -/
theorem abs_le_of_hermiteQuartic {x₀ h L : ℝ} (hh : 0 < h) (Φ : ℕ → ℝ → ℝ)
    (hcontinuous : ∀ j < 4, ContinuousOn (Φ j) (Icc x₀ (x₀ + 2 * h)))
    (hderiv : ∀ j < 4, ∀ z ∈ Ioo x₀ (x₀ + 2 * h), HasDerivAt (Φ j) (Φ (j + 1) z) z)
    (hlip : ∀ x ∈ Icc x₀ (x₀ + 2 * h), ∀ y ∈ Icc x₀ (x₀ + 2 * h),
      |Φ 4 x - Φ 4 y| ≤ L * |x - y|)
    {x : ℝ} (hx : x ∈ Icc x₀ (x₀ + h)) :
    |Φ 0 x| ≤ hermiteCubicBound (Φ 0 x₀) (Φ 0 (x₀ + h)) (h * Φ 1 x₀) (h * Φ 1 (x₀ + h)) +
      |Φ 0 (x₀ + 2 * h) - hermiteCubic (Φ 0 x₀) (Φ 0 (x₀ + h)) (h * Φ 1 x₀)
        (h * Φ 1 (x₀ + h)) 2| / 64 + L * h ^ 5 / 1200 := by
  have herr := abs_sub_hermiteQuartic_le_left hh Φ hcontinuous hderiv hlip hx
  have ht := unitInterval.div_mem (sub_nonneg.2 hx.1) hh.le (sub_le_iff_le_add'.2 hx.2)
  have hH := abs_hermiteQuartic_le (l₀ := Φ 0 x₀) (l₁ := Φ 0 (x₀ + h)) (l₂ := Φ 0 (x₀ + 2 * h))
    (m₀ := h * Φ 1 x₀) (m₁ := h * Φ 1 (x₀ + h)) ht
  have hG := abs_hermiteCubic_le (l₀ := Φ 0 x₀) (l₁ := Φ 0 (x₀ + h)) (m₀ := h * Φ 1 x₀)
    (m₁ := h * Φ 1 (x₀ + h)) ht
  have := abs_sub_abs_le_abs_sub (Φ 0 x) (hermiteQuartic (Φ 0 x₀) (Φ 0 (x₀ + h))
    (Φ 0 (x₀ + 2 * h)) (h * Φ 1 x₀) (h * Φ 1 (x₀ + h)) ((x - x₀) / h))
  linarith

/-- **Supp II (8.33), (8.36).** The slope on `[x₀, x₁]` is at most `hermiteSlopeBound / h` plus
`2 L h³ / 81` for an `L`-Lipschitz third derivative. -/
theorem abs_deriv_le_of_hermiteCubic {x₀ h L : ℝ} (hh : 0 < h) (Φ : ℕ → ℝ → ℝ)
    (hcontinuous : ∀ j < 4, ContinuousOn (Φ j) (Icc x₀ (x₀ + h)))
    (hderiv : ∀ j < 3, ∀ z ∈ Ioo x₀ (x₀ + h), HasDerivAt (Φ j) (Φ (j + 1) z) z)
    (hlip : ∀ x ∈ Icc x₀ (x₀ + h), ∀ y ∈ Icc x₀ (x₀ + h), |Φ 3 x - Φ 3 y| ≤ L * |x - y|)
    {x : ℝ} (hx : x ∈ Icc x₀ (x₀ + h)) :
    |Φ 1 x| ≤ hermiteSlopeBound (Φ 0 x₀) (Φ 0 (x₀ + h)) (h * Φ 1 x₀) (h * Φ 1 (x₀ + h)) / h +
      2 * L * h ^ 3 / 81 := by
  have herr := abs_deriv_sub_hermiteCubic_le_left hh Φ hcontinuous hderiv hlip hx
  have ht := unitInterval.div_mem (sub_nonneg.2 hx.1) hh.le (sub_le_iff_le_add'.2 hx.2)
  have hS := abs_hermiteCubicSlope_le (l₀ := Φ 0 x₀) (l₁ := Φ 0 (x₀ + h)) (m₀ := h * Φ 1 x₀)
    (m₁ := h * Φ 1 (x₀ + h)) ht
  have hS' : |hermiteCubicSlope (Φ 0 x₀) (Φ 0 (x₀ + h)) (h * Φ 1 x₀) (h * Φ 1 (x₀ + h))
      ((x - x₀) / h) / h| ≤
      hermiteSlopeBound (Φ 0 x₀) (Φ 0 (x₀ + h)) (h * Φ 1 x₀) (h * Φ 1 (x₀ + h)) / h := by
    rw [abs_div, abs_of_pos hh]
    exact div_le_div_of_nonneg_right hS hh.le
  have := abs_sub_abs_le_abs_sub (Φ 1 x) (hermiteCubicSlope (Φ 0 x₀) (Φ 0 (x₀ + h))
    (h * Φ 1 x₀) (h * Φ 1 (x₀ + h)) ((x - x₀) / h) / h)
  linarith

/-- **Supp II (8.27)-(8.35).** The slope on `[x₀, x₁]` is at most
`(hermiteSlopeBound + |l₂ - G₄(2)| / (12 √3)) / h + L h⁴ / 96` for an `L`-Lipschitz fourth
derivative on `[x₀, x₀ + 2h]`. -/
theorem abs_deriv_le_of_hermiteQuartic {x₀ h L : ℝ} (hh : 0 < h) (Φ : ℕ → ℝ → ℝ)
    (hcontinuous : ∀ j < 5, ContinuousOn (Φ j) (Icc x₀ (x₀ + 2 * h)))
    (hderiv : ∀ j < 4, ∀ z ∈ Ioo x₀ (x₀ + 2 * h), HasDerivAt (Φ j) (Φ (j + 1) z) z)
    (hlip : ∀ x ∈ Icc x₀ (x₀ + 2 * h), ∀ y ∈ Icc x₀ (x₀ + 2 * h),
      |Φ 4 x - Φ 4 y| ≤ L * |x - y|)
    {x : ℝ} (hx : x ∈ Icc x₀ (x₀ + h)) :
    |Φ 1 x| ≤ (hermiteSlopeBound (Φ 0 x₀) (Φ 0 (x₀ + h)) (h * Φ 1 x₀) (h * Φ 1 (x₀ + h)) +
      |Φ 0 (x₀ + 2 * h) - hermiteCubic (Φ 0 x₀) (Φ 0 (x₀ + h)) (h * Φ 1 x₀)
        (h * Φ 1 (x₀ + h)) 2| / (12 * Real.sqrt 3)) / h + L * h ^ 4 / 96 := by
  have herr := abs_deriv_sub_hermiteQuartic_le_left hh Φ hcontinuous hderiv hlip hx
  have ht := unitInterval.div_mem (sub_nonneg.2 hx.1) hh.le (sub_le_iff_le_add'.2 hx.2)
  have hS := abs_hermiteCubicSlope_le (l₀ := Φ 0 x₀) (l₁ := Φ 0 (x₀ + h)) (m₀ := h * Φ 1 x₀)
    (m₁ := h * Φ 1 (x₀ + h)) ht
  have hW := abs_quarticWeightSlope_le ht
  set c := Φ 0 (x₀ + 2 * h) - hermiteCubic (Φ 0 x₀) (Φ 0 (x₀ + h)) (h * Φ 1 x₀) (h * Φ 1 (x₀ + h)) 2
  set t := (x - x₀) / h
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hnum : |hermiteCubicSlope (Φ 0 x₀) (Φ 0 (x₀ + h)) (h * Φ 1 x₀) (h * Φ 1 (x₀ + h)) t +
      c * (t * (t - 1) * (t - 1 / 2))| ≤
      hermiteSlopeBound (Φ 0 x₀) (Φ 0 (x₀ + h)) (h * Φ 1 x₀) (h * Φ 1 (x₀ + h)) +
        |c| / (12 * Real.sqrt 3) := by
    refine (abs_add_le _ _).trans (add_le_add hS ?_)
    rw [abs_mul]
    calc |c| * |t * (t - 1) * (t - 1 / 2)| ≤ |c| * (1 / (12 * Real.sqrt 3)) := by gcongr
      _ = |c| / (12 * Real.sqrt 3) := by ring
  have hS' := div_le_div_of_nonneg_right hnum hh.le
  rw [← abs_of_pos hh, ← abs_div, abs_of_pos hh] at hS'
  have := abs_sub_abs_le_abs_sub (Φ 1 x) ((hermiteCubicSlope (Φ 0 x₀) (Φ 0 (x₀ + h))
    (h * Φ 1 x₀) (h * Φ 1 (x₀ + h)) t + c * (t * (t - 1) * (t - 1 / 2))) / h)
  linarith

end PDE.Analysis.Approximation
