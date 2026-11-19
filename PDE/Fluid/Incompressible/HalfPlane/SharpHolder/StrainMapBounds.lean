/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.StrainMap

/-!
# Certified bounds of the transport map and the threshold of the strain estimate

The map `T(s₁, s₂)` of Chen and Hou, Part I, (B.63)-(B.65) is the unique positive root of the cubic
`strainCubic s₁ s₂`. A rational `t` is certified below the root by `strainCubic s₁ s₂ t ≤ 0`
(`le_strainMap_of_strainCubic_nonpos`) and above it by `strainCubic s₁ s₂ t > 0`, `t ≥ 0`
(`strainMap_lt_of_strainCubic_pos`); on the axis side, `strainCubic s₁ 0 t ≤ 0` with
`t ≤ 1/(4 s₁)` gives `t ≤ T(s₁, s₂)` for every `s₂` (`le_strainMap_of_axis`), and in
particular `1 - s₁ ≤ T(s₁, s₂)` (`one_sub_le_strainMap`), that is `s₁ - T ≤ 2 (s₁ - 1/2)`.

The divided differences of `T` in each variable are rational in the two values of `T`
(`strainMap_sub_mul_eq`, `strainMap_sub_mul_eq_right`), from the symmetric form
`16 s₁ strainCubic`. On a cell `[x₀, x₁] × [z₀, z₁]` with `T ∈ [T₀, T₁]` they give the affine
majorant `s₁ - T(s₁, s₂) ≤ (x₁ - T₀) - (1 + λ₁)(x₁ - s₁) - λ₂ (s₂ - z₀)`
(`sub_strainMap_le_affine`).

Rational bounds of the threshold `f` are certified by the sign of the quartic `Δ₁`
(`le_strainThreshold_of_quartic`, `strainThreshold_le_of_quartic`), at candidates from integer
square roots (`thresholdGuess`).

## Main definitions

* `strainQuarticRat`: the quartic `Δ₁` over the rationals.
* `thresholdGuess`: a rational approximation of `f` from below or above, from integer square
  roots.
* `thresholdLow`: the certified lower bound `f⁻ = max(1/2, guess)`.
* `strainDenomBound`: an upper bound of the denominators of both divided differences on a cell.

## Main results

* `le_strainMap_of_strainCubic_nonpos`, `strainMap_lt_of_strainCubic_pos`: the sign of the cubic
  at a rational point places it below or above the root.
* `le_strainMap_of_axis`: if `t ≤ 1/(4 s₁)` and the cubic on the axis is nonpositive at `t`, then
  `t ≤ T(s₁, s₂)` for every `s₂`.
* `one_sub_le_strainMap`: `1 - s₁ ≤ T(s₁, s₂)`.
* `strainMap_sub_mul_eq`, `strainMap_sub_mul_eq_right`: the divided differences of `T` in `s₁`
  and in `s₂`.
* `strainMap_mem_cell`: on a cell with `x₀ ≥ 1/2`, `z₀ > 0`, `T` lies between `T(x₁, z₀)` and
  `T(x₀, z₁)`.
* `sub_strainMap_le_affine`: the affine majorant of `s₁ - T` on a cell.
* `le_strainThreshold_of_quartic`, `strainThreshold_le_of_quartic`: a rational `q ≥ 0` is below
  the threshold if `q ≤ 1/2` or `Δ₁(q, s₂) > 0`, and above it if `Δ₁(q, s₂) < 0`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 3.3, (3.10), p. 31, and
  Appendix B.3.2, (B.63)-(B.65), pp. 141-142.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open Set

namespace IncompressibleFlow.SharpHolder

/-! ### Certified bounds of the root -/

/-- A point where the cubic is nonpositive lies below the root. -/
theorem le_strainMap_of_strainCubic_nonpos {s₁ s₂ t : ℝ} (h₁ : 0 < s₁) (h₂ : s₂ ≠ 0)
    (h : strainCubic s₁ s₂ t ≤ 0) : t ≤ strainMap s₁ s₂ := by
  by_contra hlt
  push Not at hlt
  exact absurd h (not_le.2 (strainCubic_pos_of_lt h₁ h₂ hlt))

/-- The cubic grows in `s₂²` only by `s₂² (2t - 1/(2 s₁)) - s₂⁴ / s₁`. -/
theorem strainCubic_eq_axis (s₁ s₂ t : ℝ) (h₁ : s₁ ≠ 0) :
    strainCubic s₁ s₂ t = strainCubic s₁ 0 t + s₂ ^ 2 * (2 * t - 1 / (2 * s₁)) - s₂ ^ 4 / s₁ := by
  simp only [strainCubic]
  field_simp
  ring

/-- A lower bound of `T(s₁, σ)` for every `σ ≠ 0` holds at `σ = 0` too, by continuity of `T` in
its second variable. -/
theorem le_strainMap_of_forall_ne_zero {s₁ t : ℝ} (h₁ : 0 < s₁)
    (h : ∀ σ : ℝ, σ ≠ 0 → t ≤ strainMap s₁ σ) (s₂ : ℝ) : t ≤ strainMap s₁ s₂ := by
  rcases eq_or_ne s₂ 0 with rfl | h₂
  · exact ge_of_tendsto ((continuousAt_strainMap_right h₁ 0).tendsto.mono_left
      (nhdsWithin_le_nhds (s := {0}ᶜ))) (eventually_nhdsWithin_of_forall fun σ hσ ↦ h σ hσ)
  · exact h s₂ h₂

/-- **The axis certificate.** If `t ≤ 1/(4 s₁)` and the cubic on the axis is nonpositive at `t`,
then `t ≤ T(s₁, s₂)` for every `s₂`. -/
theorem le_strainMap_of_axis {s₁ s₂ t : ℝ} (h₁ : 0 < s₁) (ht : t ≤ 1 / (4 * s₁))
    (h : strainCubic s₁ 0 t ≤ 0) : t ≤ strainMap s₁ s₂ := by
  refine le_strainMap_of_forall_ne_zero h₁ (fun s₂ h₂ ↦ ?_) s₂
  refine le_strainMap_of_strainCubic_nonpos h₁ h₂ ?_
  rw [strainCubic_eq_axis s₁ s₂ t h₁.ne']
  have h4 : 0 ≤ s₂ ^ 4 / s₁ := by positivity
  have hle : 2 * t - 1 / (2 * s₁) ≤ 0 := by
    have : 2 * t ≤ 2 * (1 / (4 * s₁)) := by linarith
    have e : 2 * (1 / (4 * s₁)) = 1 / (2 * s₁) := by field_simp; ring
    linarith
  nlinarith [sq_nonneg s₂]

/-- `1 - s₁ ≤ T(s₁, s₂)`: on the axis the cubic at `1 - s₁` is `-(s₁ - 1/2)⁴ / s₁`. -/
theorem one_sub_le_strainMap {s₁ s₂ : ℝ} (h₁ : 0 < s₁) :
    1 - s₁ ≤ strainMap s₁ s₂ := by
  refine le_strainMap_of_axis h₁ ?_ ?_
  · rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2 * s₁ - 1)]
  · have e : strainCubic s₁ 0 (1 - s₁) = -(s₁ - 1 / 2) ^ 4 / s₁ := by
      simp only [strainCubic]
      field_simp
      ring
    rw [e]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg ((s₁ - 1 / 2) ^ 2)]) h₁.le

/-- Below the root the cubic is negative on `[0, T)`. -/
theorem strainCubic_neg_of_lt {s₁ s₂ t : ℝ} (h₁ : 0 < s₁) (h₂ : s₂ ≠ 0) (ht : 0 ≤ t)
    (hlt : t < strainMap s₁ s₂) : strainCubic s₁ s₂ t < 0 := by
  have h0 : strainCubic s₁ s₂ 0 < 0 := by
    simp only [strainCubic]
    have : 0 < (4 * s₂ ^ 2 + 1) ^ 2 / (16 * s₁) := by positivity
    linarith [show (0 : ℝ) ^ 3 + 0 ^ 2 * s₁ + 0 * (s₁ ^ 2 - 1 / 2 + 2 * s₂ ^ 2) = 0 by ring]
  by_contra hge
  push Not at hge
  rcases eq_or_lt_of_le hge with heq | hpos
  · exact absurd (eq_strainMap_of_strainCubic_eq_zero h₁ h₂ heq.symm) hlt.ne
  · have hcont : ContinuousOn (strainCubic s₁ s₂) (Icc 0 t) := by
      unfold strainCubic
      fun_prop
    obtain ⟨u, hu, hroot⟩ := intermediate_value_Icc ht hcont ⟨h0.le, hpos.le⟩
    have := eq_strainMap_of_strainCubic_eq_zero h₁ h₂ hroot
    linarith [hu.2]

/-- A nonnegative point where the cubic is positive lies above the root. -/
theorem strainMap_lt_of_strainCubic_pos {s₁ s₂ t : ℝ} (h₁ : 0 < s₁) (h₂ : s₂ ≠ 0) (ht : 0 ≤ t)
    (h : 0 < strainCubic s₁ s₂ t) : strainMap s₁ s₂ < t := by
  by_contra hle
  push Not at hle
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [heq, strainCubic_strainMap h₁ h₂] at h
    exact lt_irrefl _ h
  · exact absurd h (not_lt.2 (strainCubic_neg_of_lt h₁ h₂ ht hlt).le)

/-! ### Certified bounds of the threshold -/

/-- The quartic `Δ₁` over the rationals. -/
def strainQuarticRat (s₁ s₂ : ℚ) : ℚ :=
  s₂ ^ 4 - 2 * s₁ ^ 2 * s₂ ^ 2 - 3 * s₁ ^ 4 + s₁ ^ 2 / 2 + s₂ ^ 2 / 2 + 1 / 16

/-- `strainQuarticRat s₁ s₂` is the quartic `Δ₁(s₁, s₂)` over the reals. -/
theorem cast_strainQuarticRat (s₁ s₂ : ℚ) :
    ((strainQuarticRat s₁ s₂ : ℚ) : ℝ) = strainQuartic s₁ s₂ := by
  simp only [strainQuarticRat, strainQuartic]
  push_cast
  ring

/-- A lower bound of `√q` on the grid `2^-t`. -/
def sqrtBelow (t : ℕ) (q : ℚ) : ℚ := (Nat.sqrt (⌊q * 4 ^ t⌋).toNat : ℚ) / 2 ^ t

/-- An approximation of `f(p)` from below (`up = false`) or above (`up = true`), on the grid
`2^-40`, displaced by `2^-38`; only the sign checks of `Δ₁` give it a meaning. -/
def thresholdGuess (up : Bool) (p : ℚ) : ℚ :=
  let e : ℚ := if up then 1 / 2 ^ 40 else 0
  let s := sqrtBelow 40 (16 * p ^ 4 + 4 * p ^ 2 + 1) + e
  let f := sqrtBelow 40 ((1 / 2 - 2 * p ^ 2 + s) / 6) + e
  if up then f + 1 / 2 ^ 38 else f - 1 / 2 ^ 38

/-- The certified lower bound `f⁻ = max(1/2, guess)` at `l`. -/
def thresholdLow (l : ℚ) : ℚ := max (1 / 2) (thresholdGuess false l)

/-- A rational `q` is below the threshold if `q ≤ 1/2` or `Δ₁(q, s₂) > 0` with `q ≥ 0`. -/
theorem le_strainThreshold_of_quartic {q : ℚ} {s₂ : ℝ}
    (h : q ≤ 1 / 2 ∨ (0 ≤ q ∧ 0 < strainQuartic q s₂)) : (q : ℝ) ≤ strainThreshold s₂ := by
  rcases h with h | ⟨h0, h⟩
  · have h' : (q : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.2 h
    have h'' : (q : ℝ) ≤ 1 / 2 := by simpa using h'
    exact h''.trans (one_half_le_strainThreshold _)
  · exact ((strainQuartic_pos_iff (by exact_mod_cast h0) _).1 h).le

/-- A rational `q ≥ 0` with `Δ₁(q, s₂) < 0` is above the threshold. -/
theorem strainThreshold_le_of_quartic {q : ℚ} {s₂ : ℝ} (h0 : 0 ≤ q)
    (h : strainQuartic q s₂ < 0) : strainThreshold s₂ ≤ (q : ℝ) :=
  ((strainQuartic_neg_iff (by exact_mod_cast h0) _).1 h).le

/-! ### Divided differences -/

/-- The root equation in polynomial form: `16 s₁ strainCubic s₁ s₂ T = 0`. -/
theorem strainMap_poly {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : s₂ ≠ 0) :
    16 * s₁ * strainMap s₁ s₂ ^ 3 + 16 * s₁ ^ 2 * strainMap s₁ s₂ ^ 2 +
      16 * s₁ * strainMap s₁ s₂ * (s₁ ^ 2 - 1 / 2 + 2 * s₂ ^ 2) - (4 * s₂ ^ 2 + 1) ^ 2 = 0 := by
  have h := strainCubic_strainMap h₁ h₂
  simp only [strainCubic] at h
  field_simp at h
  linarith

/-- **The divided difference in `s₁`.** With `a = T(x, z)`, `b = T(y, z)`:
`(a - b) · 16 y (a² + a b + b² + y (a + b) + y² + 2 z² - 1/2) =
  (y - x) · 16 a (a² + a (x + y) + x² + x y + y² + 2 z² - 1/2)`. -/
theorem strainMap_sub_mul_eq {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : z ≠ 0) :
    (strainMap x z - strainMap y z) * (16 * y * (strainMap x z ^ 2 + strainMap x z *
      strainMap y z + strainMap y z ^ 2 + y * (strainMap x z + strainMap y z) + y ^ 2 +
      2 * z ^ 2 - 1 / 2)) =
    (y - x) * (16 * strainMap x z * (strainMap x z ^ 2 + strainMap x z * (x + y) + x ^ 2 +
      x * y + y ^ 2 + 2 * z ^ 2 - 1 / 2)) := by
  have ha := strainMap_poly hx hz
  have hb := strainMap_poly hy hz
  linear_combination ha - hb

/-- **The divided difference in `s₂`.** With `a = T(x, z)`, `b = T(x, v)`:
`(b - a) · 16 x (a² + a b + b² + x (a + b) + x² + 2 v² - 1/2) =
  (v² - z²) (16 (v² + z²) + 8 - 32 x a)`. -/
theorem strainMap_sub_mul_eq_right {x z v : ℝ} (hx : 0 < x) (hz : z ≠ 0) (hv : v ≠ 0) :
    (strainMap x v - strainMap x z) * (16 * x * (strainMap x z ^ 2 + strainMap x z *
      strainMap x v + strainMap x v ^ 2 + x * (strainMap x z + strainMap x v) + x ^ 2 +
      2 * v ^ 2 - 1 / 2)) =
    (v ^ 2 - z ^ 2) * (16 * (v ^ 2 + z ^ 2) + 8 - 32 * x * strainMap x z) := by
  have ha := strainMap_poly hx hz
  have hb := strainMap_poly hx hv
  linear_combination hb - ha

/-! ### The affine majorant on a cell -/

/-- The upper bound `16 x₁ (3 T₁² + 2 x₁ T₁ + x₁² + 2 z₁² - 1/2)` of the denominators of both
divided differences on a cell. -/
def strainDenomBound (x₁ z₁ T₁ : ℝ) : ℝ :=
  16 * x₁ * (3 * T₁ ^ 2 + 2 * x₁ * T₁ + x₁ ^ 2 + 2 * z₁ ^ 2 - 1 / 2)

/-- On a cell `[x₀, x₁] × [z₀, z₁]` with `x₀ ≥ 1/2`, `z₀ > 0`, the map takes values between
`T(x₁, z₀)` and `T(x₀, z₁)`. -/
theorem strainMap_mem_cell {x₀ x₁ z₀ z₁ s₁ s₂ : ℝ} (hx₀ : 0 < x₀) (hz₀ : 0 < z₀)
    (hs₁ : s₁ ∈ Icc x₀ x₁) (hs₂ : s₂ ∈ Icc z₀ z₁) :
    strainMap x₁ z₀ ≤ strainMap s₁ s₂ ∧ strainMap s₁ s₂ ≤ strainMap x₀ z₁ := by
  have hs₁0 : 0 < s₁ := hx₀.trans_le hs₁.1
  have hs₂0 : 0 < s₂ := hz₀.trans_le hs₂.1
  have hx₁0 : 0 < x₁ := hs₁0.trans_le hs₁.2
  constructor
  · calc strainMap x₁ z₀ ≤ strainMap s₁ z₀ :=
          (strictAntiOn_strainMap hz₀).antitoneOn hs₁0 hx₁0 hs₁.2
      _ ≤ strainMap s₁ s₂ := monotoneOn_strainMap_right hs₁0 hz₀ hs₂0 hs₂.1
  · calc strainMap s₁ s₂ ≤ strainMap s₁ z₁ :=
          monotoneOn_strainMap_right hs₁0 hs₂0 (hs₂0.trans_le hs₂.2) hs₂.2
      _ ≤ strainMap x₀ z₁ := (strictAntiOn_strainMap (hs₂0.trans_le hs₂.2)).antitoneOn hx₀ hs₁0
          hs₁.1

/-- **The affine majorant of `s₁ - T` on a cell.** If `T₀ ≤ T(x₁, z₀)`, `T(x₀, z₁) ≤ T₁`,
`T₀ ≥ 0`, and `λ₁, λ₂ ≥ 0` satisfy `λ₁ D ≤ 16 T₀ (T₀² + 2 T₀ x₀ + 3 x₀² + 2 z₀² - 1/2)` and
`λ₂ D ≤ 2 z₀ max(0, 32 z₀² + 8 - 32 x₁ T₁)` with `D = strainDenomBound x₁ z₁ T₁`, then on the cell
`s₁ - T(s₁, s₂) ≤ (x₁ - T₀) - (1 + λ₁)(x₁ - s₁) - λ₂ (s₂ - z₀)`. -/
theorem sub_strainMap_le_affine {x₀ x₁ z₀ z₁ T₀ T₁ l₁ l₂ s₁ s₂ : ℝ} (hx₀ : 1 / 2 ≤ x₀)
    (hz₀ : 0 < z₀) (hs₁ : s₁ ∈ Icc x₀ x₁) (hs₂ : s₂ ∈ Icc z₀ z₁)
    (hT₀ : T₀ ≤ strainMap x₁ z₀) (hT₁ : strainMap x₀ z₁ ≤ T₁) (hT₀0 : 0 ≤ T₀)
    (hl₁ : l₁ * strainDenomBound x₁ z₁ T₁ ≤
      16 * T₀ * (T₀ ^ 2 + 2 * T₀ * x₀ + 3 * x₀ ^ 2 + 2 * z₀ ^ 2 - 1 / 2)) (hl₁0 : 0 ≤ l₁)
    (hl₂ : l₂ * strainDenomBound x₁ z₁ T₁ ≤ 2 * z₀ * max 0 (32 * z₀ ^ 2 + 8 - 32 * x₁ * T₁))
    (hl₂0 : 0 ≤ l₂) :
    s₁ - strainMap s₁ s₂ ≤ (x₁ - T₀) - (1 + l₁) * (x₁ - s₁) - l₂ * (s₂ - z₀) := by
  have hx₀0 : 0 < x₀ := lt_of_lt_of_le (by norm_num) hx₀
  have hs₁0 : 0 < s₁ := hx₀0.trans_le hs₁.1
  have hs₂0 : 0 < s₂ := hz₀.trans_le hs₂.1
  have hx₁0 : 0 < x₁ := hs₁0.trans_le hs₁.2
  have hx₁ : x₁ ∈ Icc x₀ x₁ := ⟨hs₁.1.trans hs₁.2, le_rfl⟩
  have hz₀' : z₀ ∈ Icc z₀ z₁ := ⟨le_rfl, hs₂.1.trans hs₂.2⟩
  -- facts about the values of the map, then the values become variables
  obtain ⟨ha₁, ha₂⟩ := strainMap_mem_cell hx₀0 hz₀ hs₁ hs₂
  obtain ⟨hb₁, hb₂⟩ := strainMap_mem_cell hx₀0 hz₀ hx₁ hs₂
  obtain ⟨hc₁, hc₂⟩ := strainMap_mem_cell hx₀0 hz₀ hx₁ hz₀'
  have e₁ := strainMap_sub_mul_eq hs₁0 hx₁0 hs₂0.ne'
  have e₂ := strainMap_sub_mul_eq_right hx₁0 hz₀.ne' hs₂0.ne'
  have h34b := three_fourths_le_strainMap hx₁0 hs₂0.ne'
  have h34d := three_fourths_le_strainMap hx₀0 (hz₀.trans_le (hs₂.1.trans hs₂.2)).ne'
  have hmul := strainMap_mul_le hx₁0 hz₀.ne'
  generalize strainMap s₁ s₂ = a at *
  generalize strainMap x₁ s₂ = b at *
  generalize strainMap x₁ z₀ = c at *
  generalize strainMap x₀ z₁ = d at *
  have hT₁0 : 0 ≤ T₁ := hT₀0.trans (hT₀.trans (hc₁.trans (hc₂.trans hT₁)))
  have hz₁ : z₀ ≤ z₁ := hs₂.1.trans hs₂.2
  have ha0 : 0 ≤ a := hT₀0.trans (hT₀.trans ha₁)
  have hb0 : 0 ≤ b := hT₀0.trans (hT₀.trans hb₁)
  have hc0 : 0 ≤ c := hT₀0.trans hT₀
  have haT : a ≤ T₁ := ha₂.trans hT₁
  have hbT : b ≤ T₁ := hb₂.trans hT₁
  have hcT : c ≤ T₁ := hc₂.trans hT₁
  have hs₂z : s₂ ^ 2 ≤ z₁ ^ 2 := pow_le_pow_left₀ hs₂0.le hs₂.2 2
  -- the bracket `T₁² + ...` dominates a bracket at `(x₀, z₁)`, which is at least `3/4`
  have hbr₁ : 1 / 4 ≤ 3 * T₁ ^ 2 + 2 * x₁ * T₁ + x₁ ^ 2 + 2 * z₁ ^ 2 - 1 / 2 := by
    have h34 := h34d
    have hd0 : 0 ≤ d := hc0.trans hc₂
    have hx01 : x₀ ≤ x₁ := hs₁.1.trans hs₁.2
    have hdT : d ≤ T₁ := hT₁
    have e1 := pow_le_pow_left₀ hd0 hdT 2
    have e2 := mul_le_mul hdT hx01 hx₀0.le hT₁0
    have e3 : x₀ ^ 2 ≤ x₁ ^ 2 := pow_le_pow_left₀ hx₀0.le hx01 2
    linarith only [h34, e1, e2, e3, sq_nonneg T₁, mul_nonneg hT₁0 hx₁0.le]
  have hD : 0 < strainDenomBound x₁ z₁ T₁ := by
    unfold strainDenomBound
    exact mul_pos (mul_pos (by norm_num) hx₁0) (lt_of_lt_of_le (by norm_num) hbr₁)
  have hDbr : ∀ u v w : ℝ, 0 ≤ u → u ≤ T₁ → 0 ≤ v → v ≤ T₁ → w ^ 2 ≤ z₁ ^ 2 →
      16 * x₁ * (u ^ 2 + u * v + v ^ 2 + x₁ * (u + v) + x₁ ^ 2 + 2 * w ^ 2 - 1 / 2) ≤
        strainDenomBound x₁ z₁ T₁ := by
    intro u v w hu hu' hv hv' hw
    unfold strainDenomBound
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have e1 : u ^ 2 ≤ T₁ ^ 2 := pow_le_pow_left₀ hu hu' 2
    have e2 : u * v ≤ T₁ * T₁ := mul_le_mul hu' hv' hv hT₁0
    have e3 : v ^ 2 ≤ T₁ ^ 2 := pow_le_pow_left₀ hv hv' 2
    have e4 : x₁ * (u + v) ≤ x₁ * (T₁ + T₁) := mul_le_mul_of_nonneg_left (by linarith) hx₁0.le
    linarith only [e1, e2, e3, e4, hw]
  -- step 1: the divided difference in `s₁` at height `s₂`
  have step₁ : l₁ * (x₁ - s₁) ≤ a - b := by
    have e := e₁
    set B := 16 * x₁ * (a ^ 2 + a * b + b ^ 2 + x₁ * (a + b) + x₁ ^ 2 + 2 * s₂ ^ 2 - 1 / 2)
    set A := 16 * a * (a ^ 2 + a * (s₁ + x₁) + s₁ ^ 2 + s₁ * x₁ + x₁ ^ 2 + 2 * s₂ ^ 2 - 1 / 2)
    have h34 := h34b
    have hB : 0 < B := by
      have : 0 < a ^ 2 + a * b + b ^ 2 + x₁ * (a + b) + x₁ ^ 2 + 2 * s₂ ^ 2 - 1 / 2 := by
        linarith only [h34, sq_nonneg a, mul_nonneg ha0 hb0, mul_nonneg hx₁0.le ha0]
      exact mul_pos (mul_pos (by norm_num) hx₁0) this
    have hBle : B ≤ strainDenomBound x₁ z₁ T₁ := hDbr a b s₂ ha0 haT hb0 hbT hs₂z
    have hlo0 : 0 ≤ T₀ ^ 2 + 2 * T₀ * x₀ + 3 * x₀ ^ 2 + 2 * z₀ ^ 2 - 1 / 2 := by
      have hx2 : 1 / 4 ≤ x₀ ^ 2 := by linarith only [mul_le_mul hx₀ hx₀ (by norm_num) hx₀0.le]
      linarith only [hx2, mul_nonneg hT₀0 hx₀0.le, sq_nonneg T₀, sq_nonneg z₀]
    have hbr : T₀ ^ 2 + 2 * T₀ * x₀ + 3 * x₀ ^ 2 + 2 * z₀ ^ 2 - 1 / 2 ≤
        a ^ 2 + a * (s₁ + x₁) + s₁ ^ 2 + s₁ * x₁ + x₁ ^ 2 + 2 * s₂ ^ 2 - 1 / 2 := by
      have hTa : T₀ ≤ a := hT₀.trans ha₁
      have hx01 : x₀ ≤ x₁ := hs₁.1.trans hs₁.2
      have e1 : T₀ ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hT₀0 hTa 2
      have e2 : T₀ * x₀ ≤ a * s₁ := mul_le_mul hTa hs₁.1 hx₀0.le ha0
      have e2' : T₀ * x₀ ≤ a * x₁ := mul_le_mul hTa hx01 hx₀0.le ha0
      have e3 : x₀ ^ 2 ≤ s₁ ^ 2 := pow_le_pow_left₀ hx₀0.le hs₁.1 2
      have e4 := mul_le_mul hs₁.1 hx01 hx₀0.le hs₁0.le
      have e5 : x₀ ^ 2 ≤ x₁ ^ 2 := pow_le_pow_left₀ hx₀0.le hx01 2
      have e6 : z₀ ^ 2 ≤ s₂ ^ 2 := pow_le_pow_left₀ hz₀.le hs₂.1 2
      linarith only [e1, e2, e2', e3, e4, e5, e6]
    have hAge : 16 * T₀ * (T₀ ^ 2 + 2 * T₀ * x₀ + 3 * x₀ ^ 2 + 2 * z₀ ^ 2 - 1 / 2) ≤ A := by
      have hTa : T₀ ≤ a := hT₀.trans ha₁
      simp only [A]
      exact mul_le_mul (by linarith) hbr hlo0 (by positivity)
    have hxs : 0 ≤ x₁ - s₁ := by linarith only [hs₁.2]
    have key : l₁ * (x₁ - s₁) * B ≤ (a - b) * B := by
      rw [e]
      calc l₁ * (x₁ - s₁) * B ≤ l₁ * (x₁ - s₁) * strainDenomBound x₁ z₁ T₁ :=
            mul_le_mul_of_nonneg_left hBle (mul_nonneg hl₁0 hxs)
        _ = (x₁ - s₁) * (l₁ * strainDenomBound x₁ z₁ T₁) := by ring
        _ ≤ (x₁ - s₁) * A := mul_le_mul_of_nonneg_left (hl₁.trans hAge) hxs
    exact le_of_mul_le_mul_right key hB
  -- step 2: the divided difference in `s₂` at `x₁`
  have step₂ : l₂ * (s₂ - z₀) ≤ b - c := by
    have e := e₂
    set D := 16 * x₁ * (c ^ 2 + c * b + b ^ 2 + x₁ * (c + b) + x₁ ^ 2 + 2 * s₂ ^ 2 - 1 / 2)
    have h34 := h34b
    have hDp : 0 < D := by
      have : 0 < c ^ 2 + c * b + b ^ 2 + x₁ * (c + b) + x₁ ^ 2 + 2 * s₂ ^ 2 - 1 / 2 := by
        linarith only [h34, sq_nonneg c, mul_nonneg hc0 hb0, mul_nonneg hx₁0.le hc0]
      exact mul_pos (mul_pos (by norm_num) hx₁0) this
    have hDle : D ≤ strainDenomBound x₁ z₁ T₁ := hDbr c b s₂ hc0 hcT hb0 hbT hs₂z
    have e6 : z₀ ^ 2 ≤ s₂ ^ 2 := pow_le_pow_left₀ hz₀.le hs₂.1 2
    have hbr0 : 0 ≤ 16 * (s₂ ^ 2 + z₀ ^ 2) + 8 - 32 * x₁ * c := by
      linarith only [hmul, e6]
    have hbr : 32 * z₀ ^ 2 + 8 - 32 * x₁ * T₁ ≤ 16 * (s₂ ^ 2 + z₀ ^ 2) + 8 - 32 * x₁ * c := by
      have : x₁ * c ≤ x₁ * T₁ := mul_le_mul_of_nonneg_left hcT hx₁0.le
      linarith only [this, e6]
    have hsz : 0 ≤ s₂ - z₀ := by linarith only [hs₂.1]
    have key : l₂ * (s₂ - z₀) * D ≤ (b - c) * D := by
      rw [show (b - c) * D = (s₂ ^ 2 - z₀ ^ 2) * (16 * (s₂ ^ 2 + z₀ ^ 2) + 8 - 32 * x₁ * c) from
        by rw [← e]]
      have h₁ : l₂ * (s₂ - z₀) * D ≤
          (s₂ - z₀) * (2 * z₀ * max 0 (32 * z₀ ^ 2 + 8 - 32 * x₁ * T₁)) := by
        calc l₂ * (s₂ - z₀) * D ≤ l₂ * (s₂ - z₀) * strainDenomBound x₁ z₁ T₁ :=
              mul_le_mul_of_nonneg_left hDle (mul_nonneg hl₂0 hsz)
          _ = (s₂ - z₀) * (l₂ * strainDenomBound x₁ z₁ T₁) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hl₂ hsz
      have h₂ : (s₂ - z₀) * (2 * z₀ * max 0 (32 * z₀ ^ 2 + 8 - 32 * x₁ * T₁)) ≤
          (s₂ - z₀) * (2 * z₀ * (16 * (s₂ ^ 2 + z₀ ^ 2) + 8 - 32 * x₁ * c)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (max_le hbr0 hbr)
          (by linarith only [hz₀])) hsz
      -- the difference of the two sides is `(s₂ - z₀)² (16 (s₂² + z₀²) + 8 - 32 x₁ c) ≥ 0`
      have h₃ : (s₂ - z₀) * (2 * z₀ * (16 * (s₂ ^ 2 + z₀ ^ 2) + 8 - 32 * x₁ * c)) ≤
          (s₂ ^ 2 - z₀ ^ 2) * (16 * (s₂ ^ 2 + z₀ ^ 2) + 8 - 32 * x₁ * c) := by
        linear_combination mul_nonneg (mul_nonneg hsz hsz) hbr0
      exact h₁.trans (h₂.trans h₃)
    exact le_of_mul_le_mul_right key hDp
  linarith only [step₁, step₂, hT₀]

end IncompressibleFlow.SharpHolder
