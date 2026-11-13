/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearMap

/-!
# Bounds of the vertical transport map of the shear estimates

The map `T(p, t)` of `shearMap` is the nonnegative root of
`t P(p, t, T) = t T³ + t² T² + t T (t² + 2 + 2 p²) - (p² - 1)²`, which increases in `T ≥ 0`, so
the sign of the cubic at a point bounds `T` (`le_shearMap_of_shearCubic_nonpos`,
`shearMap_le_of_shearCubic_nonneg`). The divided differences of `T` in `t` and in `p` are
rational in the values of `T` (`shearMap_sub_mul_eq_right`, `shearMap_sub_mul_eq_left`); with the
monotonicity of `T` they give affine majorants of `t - T(p, t)` on rectangles to the right and to
the left of `p = 1` (`sub_shearMap_le_affine_right`, `sub_shearMap_le_affine_left`).

The sign quartic `Q(p, t)` of `Δ` is convex in `p²` and decreasing in `t ≥ 0`
(`shearQuartic_le_max`, `shearQuartic_le_of_right`, `shearQuartic_le_of_left`). Where `Q ≤ 0`
and `p > 0`, `Δ ≥ 0` and `T ≤ t` (`shearDifference_nonneg_of_shearQuartic_nonpos`,
`shearMap_le_self_of_shearQuartic_nonpos`); where `Q ≥ 0`, `t ≤ s_c(p)`
(`le_shearThreshold_of_shearQuartic_nonneg`).

## Main results

* `le_shearMap_of_shearCubic_nonpos`, `shearMap_le_of_shearCubic_nonneg`: for `t > 0` and
  `T ≥ 0`, `P(p, t, T) ≤ 0` gives `T ≤ T(p, t)` and `P(p, t, T) ≥ 0` gives `T(p, t) ≤ T`.
* `antitoneOn_shearMap_right`: `T(p, ·)` decreases on `(0, ∞)`.
* `shearMap_sub_mul_eq_right`, `shearMap_sub_mul_eq_left`: the divided differences of `T` in `t`
  and in `p` as rational identities in the values of `T`.
* `sub_shearMap_le_affine_right`, `sub_shearMap_le_affine_left`: affine majorants of
  `t - T(p, t)` on rectangles to the right and to the left of `p = 1`.
* `shearQuartic_le_max`: on `[p₀, p₁]` above `t₀ ≥ 0`, `Q` is at most its larger value at the
  two lower corners.
* `shearDifference_nonneg_of_shearQuartic_nonpos`, `shearMap_le_self_of_shearQuartic_nonpos`:
  where `Q ≤ 0` and `p > 0`, `Δ ≥ 0` and `T(p, t) ≤ t`.
* `le_shearThreshold_of_shearQuartic_nonneg`: where `Q ≥ 0`, `t ≤ s_c(p)`.
-/

@[expose] public section

noncomputable section

open Set

namespace IncompressibleFlow.SharpHolder

/-! ### Root bounds -/

/-- `t P(p, t, T)` as a polynomial. -/
theorem mul_shearCubic_eq (p : ℝ) {t : ℝ} (ht : t ≠ 0) (T : ℝ) :
    t * shearCubic p t T =
      t * T ^ 3 + t ^ 2 * T ^ 2 + t * T * (t ^ 2 + 2 + 2 * p ^ 2) - (p ^ 2 - 1) ^ 2 := by
  simp only [shearCubic]
  field_simp

/-- For `t > 0` and `T ≥ 0`, `P(p, t, T) ≤ 0` gives `T ≤ T(p, t)`. -/
theorem le_shearMap_of_shearCubic_nonpos {p t T : ℝ} (ht : 0 < t) (hT : 0 ≤ T)
    (h : shearCubic p t T ≤ 0) : T ≤ shearMap p t := by
  by_contra hlt
  push Not at hlt
  have := shearCubic_strictMonoOn (y₁ := p) ht (show shearMap p t ∈ Ici 0 from
    shearMap_nonneg ht) (show T ∈ Ici 0 from hT) hlt
  rw [shearCubic_shearMap] at this
  linarith

/-- For `t > 0` and `T ≥ 0`, `P(p, t, T) ≥ 0` gives `T(p, t) ≤ T`. -/
theorem shearMap_le_of_shearCubic_nonneg {p t T : ℝ} (ht : 0 < t) (hT : 0 ≤ T)
    (h : 0 ≤ shearCubic p t T) : shearMap p t ≤ T := by
  by_contra hlt
  push Not at hlt
  have := shearCubic_strictMonoOn (y₁ := p) ht (show T ∈ Ici 0 from hT)
    (show shearMap p t ∈ Ici 0 from shearMap_nonneg ht) hlt
  rw [shearCubic_shearMap] at this
  linarith

/-- `T(±1, t) = 0`. -/
theorem shearMap_eq_zero_of_sq_eq_one {p t : ℝ} (h : p ^ 2 = 1) :
    shearMap p t = 0 :=
  (eq_shearMap_of_shearCubic_eq_zero (by simp [shearCubic, h])).symm

/-- `T(p, ·)` decreases on `(0, ∞)` for every `p`. -/
theorem antitoneOn_shearMap_right (p : ℝ) : AntitoneOn (shearMap p) (Ioi 0) := by
  by_cases h : p ^ 2 = 1
  · intro t _ t' _ _
    rw [shearMap_eq_zero_of_sq_eq_one h, shearMap_eq_zero_of_sq_eq_one h]
  · exact (strictAntiOn_shearMap_right h).antitoneOn

/-! ### Divided differences -/

/-- The divided difference in `t`: with `T = T(p, t)`, `T' = T(p, t')`,
`T (t - t') A(t, t', T) + t' (T - T') A(T, T', t') = 0`, where
`A(x, x', y) = x² + x x' + x'² + y (x + x') + y² + 2 + 2 p²`. -/
theorem shearMap_sub_mul_eq_right (p : ℝ) {t t' : ℝ} (ht : 0 < t) (ht' : 0 < t') :
    shearMap p t * (t - t') * (t ^ 2 + t * t' + t' ^ 2 + shearMap p t * (t + t') +
        shearMap p t ^ 2 + (2 + 2 * p ^ 2)) +
      t' * (shearMap p t - shearMap p t') * (shearMap p t ^ 2 + shearMap p t * shearMap p t' +
        shearMap p t' ^ 2 + t' * (shearMap p t + shearMap p t') + t' ^ 2 + (2 + 2 * p ^ 2)) =
      0 := by
  have e₁ := mul_shearCubic_eq p ht.ne' (shearMap p t)
  have e₂ := mul_shearCubic_eq p ht'.ne' (shearMap p t')
  rw [shearCubic_shearMap, mul_zero] at e₁
  rw [shearCubic_shearMap, mul_zero] at e₂
  generalize shearMap p t = T at *
  generalize shearMap p t' = S at *
  linear_combination (-1 : ℝ) * e₁ + e₂

/-- The divided difference in `p`: with `T = T(p, t)`, `S = T(p', t)`,
`t (T - S) (T² + T S + S² + t (T + S) + t² + 2 + 2 p²) = (p² - p'²)(p² + p'² - 2 - 2 t S)`. -/
theorem shearMap_sub_mul_eq_left (p p' : ℝ) {t : ℝ} (ht : 0 < t) :
    t * (shearMap p t - shearMap p' t) * (shearMap p t ^ 2 + shearMap p t * shearMap p' t +
        shearMap p' t ^ 2 + t * (shearMap p t + shearMap p' t) + t ^ 2 + (2 + 2 * p ^ 2)) =
      (p ^ 2 - p' ^ 2) * (p ^ 2 + p' ^ 2 - 2 - 2 * t * shearMap p' t) := by
  have e₁ := mul_shearCubic_eq p ht.ne' (shearMap p t)
  have e₂ := mul_shearCubic_eq p' ht.ne' (shearMap p' t)
  rw [shearCubic_shearMap, mul_zero] at e₁
  rw [shearCubic_shearMap, mul_zero] at e₂
  generalize shearMap p t = T at *
  generalize shearMap p' t = S at *
  linear_combination (-1 : ℝ) * e₁ + e₂

/-- The lower bound of the decrease of `T(p, ·)` between `t` and `t₁`. -/
private theorem shearMap_slope_right {p p₀ p₁ t t₀ t₁ T₀ T₁ l : ℝ} (hp₀ : 0 ≤ p₀)
    (hp : p ∈ Icc p₀ p₁) (ht₀ : 0 < t₀) (ht : t ∈ Icc t₀ t₁) (hT₀ : 0 ≤ T₀)
    (hlo : T₀ ≤ shearMap p t₁) (hhi : shearMap p t ≤ T₁) (hl : 0 ≤ l)
    (hl' : l * (t₁ * (3 * T₁ ^ 2 + 2 * t₁ * T₁ + t₁ ^ 2 + (2 + 2 * p₁ ^ 2))) ≤
      T₀ * (3 * t₀ ^ 2 + 2 * T₀ * t₀ + T₀ ^ 2 + (2 + 2 * p₀ ^ 2))) :
    l * (t₁ - t) ≤ shearMap p t - shearMap p t₁ := by
  obtain ⟨hpa, hpb⟩ := hp
  obtain ⟨hta, htb⟩ := ht
  have ht0 : 0 < t := ht₀.trans_le hta
  have ht1 : 0 < t₁ := ht0.trans_le htb
  have hid := shearMap_sub_mul_eq_right p ht0 ht1
  have hanti : shearMap p t₁ ≤ shearMap p t := antitoneOn_shearMap_right p ht0 ht1 htb
  generalize shearMap p t = T at *
  generalize shearMap p t₁ = T' at *
  have hT' : 0 ≤ T' := hT₀.trans hlo
  have hT : 0 ≤ T := hT'.trans hanti
  have hT'1 : T' ≤ T₁ := hanti.trans hhi
  set A₁ := t ^ 2 + t * t₁ + t₁ ^ 2 + T * (t + t₁) + T ^ 2 + (2 + 2 * p ^ 2) with hA₁def
  set A₂ := T ^ 2 + T * T' + T' ^ 2 + t₁ * (T + T') + t₁ ^ 2 + (2 + 2 * p ^ 2) with hA₂def
  have hpp : p₀ ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ hp₀ hpa 2
  have hpp' : p ^ 2 ≤ p₁ ^ 2 := pow_le_pow_left₀ (hp₀.trans hpa) hpb 2
  have hA₁ : 3 * t₀ ^ 2 + 2 * T₀ * t₀ + T₀ ^ 2 + (2 + 2 * p₀ ^ 2) ≤ A₁ := by
    have h1 : t₀ ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ ht₀.le hta 2
    have h2 : t₀ * t₀ ≤ t * t₁ := mul_le_mul hta (hta.trans htb) ht₀.le ht0.le
    have h3 : t₀ ^ 2 ≤ t₁ ^ 2 := pow_le_pow_left₀ ht₀.le (hta.trans htb) 2
    have h4 : T₀ * (2 * t₀) ≤ T * (t + t₁) :=
      mul_le_mul (hlo.trans hanti) (by linarith) (by linarith) hT
    have h5 : T₀ ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hT₀ (hlo.trans hanti) 2
    rw [hA₁def]
    nlinarith only [h1, h2, h3, h4, h5, hpp]
  have hA₂ : A₂ ≤ 3 * T₁ ^ 2 + 2 * t₁ * T₁ + t₁ ^ 2 + (2 + 2 * p₁ ^ 2) := by
    have h1 : T ^ 2 ≤ T₁ ^ 2 := pow_le_pow_left₀ hT hhi 2
    have h2 : T * T' ≤ T₁ * T₁ := mul_le_mul hhi hT'1 hT' (hT.trans hhi)
    have h3 : T' ^ 2 ≤ T₁ ^ 2 := pow_le_pow_left₀ hT' hT'1 2
    have h4 : t₁ * (T + T') ≤ t₁ * (2 * T₁) := mul_le_mul_of_nonneg_left (by linarith) ht1.le
    rw [hA₂def]
    nlinarith only [h1, h2, h3, h4, hpp']
  have hA₂pos : 0 < A₂ := by
    have h1 : 0 ≤ T * T' := mul_nonneg hT hT'
    have h2 : 0 ≤ t₁ * (T + T') := mul_nonneg ht1.le (add_nonneg hT hT')
    rw [hA₂def]
    nlinarith only [h1, h2, sq_nonneg T, sq_nonneg T', sq_nonneg t₁, sq_nonneg p]
  have hA₁0 : 0 ≤ 3 * t₀ ^ 2 + 2 * T₀ * t₀ + T₀ ^ 2 + (2 + 2 * p₀ ^ 2) := by positivity
  have hchain : l * (t₁ * A₂) ≤ T * A₁ := by
    calc l * (t₁ * A₂) ≤ l * (t₁ * (3 * T₁ ^ 2 + 2 * t₁ * T₁ + t₁ ^ 2 + (2 + 2 * p₁ ^ 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA₂ ht1.le) hl
      _ ≤ T₀ * (3 * t₀ ^ 2 + 2 * T₀ * t₀ + T₀ ^ 2 + (2 + 2 * p₀ ^ 2)) := hl'
      _ ≤ T * A₁ := mul_le_mul (hlo.trans hanti) hA₁ hA₁0 hT
  have hts : 0 ≤ t₁ - t := by linarith
  have hpos : 0 < t₁ * A₂ := mul_pos ht1 hA₂pos
  have e : (T - T') * (t₁ * A₂) = (t₁ - t) * (T * A₁) := by
    rw [hA₁def, hA₂def]
    linear_combination hid
  refine le_of_mul_le_mul_right ?_ hpos
  calc l * (t₁ - t) * (t₁ * A₂) = (t₁ - t) * (l * (t₁ * A₂)) := by ring
    _ ≤ (t₁ - t) * (T * A₁) := mul_le_mul_of_nonneg_left hchain hts
    _ = (T - T') * (t₁ * A₂) := e.symm

/-- **The affine majorant to the right of `p = 1`.** On `[p₀, p₁] × [t₀, t₁]` with `p₀ ≥ 1`,
`t₀ > 0`, `0 ≤ T₀ ≤ T(p₀, t₁)` and `T(p₁, t₀) ≤ T₁`, slopes `λ, μ ≥ 0` with
`λ t₁ A_hi ≤ T₀ A_lo` and `μ t₁ A_hi ≤ 2 p₀ max(0, 2 p₀² - 2 - 2 t₁ T₁)`, where
`A_hi = 3 T₁² + 2 t₁ T₁ + t₁² + 2 + 2 p₁²` and `A_lo = 3 t₀² + 2 T₀ t₀ + T₀² + 2 + 2 p₀²`, give
`t - T(p, t) ≤ (t₁ - T₀) - (1 + λ)(t₁ - t) - μ (p - p₀)`. -/
theorem sub_shearMap_le_affine_right {p₀ p₁ t₀ t₁ T₀ T₁ l m : ℝ} (hp₀ : 1 ≤ p₀) (ht₀ : 0 < t₀)
    (hT₀ : 0 ≤ T₀) (hT₀le : T₀ ≤ shearMap p₀ t₁) (hT₁le : shearMap p₁ t₀ ≤ T₁) (hl : 0 ≤ l)
    (hl' : l * (t₁ * (3 * T₁ ^ 2 + 2 * t₁ * T₁ + t₁ ^ 2 + (2 + 2 * p₁ ^ 2))) ≤
      T₀ * (3 * t₀ ^ 2 + 2 * T₀ * t₀ + T₀ ^ 2 + (2 + 2 * p₀ ^ 2)))
    (hm : 0 ≤ m)
    (hm' : m * (t₁ * (3 * T₁ ^ 2 + 2 * t₁ * T₁ + t₁ ^ 2 + (2 + 2 * p₁ ^ 2))) ≤
      2 * p₀ * max 0 (2 * p₀ ^ 2 - 2 - 2 * t₁ * T₁))
    {p t : ℝ} (hp : p ∈ Icc p₀ p₁) (ht : t ∈ Icc t₀ t₁) :
    t - shearMap p t ≤ (t₁ - T₀) - (1 + l) * (t₁ - t) - m * (p - p₀) := by
  obtain ⟨hpa, hpb⟩ := hp
  obtain ⟨hta, htb⟩ := ht
  have ht0 : 0 < t := ht₀.trans_le hta
  have ht1 : 0 < t₁ := ht0.trans_le htb
  have hp1 : 1 ≤ p := hp₀.trans hpa
  have hmono : ∀ {a b s : ℝ}, 0 < s → 1 ≤ a → a ≤ b → shearMap a s ≤ shearMap b s :=
    fun hs ha hab ↦ monotoneOn_shearMap_left hs ha (ha.trans hab) hab
  have hS : shearMap p₀ t₁ ≤ shearMap p t₁ := hmono ht1 hp₀ hpa
  have hhi : shearMap p t ≤ T₁ :=
    (antitoneOn_shearMap_right p ht₀ ht0 hta).trans ((hmono ht₀ hp1 hpb).trans hT₁le)
  have key₁ := shearMap_slope_right (hp₀ := zero_le_one.trans hp₀) ⟨hpa, hpb⟩ ht₀ ⟨hta, htb⟩
    hT₀ (hT₀le.trans hS) hhi hl hl'
  have key₂ : m * (p - p₀) ≤ shearMap p t₁ - shearMap p₀ t₁ := by
    rcases eq_or_lt_of_le hm with hm0 | hmpos
    · rw [← hm0, zero_mul]
      linarith
    have hT₁0 : 0 ≤ T₁ := (shearMap_nonneg ht₀).trans hT₁le
    set H := 3 * T₁ ^ 2 + 2 * t₁ * T₁ + t₁ ^ 2 + (2 + 2 * p₁ ^ 2) with hHdef
    have hH : 0 < H := by rw [hHdef]; positivity
    have hp0 : 0 < p₀ := by linarith
    have hf : 0 < 2 * p₀ ^ 2 - 2 - 2 * t₁ * T₁ := by
      by_contra hc
      push Not at hc
      rw [max_eq_left hc, mul_zero] at hm'
      have := mul_pos hmpos (mul_pos ht1 hH)
      linarith
    rw [max_eq_right hf.le] at hm'
    have hid := shearMap_sub_mul_eq_left p p₀ ht1
    have hT1 : shearMap p t₁ ≤ T₁ := (antitoneOn_shearMap_right p ht0 ht1 htb).trans hhi
    have hT01 : shearMap p₀ t₁ ≤ T₁ := hS.trans hT1
    generalize shearMap p t₁ = T at *
    generalize shearMap p₀ t₁ = S at *
    have hS0 : 0 ≤ S := hT₀.trans hT₀le
    have hT0 : 0 ≤ T := hS0.trans hS
    set A := T ^ 2 + T * S + S ^ 2 + t₁ * (T + S) + t₁ ^ 2 + (2 + 2 * p ^ 2) with hAdef
    have hApos : 0 < A := by
      have h1 : 0 ≤ T * S := mul_nonneg hT0 hS0
      have h2 : 0 ≤ t₁ * (T + S) := mul_nonneg ht1.le (add_nonneg hT0 hS0)
      rw [hAdef]
      nlinarith only [h1, h2, sq_nonneg T, sq_nonneg S, sq_nonneg t₁, sq_nonneg p]
    have hAle : A ≤ H := by
      have h1 : T ^ 2 ≤ T₁ ^ 2 := pow_le_pow_left₀ hT0 hT1 2
      have h2 : T * S ≤ T₁ * T₁ := mul_le_mul hT1 hT01 hS0 hT₁0
      have h3 : S ^ 2 ≤ T₁ ^ 2 := pow_le_pow_left₀ hS0 hT01 2
      have h4 : t₁ * (T + S) ≤ t₁ * (2 * T₁) := mul_le_mul_of_nonneg_left (by linarith) ht1.le
      have h5 : p ^ 2 ≤ p₁ ^ 2 := pow_le_pow_left₀ (by linarith) hpb 2
      rw [hAdef, hHdef]
      nlinarith only [h1, h2, h3, h4, h5]
    have hpp : 0 ≤ p - p₀ := by linarith
    have hr1 : (p - p₀) * (2 * p₀) ≤ p ^ 2 - p₀ ^ 2 := by
      have : (p - p₀) * (2 * p₀) ≤ (p - p₀) * (p + p₀) :=
        mul_le_mul_of_nonneg_left (by linarith) hpp
      linarith [show (p - p₀) * (p + p₀) = p ^ 2 - p₀ ^ 2 by ring]
    have hr2 : 2 * p₀ ^ 2 - 2 - 2 * t₁ * T₁ ≤ p ^ 2 + p₀ ^ 2 - 2 - 2 * t₁ * S := by
      have h1 : p₀ ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ hp0.le hpa 2
      have h2 : t₁ * S ≤ t₁ * T₁ := mul_le_mul_of_nonneg_left hT01 ht1.le
      linarith
    have hr1' : 0 ≤ (p - p₀) * (2 * p₀) := mul_nonneg hpp (by linarith)
    have hrhs : (p - p₀) * (2 * p₀) * (2 * p₀ ^ 2 - 2 - 2 * t₁ * T₁) ≤
        (p ^ 2 - p₀ ^ 2) * (p ^ 2 + p₀ ^ 2 - 2 - 2 * t₁ * S) :=
      mul_le_mul hr1 hr2 hf.le (hr1'.trans hr1)
    have hm'' : m * (t₁ * A) ≤ 2 * p₀ * (2 * p₀ ^ 2 - 2 - 2 * t₁ * T₁) :=
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAle ht1.le) hm).trans hm'
    have hpos : 0 < t₁ * A := mul_pos ht1 hApos
    have e : (T - S) * (t₁ * A) = (p ^ 2 - p₀ ^ 2) * (p ^ 2 + p₀ ^ 2 - 2 - 2 * t₁ * S) := by
      rw [hAdef]
      linear_combination hid
    refine le_of_mul_le_mul_right ?_ hpos
    calc m * (p - p₀) * (t₁ * A) = (p - p₀) * (m * (t₁ * A)) := by ring
      _ ≤ (p - p₀) * (2 * p₀ * (2 * p₀ ^ 2 - 2 - 2 * t₁ * T₁)) :=
        mul_le_mul_of_nonneg_left hm'' hpp
      _ = (p - p₀) * (2 * p₀) * (2 * p₀ ^ 2 - 2 - 2 * t₁ * T₁) := by ring
      _ ≤ _ := hrhs
      _ = (T - S) * (t₁ * A) := e.symm
  linarith

/-- **The affine majorant to the left of `p = 1`.** On `[p₀, p₁] × [t₀, t₁]` with
`0 ≤ p₀ ≤ p₁ ≤ 1`, `t₀ > 0`, `0 ≤ T₀ ≤ T(p₁, t₁)` and `T(p₀, t₀) ≤ T₁`, slopes `λ, μ ≥ 0` with
`λ t₁ A_hi ≤ T₀ A_lo` and `μ t₁ A_hi ≤ (p₀ + p₁)(2 - 2 p₁² + 2 t₁ T₀)` give
`t - T(p, t) ≤ (t₁ - T₀) - (1 + λ)(t₁ - t) - μ (p₁ - p)`. -/
theorem sub_shearMap_le_affine_left {p₀ p₁ t₀ t₁ T₀ T₁ l m : ℝ} (hp₀ : 0 ≤ p₀) (hp₁ : p₁ ≤ 1)
    (ht₀ : 0 < t₀) (hT₀ : 0 ≤ T₀) (hT₀le : T₀ ≤ shearMap p₁ t₁) (hT₁le : shearMap p₀ t₀ ≤ T₁)
    (hl : 0 ≤ l)
    (hl' : l * (t₁ * (3 * T₁ ^ 2 + 2 * t₁ * T₁ + t₁ ^ 2 + (2 + 2 * p₁ ^ 2))) ≤
      T₀ * (3 * t₀ ^ 2 + 2 * T₀ * t₀ + T₀ ^ 2 + (2 + 2 * p₀ ^ 2)))
    (hm : 0 ≤ m)
    (hm' : m * (t₁ * (3 * T₁ ^ 2 + 2 * t₁ * T₁ + t₁ ^ 2 + (2 + 2 * p₁ ^ 2))) ≤
      (p₀ + p₁) * (2 - 2 * p₁ ^ 2 + 2 * t₁ * T₀))
    {p t : ℝ} (hp : p ∈ Icc p₀ p₁) (ht : t ∈ Icc t₀ t₁) :
    t - shearMap p t ≤ (t₁ - T₀) - (1 + l) * (t₁ - t) - m * (p₁ - p) := by
  obtain ⟨hpa, hpb⟩ := hp
  obtain ⟨hta, htb⟩ := ht
  have ht0 : 0 < t := ht₀.trans_le hta
  have ht1 : 0 < t₁ := ht0.trans_le htb
  have hanti : ∀ {a b s : ℝ}, 0 < s → 0 ≤ a → a ≤ b → b ≤ 1 → shearMap b s ≤ shearMap a s :=
    fun hs ha hab hb ↦ antitoneOn_shearMap_left hs ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩ hab
  have hp0 : 0 ≤ p := hp₀.trans hpa
  have hS : shearMap p₁ t₁ ≤ shearMap p t₁ := hanti ht1 hp0 hpb hp₁
  have hhi : shearMap p t ≤ T₁ :=
    (antitoneOn_shearMap_right p ht₀ ht0 hta).trans ((hanti ht₀ hp₀ hpa (hpb.trans hp₁)).trans
      hT₁le)
  have key₁ := shearMap_slope_right hp₀ ⟨hpa, hpb⟩ ht₀ ⟨hta, htb⟩ hT₀ (hT₀le.trans hS) hhi hl hl'
  have key₂ : m * (p₁ - p) ≤ shearMap p t₁ - shearMap p₁ t₁ := by
    have hid := shearMap_sub_mul_eq_left p p₁ ht1
    have hT1 : shearMap p t₁ ≤ T₁ := (antitoneOn_shearMap_right p ht0 ht1 htb).trans hhi
    have hT₁0 : 0 ≤ T₁ := (shearMap_nonneg ht₀).trans hT₁le
    generalize shearMap p t₁ = T at *
    generalize shearMap p₁ t₁ = R at *
    have hR0 : 0 ≤ R := hT₀.trans hT₀le
    have hT0 : 0 ≤ T := hR0.trans hS
    have hR1 : R ≤ T₁ := hS.trans hT1
    set H := 3 * T₁ ^ 2 + 2 * t₁ * T₁ + t₁ ^ 2 + (2 + 2 * p₁ ^ 2) with hHdef
    set A := T ^ 2 + T * R + R ^ 2 + t₁ * (T + R) + t₁ ^ 2 + (2 + 2 * p ^ 2) with hAdef
    have hApos : 0 < A := by
      have h1 : 0 ≤ T * R := mul_nonneg hT0 hR0
      have h2 : 0 ≤ t₁ * (T + R) := mul_nonneg ht1.le (add_nonneg hT0 hR0)
      rw [hAdef]
      nlinarith only [h1, h2, sq_nonneg T, sq_nonneg R, sq_nonneg t₁, sq_nonneg p]
    have hAle : A ≤ H := by
      have h1 : T ^ 2 ≤ T₁ ^ 2 := pow_le_pow_left₀ hT0 hT1 2
      have h2 : T * R ≤ T₁ * T₁ := mul_le_mul hT1 hR1 hR0 hT₁0
      have h3 : R ^ 2 ≤ T₁ ^ 2 := pow_le_pow_left₀ hR0 hR1 2
      have h4 : t₁ * (T + R) ≤ t₁ * (2 * T₁) := mul_le_mul_of_nonneg_left (by linarith) ht1.le
      have h5 : p ^ 2 ≤ p₁ ^ 2 := pow_le_pow_left₀ hp0 hpb 2
      rw [hAdef, hHdef]
      nlinarith only [h1, h2, h3, h4, h5]
    have hpp : 0 ≤ p₁ - p := by linarith
    have hp1sq : p₁ ^ 2 ≤ 1 := by
      have := pow_le_pow_left₀ (hp₀.trans (hpa.trans hpb)) hp₁ 2
      simpa using this
    have hg : 0 ≤ 2 - 2 * p₁ ^ 2 + 2 * t₁ * T₀ := by
      have : 0 ≤ t₁ * T₀ := mul_nonneg ht1.le hT₀
      linarith
    have hr1 : (p₁ - p) * (p₀ + p₁) ≤ p₁ ^ 2 - p ^ 2 := by
      have : (p₁ - p) * (p₀ + p₁) ≤ (p₁ - p) * (p + p₁) :=
        mul_le_mul_of_nonneg_left (by linarith) hpp
      linarith [show (p₁ - p) * (p + p₁) = p₁ ^ 2 - p ^ 2 by ring]
    have hr2 : 2 - 2 * p₁ ^ 2 + 2 * t₁ * T₀ ≤ 2 - p ^ 2 - p₁ ^ 2 + 2 * t₁ * R := by
      have h1 : p ^ 2 ≤ p₁ ^ 2 := pow_le_pow_left₀ hp0 hpb 2
      have h2 : t₁ * T₀ ≤ t₁ * R := mul_le_mul_of_nonneg_left hT₀le ht1.le
      linarith
    have hr1' : 0 ≤ (p₁ - p) * (p₀ + p₁) := mul_nonneg hpp (by linarith)
    have hrhs : (p₁ - p) * (p₀ + p₁) * (2 - 2 * p₁ ^ 2 + 2 * t₁ * T₀) ≤
        (p₁ ^ 2 - p ^ 2) * (2 - p ^ 2 - p₁ ^ 2 + 2 * t₁ * R) :=
      mul_le_mul hr1 hr2 hg (hr1'.trans hr1)
    have hm'' : m * (t₁ * A) ≤ (p₀ + p₁) * (2 - 2 * p₁ ^ 2 + 2 * t₁ * T₀) :=
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAle ht1.le) hm).trans hm'
    have hpos : 0 < t₁ * A := mul_pos ht1 hApos
    have e : (T - R) * (t₁ * A) = (p₁ ^ 2 - p ^ 2) * (2 - p ^ 2 - p₁ ^ 2 + 2 * t₁ * R) := by
      rw [hAdef]
      linear_combination hid
    refine le_of_mul_le_mul_right ?_ hpos
    calc m * (p₁ - p) * (t₁ * A) = (p₁ - p) * (m * (t₁ * A)) := by ring
      _ ≤ (p₁ - p) * ((p₀ + p₁) * (2 - 2 * p₁ ^ 2 + 2 * t₁ * T₀)) :=
        mul_le_mul_of_nonneg_left hm'' hpp
      _ = (p₁ - p) * (p₀ + p₁) * (2 - 2 * p₁ ^ 2 + 2 * t₁ * T₀) := by ring
      _ ≤ _ := hrhs
      _ = (T - R) * (t₁ * A) := e.symm
  linarith

/-! ### The sign quartic -/

/-- `Q(p, ·)` decreases on `[0, ∞)`. -/
theorem shearQuartic_le_of_le {p t t' : ℝ} (ht : 0 ≤ t) (htt : t ≤ t') :
    shearQuartic p t' ≤ shearQuartic p t := by
  have h1 : t ^ 2 ≤ t' ^ 2 := pow_le_pow_left₀ ht htt 2
  have h2 : (t ^ 2) ^ 2 ≤ (t' ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg t) h1 2
  simp only [shearQuartic]
  nlinarith [sq_nonneg p]

/-- `Q(·, t₀)` is convex in `p²`, so on `[p₀, p₁]` (with `p₀ ≥ 0`) and above `t₀ ≥ 0` it is at
most its larger value at the two lower corners. -/
theorem shearQuartic_le_max {p₀ p₁ t₀ p t : ℝ} (hp₀ : 0 ≤ p₀) (hp : p ∈ Icc p₀ p₁)
    (ht₀ : 0 ≤ t₀) (ht : t₀ ≤ t) :
    shearQuartic p t ≤ max (shearQuartic p₀ t₀) (shearQuartic p₁ t₀) := by
  refine (shearQuartic_le_of_le ht₀ ht).trans ?_
  obtain ⟨hpa, hpb⟩ := hp
  have hu₀ : p₀ ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ hp₀ hpa 2
  have hu₁ : p ^ 2 ≤ p₁ ^ 2 := pow_le_pow_left₀ (hp₀.trans hpa) hpb 2
  have e₀ : shearQuartic p t₀ - shearQuartic p₀ t₀ =
      (p ^ 2 - p₀ ^ 2) * (p ^ 2 + p₀ ^ 2 - 2 * (t₀ ^ 2 + 1)) := by
    simp only [shearQuartic]; ring
  have e₁ : shearQuartic p t₀ - shearQuartic p₁ t₀ =
      (p ^ 2 - p₁ ^ 2) * (p ^ 2 + p₁ ^ 2 - 2 * (t₀ ^ 2 + 1)) := by
    simp only [shearQuartic]; ring
  rcases le_total (p ^ 2 + p₀ ^ 2) (2 * (t₀ ^ 2 + 1)) with h | h
  · have : shearQuartic p t₀ ≤ shearQuartic p₀ t₀ := by
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hu₀) (sub_nonpos.2 h)]
    exact this.trans (le_max_left _ _)
  · have : shearQuartic p t₀ ≤ shearQuartic p₁ t₀ := by
      nlinarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hu₁)
        (show 0 ≤ p ^ 2 + p₁ ^ 2 - 2 * (t₀ ^ 2 + 1) by linarith)]
    exact this.trans (le_max_right _ _)

/-- To the right of `p_b` with `p_b² ≥ t₁² + 1` and below `t₁`, `Q ≥ Q(p_b, t₁)`. -/
theorem shearQuartic_le_of_right {p_b p t t₁ : ℝ} (hb : t₁ ^ 2 + 1 ≤ p_b ^ 2) (hb0 : 0 ≤ p_b)
    (hp : p_b ≤ p) (ht : 0 ≤ t) (htt : t ≤ t₁) : shearQuartic p_b t₁ ≤ shearQuartic p t := by
  refine (shearQuartic_le_of_le ht htt).trans ?_
  have hu : p_b ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ hb0 hp 2
  have htt' : t ^ 2 ≤ t₁ ^ 2 := pow_le_pow_left₀ ht htt 2
  have e : shearQuartic p t - shearQuartic p_b t =
      (p ^ 2 - p_b ^ 2) * (p ^ 2 + p_b ^ 2 - 2 * (t ^ 2 + 1)) := by
    simp only [shearQuartic]; ring
  nlinarith [mul_nonneg (sub_nonneg.2 hu) (show 0 ≤ p ^ 2 + p_b ^ 2 - 2 * (t ^ 2 + 1) by linarith)]

/-- To the left of `p_a ≤ 1` and below `t₁`, `Q ≥ Q(p_a, t₁)`. -/
theorem shearQuartic_le_of_left {p_a p t t₁ : ℝ} (ha : p_a ≤ 1) (hp0 : 0 ≤ p) (hp : p ≤ p_a)
    (ht : 0 ≤ t) (htt : t ≤ t₁) : shearQuartic p_a t₁ ≤ shearQuartic p t := by
  refine (shearQuartic_le_of_le ht htt).trans ?_
  have hu : p ^ 2 ≤ p_a ^ 2 := pow_le_pow_left₀ hp0 hp 2
  have hu1 : p_a ^ 2 ≤ 1 := by nlinarith
  have e : shearQuartic p t - shearQuartic p_a t =
      (p ^ 2 - p_a ^ 2) * (p ^ 2 + p_a ^ 2 - 2 * (t ^ 2 + 1)) := by
    simp only [shearQuartic]; ring
  nlinarith [mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 hu)
    (show p ^ 2 + p_a ^ 2 - 2 * (t ^ 2 + 1) ≤ 0 by nlinarith [sq_nonneg t])]

/-- Where `Q ≤ 0` and `p > 0`, `Δ ≥ 0`. -/
theorem shearDifference_nonneg_of_shearQuartic_nonpos {p t : ℝ} (hp : 0 < p) (ht : 0 < t)
    (h : shearQuartic p t ≤ 0) : 0 ≤ shearDifference p t := by
  have h₁ : (p + 1) ^ 2 + t ^ 2 ≠ 0 := by positivity
  have h₂ : (p - 1) ^ 2 + t ^ 2 ≠ 0 := by positivity
  rw [shearDifference_eq h₁ h₂]
  exact div_nonneg (by nlinarith) (by positivity)

/-- Where `Q ≤ 0`, `T(p, t) ≤ t`. -/
theorem shearMap_le_self_of_shearQuartic_nonpos {p t : ℝ} (ht : 0 < t)
    (h : shearQuartic p t ≤ 0) : shearMap p t ≤ t := by
  have e := mul_shearCubic_self ht.ne' p
  refine shearMap_le_of_shearCubic_nonneg ht ht.le ?_
  by_contra hc
  push Not at hc
  have := mul_neg_of_pos_of_neg ht hc
  linarith

/-- Above the threshold the sign quartic is negative. -/
theorem shearQuartic_neg_of_shearThreshold_lt {p t : ℝ} (h : shearThreshold p < t) :
    shearQuartic p t < 0 := by
  have hs : 0 ≤ shearThreshold p := Real.sqrt_nonneg _
  rw [shearQuartic_eq_threshold]
  have hw := Real.sqrt_nonneg (p ^ 4 - p ^ 2 + 1)
  have ha : 0 < t ^ 2 - (-(p ^ 2 + 1) - 2 * Real.sqrt (p ^ 4 - p ^ 2 + 1)) / 3 := by
    linarith [sq_nonneg t, sq_nonneg p]
  have hb : 0 < t ^ 2 - shearThreshold p ^ 2 := by nlinarith
  have := mul_pos hb ha
  linarith

/-- Where `Q ≥ 0`, `t ≤ s_c(p)`. -/
theorem le_shearThreshold_of_shearQuartic_nonneg {p t : ℝ} (ht : 0 ≤ t)
    (h : 0 ≤ shearQuartic p t) : t ≤ shearThreshold p := by
  rw [shearQuartic_eq_threshold] at h
  have hw := Real.sqrt_nonneg (p ^ 4 - p ^ 2 + 1)
  have ha : 0 < t ^ 2 - (-(p ^ 2 + 1) - 2 * Real.sqrt (p ^ 4 - p ^ 2 + 1)) / 3 := by
    linarith [sq_nonneg t, sq_nonneg p]
  have hle : t ^ 2 ≤ shearThreshold p ^ 2 := by
    by_contra hc
    push Not at hc
    have := mul_pos (sub_pos.2 hc) ha
    linarith
  exact (pow_le_pow_iff_left₀ ht (Real.sqrt_nonneg _) two_ne_zero).1 hle

end IncompressibleFlow.SharpHolder
