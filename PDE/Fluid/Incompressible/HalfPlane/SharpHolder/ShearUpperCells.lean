/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearConstantCells

/-!
# The rational cells of the shear column cost to the left of `p = 1`

The horizontal estimates of `u_y` and `v_x` transport every column `p > 0`. To the left of `p = 1`
the map `T(·, t)` decreases, and a slab `[t₀, t₁]` splits into the zero region `p ≤ p_a ≈ h⁻(t₁)`
(where the sign quartic is `≥ 0`), the strip `[p_a, p_b]`, `p_b ≈ h⁻(t₀)`, and the cells from `p_b`
to `1`, walked in `w = 1 - p` (`shearSlabLeft`). On a cell the evaluator mirrors
`shearCellRight` with the majorant of `sub_shearMap_le_affine_left` (`shearCellLeft`).

## Main definitions

* `shearSlopesLeft`: the slopes `(λ, μ)` of the affine majorant to the left of `p = 1`.
* `shearCellLeft`: the bound of a cell `[p₀, p₁] × [t₀, t₁]` to the left of `p = 1`.
* `shearStripLeft`: the bound of the band `[p_a, p_b] × [t₀, t₁]` at the threshold.
* `shearSlabLeft`: the bound of the slab `[t₀, t₁]` over the columns `0 < p ≤ 1`.
* `shearSlabCost`: the transport cost of the slab `[t₀, t₁]` over all columns `p > 0`.

## Main results

* `shearSlopesLeft_spec`: the slopes are nonnegative and satisfy the hypotheses of
  `sub_shearMap_le_affine_left`.
* `lintegral_le_shearCellLeft`: if `shearCellLeft t₀ t₁ p₀ p₁ = some n`, the column density over
  the cell has integral at most `n/2⁶⁴`.
* `lintegral_le_shearStripLeft`: the strip bound is sound.
* `lintegral_le_shearSlabLeft`: if `shearSlabLeft ρ t₀ t₁ = some N`, the column density over
  `(t₀, t₁] × (0, 1]` has integral at most `N/2⁶⁴`.
* `lintegral_le_shearSlabCost`: if `shearSlabCost ρ t₀ t₁ = some N`, the column density over
  `(t₀, t₁] × (0, ∞)` has integral at most `N/2⁶⁴`.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory PDE.Analysis
open scoped ENNReal

namespace IncompressibleFlow.SharpHolder

/-! ### Cells to the left of `p = 1` -/

/-- The slopes `(λ, μ)` of the affine majorant to the left of `p = 1`. -/
def shearSlopesLeft (p₀ p₁ t₀ t₁ T₀ T₁ : ℚ) : ℚ × ℚ :=
  let H := t₁ * (3 * T₁ ^ 2 + 2 * t₁ * T₁ + t₁ ^ 2 + (2 + 2 * p₁ ^ 2))
  (max 0 (roundDownRel (T₀ * (3 * t₀ ^ 2 + 2 * T₀ * t₀ + T₀ ^ 2 + (2 + 2 * p₀ ^ 2)) / H)),
    max 0 (roundDownRel ((p₀ + p₁) * (2 - 2 * p₁ ^ 2 + 2 * t₁ * T₀) / H)))

/-- The slopes `(λ, μ)` are nonnegative, and their products with
`H = t₁ (3 T₁² + 2 t₁ T₁ + t₁² + 2 + 2 p₁²)` are at most `T₀ (3 t₀² + 2 T₀ t₀ + T₀² + 2 + 2 p₀²)`
and `(p₀ + p₁)(2 - 2 p₁² + 2 t₁ T₀)`. -/
theorem shearSlopesLeft_spec {p₀ p₁ t₀ t₁ T₀ T₁ : ℚ} (hp₀ : 0 ≤ p₀) (hp : p₀ ≤ p₁)
    (hp₁ : p₁ ≤ 1) (ht₁ : 0 < t₁) (hT₀ : 0 ≤ T₀) (hT₁ : 0 ≤ T₁) :
    0 ≤ (shearSlopesLeft p₀ p₁ t₀ t₁ T₀ T₁).1 ∧ 0 ≤ (shearSlopesLeft p₀ p₁ t₀ t₁ T₀ T₁).2 ∧
      ((shearSlopesLeft p₀ p₁ t₀ t₁ T₀ T₁).1 : ℝ) *
          (t₁ * (3 * T₁ ^ 2 + 2 * t₁ * T₁ + t₁ ^ 2 + (2 + 2 * p₁ ^ 2))) ≤
        T₀ * (3 * t₀ ^ 2 + 2 * T₀ * t₀ + T₀ ^ 2 + (2 + 2 * p₀ ^ 2)) ∧
      ((shearSlopesLeft p₀ p₁ t₀ t₁ T₀ T₁).2 : ℝ) *
          (t₁ * (3 * T₁ ^ 2 + 2 * t₁ * T₁ + t₁ ^ 2 + (2 + 2 * p₁ ^ 2))) ≤
        ((p₀ : ℝ) + p₁) * (2 - 2 * (p₁ : ℝ) ^ 2 + 2 * t₁ * T₀) := by
  have hH : 0 < t₁ * (3 * T₁ ^ 2 + 2 * t₁ * T₁ + t₁ ^ 2 + (2 + 2 * p₁ ^ 2)) :=
    mul_pos ht₁ (by nlinarith [sq_nonneg T₁, sq_nonneg t₁, sq_nonneg p₁, mul_nonneg ht₁.le hT₁])
  have hp1 : p₁ ^ 2 ≤ 1 := by nlinarith
  have h₁ := max_roundDownRel_div_mul_le
    (C := T₀ * (3 * t₀ ^ 2 + 2 * T₀ * t₀ + T₀ ^ 2 + (2 + 2 * p₀ ^ 2)))
    (mul_nonneg hT₀ (by nlinarith [sq_nonneg (T₀ + t₀), sq_nonneg t₀, sq_nonneg p₀])) hH
  have h₂ := max_roundDownRel_div_mul_le (C := (p₀ + p₁) * (2 - 2 * p₁ ^ 2 + 2 * t₁ * T₀))
    (mul_nonneg (by linarith) (by nlinarith [mul_nonneg ht₁.le hT₀])) hH
  simp only [shearSlopesLeft]
  exact ⟨le_max_left _ _, le_max_left _ _, by exact_mod_cast h₁, by exact_mod_cast h₂⟩

/-- The second-order value of a cell to the left of `p = 1` with the slopes `λ, μ`. -/
def shearSecondValueLeft (p₀ p₁ t₀ t₁ T₀ l m : ℚ) : ℚ :=
  let c₀ := t₁ - T₀
  let c₁ := 1 + l
  let r := shearRadius p₀ p₁ t₀ t₁ c₀ c₁ m
  shearCellHigh ((c₀ - c₁ * t₁ - m * p₁ + r ^ 2) / (2 * r)) (m / (2 * r)) (c₁ / (2 * r))
    p₀ p₁ t₀ t₁

/-- **The cell bound** of `[p₀, p₁] × [t₀, t₁]` to the left of `p = 1`, after the checks. -/
def shearCellLeft (t₀ t₁ p₀ p₁ : ℚ) : Option ℤ :=
  let T₀ := shearMapLow p₁ t₁
  let T₁ := shearMapApprox p₀ t₀
  if decide (0 ≤ p₀) && decide (p₀ ≤ p₁) && decide (p₁ ≤ 1) && decide (0 < t₀) &&
      decide (t₀ ≤ t₁) && decide (shearQuarticRat p₀ t₀ ≤ 0) &&
      decide (shearQuarticRat p₁ t₀ ≤ 0) && shearLowOk p₁ t₁ T₀ && shearHighOk p₀ t₀ T₁ &&
      decide (T₀ ≤ t₁) then
    some (ceilScaled 64 (min (shearFirstValue p₀ p₁ t₀ t₁ T₀)
      (shearSecondValueLeft p₀ p₁ t₀ t₁ T₀ (shearSlopesLeft p₀ p₁ t₀ t₁ T₀ T₁).1
        (shearSlopesLeft p₀ p₁ t₀ t₁ T₀ T₁).2)))
  else none

/-- **Soundness of a cell to the left of `p = 1`.** -/
theorem lintegral_le_shearCellLeft {t₀ t₁ p₀ p₁ : ℚ} {n : ℤ}
    (h : shearCellLeft t₀ t₁ p₀ p₁ = some n) :
    ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioc (p₀ : ℝ) p₁, shearColumnDensity p t ≤
      ENNReal.ofReal (n / 2 ^ 64) := by
  unfold shearCellLeft at h
  dsimp only at h
  split_ifs at h with hck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hp₀, hp⟩, hp₁⟩, ht₀⟩, ht⟩, hQ₀⟩, hQ₁⟩, hlo⟩, hhi⟩, hT₀t⟩ := hck
  obtain rfl := Option.some.inj h
  set T₀ := shearMapLow p₁ t₁
  set T₁ := shearMapApprox p₀ t₀
  have ht₁ : 0 < t₁ := ht₀.trans_le ht
  have hp₀' : (0 : ℝ) ≤ p₀ := by exact_mod_cast hp₀
  have hp' : (p₀ : ℝ) ≤ p₁ := by exact_mod_cast hp
  have hp₁' : (p₁ : ℝ) ≤ 1 := by exact_mod_cast hp₁
  have ht₀' : (0 : ℝ) < t₀ := by exact_mod_cast ht₀
  have ht' : (t₀ : ℝ) ≤ t₁ := by exact_mod_cast ht
  have ht₁' : (0 : ℝ) < t₁ := by exact_mod_cast ht₁
  have hT₀0 : 0 ≤ T₀ := le_max_left _ _
  have hT₁0 : 0 ≤ T₁ := by
    simp only [shearHighOk, Bool.and_eq_true, decide_eq_true_eq] at hhi; exact hhi.1
  have hTlo : (T₀ : ℝ) ≤ shearMap p₁ t₁ := le_shearMap_of_shearLowOk ht₁ hlo
  have hThi : shearMap p₀ t₀ ≤ (T₁ : ℝ) := shearMap_le_of_shearHighOk ht₀ hhi
  have hQ : ∀ p ∈ Icc (p₀ : ℝ) p₁, ∀ t ∈ Icc (t₀ : ℝ) t₁, shearQuartic p t ≤ 0 :=
    fun p hp t ht ↦ (shearQuartic_le_max hp₀' hp ht₀'.le ht.1).trans <| max_le
      (cast_shearQuarticRat p₀ t₀ ▸ Rat.cast_nonpos.2 hQ₀)
      (cast_shearQuarticRat p₁ t₀ ▸ Rat.cast_nonpos.2 hQ₁)
  have hTcell : ∀ p ∈ Icc (p₀ : ℝ) p₁, ∀ t ∈ Icc (t₀ : ℝ) t₁, (T₀ : ℝ) ≤ shearMap p t :=
    fun p hp t ht ↦ hTlo.trans <| (antitoneOn_shearMap_left ht₁'
      ⟨hp₀'.trans hp.1, hp.2.trans hp₁'⟩ ⟨hp₀'.trans hp', hp₁'⟩ hp.2).trans
      (antitoneOn_shearMap_right p (ht₀'.trans_le ht.1) ht₁' ht.2)
  have hh1 : 0 ≤ ((p₀ : ℚ) - 1) * (p₁ - 1) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  -- the first-order value
  have hfirst : ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioc (p₀ : ℝ) p₁, shearColumnDensity p t ≤
      ENNReal.ofReal (shearFirstValue p₀ p₁ t₀ t₁ T₀) := by
    set r := sqrtApproxRel (t₁ - T₀)
    have hr : 0 < r := sqrtApproxRel_pos _
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    have hα : 0 ≤ (t₁ - T₀ + r ^ 2) / (2 * r) :=
      div_nonneg (by nlinarith [sq_nonneg r]) (by linarith)
    refine (lintegral_shearColumnDensity_cell_le (α := (((t₁ - T₀ + r ^ 2) / (2 * r) : ℚ) : ℝ))
      (β := 0) (γ := 0) (r := r) hp₀' hp' ht₀' ht' hr' hQ (fun p hp t ht ↦ ?_)).trans ?_
    · have := hTcell p hp t ht
      push_cast
      simp only [zero_mul, add_zero]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      linarith [ht.2]
    · exact ENNReal.ofReal_le_ofReal (by
        simpa only [shearFirstValue, Rat.cast_mul] using
          cornerSum_le_mul_shearMassHigh hα hp₀ hp hh1 ht₀ ht)
  -- the second-order value
  obtain ⟨hl0, hm0, hl', hm'⟩ := shearSlopesLeft_spec (p₀ := p₀) (p₁ := p₁) (t₀ := t₀)
    (t₁ := t₁) (T₀ := T₀) (T₁ := T₁) hp₀ hp hp₁ ht₁ hT₀0 hT₁0
  set l := (shearSlopesLeft p₀ p₁ t₀ t₁ T₀ T₁).1
  set m := (shearSlopesLeft p₀ p₁ t₀ t₁ T₀ T₁).2
  have hsecond : ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioc (p₀ : ℝ) p₁, shearColumnDensity p t ≤
      ENNReal.ofReal (shearSecondValueLeft p₀ p₁ t₀ t₁ T₀ l m) := by
    set r := shearRadius p₀ p₁ t₀ t₁ (t₁ - T₀) (1 + l) m
    have hr : 0 < r := sqrtApproxRel_pos _
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    refine (lintegral_shearColumnDensity_cell_le
      (α := ((((t₁ - T₀) - (1 + l) * t₁ - m * p₁ + r ^ 2) / (2 * r) : ℚ) : ℝ))
      (β := ((m / (2 * r) : ℚ) : ℝ)) (γ := (((1 + l) / (2 * r) : ℚ) : ℝ)) (r := r)
      hp₀' hp' ht₀' ht' hr' hQ (fun p hp t ht ↦ ?_)).trans ?_
    · have hL := sub_shearMap_le_affine_left hp₀' hp₁' ht₀' (by exact_mod_cast hT₀0) hTlo hThi
        (by exact_mod_cast hl0) hl' (by exact_mod_cast hm0) hm' hp ht
      have e : ((((t₁ - T₀) - (1 + l) * t₁ - m * p₁ + r ^ 2) / (2 * r) : ℚ) : ℝ) +
          ((m / (2 * r) : ℚ) : ℝ) * p + (((1 + l) / (2 * r) : ℚ) : ℝ) * t =
          ((t₁ - T₀) - (1 + l) * (t₁ - t) - m * (p₁ - p) + r ^ 2) / (2 * r) := by
        push_cast
        field_simp
        ring
      rw [e]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      linarith
    · exact ENNReal.ofReal_le_ofReal (cornerSum_le_shearCellHigh
        (((t₁ - T₀) - (1 + l) * t₁ - m * p₁ + r ^ 2) / (2 * r))
        (m / (2 * r)) ((1 + l) / (2 * r)) hp₀ hp hh1 ht₀ ht)
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal (le_ceilScaled_real 64 _))
  rcases min_choice (shearFirstValue p₀ p₁ t₀ t₁ T₀) (shearSecondValueLeft p₀ p₁ t₀ t₁ T₀ l m)
    with hmin | hmin <;> rw [hmin]
  exacts [hfirst, hsecond]

/-! ### The strip at the left threshold and the left slabs -/

/-- The strip value of the band `[p_a, p_b] × [t₀, t₁]` at the threshold to the left of `p = 1`:
the area times `2 p_b max(0, -Q(p_b, t₁)) / (((p_a + 1)² + t₀²)² ((1 - p_b)² + t₀²)²)` times an
upper bound of `(t₁ - T(p_b, t₁))^{1/2}`. -/
def shearStripLeft (t₀ t₁ pa pb : ℚ) : Option ℚ :=
  let Ts := shearMapLow pb t₁
  if shearLowOk pb t₁ Ts && decide (Ts ≤ t₁) && decide (0 ≤ pa) && decide (pa ≤ pb) &&
      decide (pb ≤ 1) && decide (0 < t₀) && decide (t₀ ≤ t₁) then
    some ((pb - pa) * (t₁ - t₀) * (2 * pb * max 0 (-shearQuarticRat pb t₁) /
      (((pa + 1) ^ 2 + t₀ ^ 2) ^ 2 * ((1 - pb) ^ 2 + t₀ ^ 2) ^ 2) * sqrtHigh (t₁ - Ts)))
  else none

/-- **Soundness of the left strip.** -/
theorem lintegral_le_shearStripLeft {t₀ t₁ pa pb v : ℚ}
    (h : shearStripLeft t₀ t₁ pa pb = some v) :
    ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioc (pa : ℝ) pb, shearColumnDensity p t ≤
      ENNReal.ofReal v := by
  unfold shearStripLeft at h
  dsimp only at h
  split_ifs at h with hck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨⟨⟨⟨hlo, hTs⟩, hpa⟩, hab⟩, hpb⟩, ht₀⟩, ht⟩ := hck
  obtain rfl := Option.some.inj h
  set Ts := shearMapLow pb t₁
  have ht₁ : 0 < t₁ := ht₀.trans_le ht
  have ht₀' : (0 : ℝ) < t₀ := by exact_mod_cast ht₀
  have ht₁' : (0 : ℝ) < t₁ := by exact_mod_cast ht₁
  have hpa' : (0 : ℝ) ≤ pa := by exact_mod_cast hpa
  have hab' : (pa : ℝ) ≤ pb := by exact_mod_cast hab
  have hpb' : (pb : ℝ) ≤ 1 := by exact_mod_cast hpb
  have hTlo : (Ts : ℝ) ≤ shearMap pb t₁ := le_shearMap_of_shearLowOk ht₁ hlo
  set Dm : ℚ := ((pa + 1) ^ 2 + t₀ ^ 2) ^ 2 * ((1 - pb) ^ 2 + t₀ ^ 2) ^ 2 with hDm
  have hDm0 : 0 < Dm := by positivity
  set D : ℚ := 2 * pb * max 0 (-shearQuarticRat pb t₁) / Dm with hD
  have hD0 : 0 ≤ D := div_nonneg (mul_nonneg (by linarith) (le_max_left _ _)) hDm0.le
  refine (lintegral_shearColumnDensity_strip_le (D := D) (φ := ((t₁ - Ts : ℚ) : ℝ)) hab'
    (by exact_mod_cast hD0) (fun p hp t ht' hs ↦ ?_)).trans (ENNReal.ofReal_le_ofReal ?_)
  · have ht0 : 0 < t := ht₀'.trans ht'.1
    have hp0 : 0 < p := hpa'.trans_lt hp.1
    have hp1 : p ≤ 1 := hp.2.trans hpb'
    have hQneg := shearQuartic_neg_of_shearThreshold_lt hs
    have hQle : shearQuartic pb t₁ ≤ shearQuartic p t :=
      shearQuartic_le_of_left hpb' hp0.le hp.2 ht0.le ht'.2
    have h₁ : (p + 1) ^ 2 + t ^ 2 ≠ 0 := by positivity
    have h₂ : (p - 1) ^ 2 + t ^ 2 ≠ 0 := by positivity
    constructor
    · rw [shearDifference_eq h₁ h₂]
      have hnum : 0 ≤ -2 * p * shearQuartic p t := by nlinarith
      have hden : 0 < ((p + 1) ^ 2 + t ^ 2) ^ 2 * ((p - 1) ^ 2 + t ^ 2) ^ 2 := by positivity
      rw [abs_of_nonneg (div_nonneg hnum hden.le)]
      have hDm' : (Dm : ℝ) ≤ ((p + 1) ^ 2 + t ^ 2) ^ 2 * ((p - 1) ^ 2 + t ^ 2) ^ 2 := by
        rw [hDm]
        push_cast
        gcongr ?_ ^ 2 * ?_ ^ 2
        · nlinarith [ht'.1, hp.1]
        · nlinarith [ht'.1, hp.2]
      have hnum' : -2 * p * shearQuartic p t ≤ 2 * pb * max 0 (-shearQuartic pb t₁) := by
        have m1 : -shearQuartic p t ≤ max 0 (-shearQuartic pb t₁) :=
          (neg_le_neg hQle).trans (le_max_right _ _)
        linarith [mul_le_mul_of_nonneg_left m1 hp0.le,
          mul_le_mul_of_nonneg_right hp.2 (le_max_left 0 (-shearQuartic pb t₁))]
      rw [hD]
      push_cast
      rw [cast_shearQuarticRat]
      exact (div_le_div₀ (mul_nonneg (by linarith) (le_max_left _ _)) hnum'
        (by exact_mod_cast hDm0) hDm').trans_eq (by rw [hDm])
    · have hT := shearMap_le_self_of_shearQuartic_nonpos ht0 hQneg.le
      have hT1 : shearMap p t₁ ≤ shearMap p t := antitoneOn_shearMap_right p ht0 ht₁' ht'.2
      have hT2 : shearMap pb t₁ ≤ shearMap p t₁ :=
        antitoneOn_shearMap_left ht₁' ⟨hp0.le, hp1⟩ ⟨hpa'.trans hab', hpb'⟩ hp.2
      rw [abs_of_nonneg (by linarith)]
      push_cast
      linarith [ht'.2]
  · push_cast
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (by exact_mod_cast sqrt_le_sqrtHigh (sub_nonneg.2 hTs)) (by exact_mod_cast hD0))
      (mul_nonneg (by linarith) (by exact_mod_cast sub_nonneg.2 ht))

/-- The next node `w + ρ max(w, t₀)` of a walk in `w = 1 - p`, rounded up. -/
def shearNextLeft (ρ t₀ w : ℚ) : ℚ := roundUpRel (w + ρ * max w t₀)

/-- **The slab** `[t₀, t₁]` to the left of `p = 1`: the zero region `[0, p_a]`, the strip
`[p_a, p_b]` and the cells from `p_b` to `1`, walked in `w = 1 - p` with the ratio `ρ`. -/
def shearSlabLeft (ρ t₀ t₁ : ℚ) : Option ℤ :=
  let pa := max 0 (roundDownRel (1 - shearLowerGap t₁ * (1 + 1 / 2 ^ 12)))
  let pb := max 0 (min 1 (roundUpRel (1 - shearLowerGap t₀ * (1 - 1 / 2 ^ 12))))
  if decide (pa ≤ pb) && (decide (pa = 0) || decide (0 ≤ shearQuarticRat pa t₁)) then
    match shearStripLeft t₀ t₁ pa pb with
    | none => none
    | some v =>
      match cellWalk (shearNextLeft ρ t₀) (fun l u ↦ shearCellLeft t₀ t₁ (1 - u) (1 - l))
          100000 0 (1 - pb) 0 with
      | some n => if 0 ≤ v then some (ceilScaled 64 v + n) else none
      | none => none
  else none

/-- **Soundness of the left slab.** -/
theorem lintegral_le_shearSlabLeft {ρ t₀ t₁ : ℚ} {N : ℤ} (h : shearSlabLeft ρ t₀ t₁ = some N) :
    ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioc (0 : ℝ) 1, shearColumnDensity p t ≤
      ENNReal.ofReal (N / 2 ^ 64) := by
  unfold shearSlabLeft at h
  dsimp only at h
  split_ifs at h with hck
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hck
  obtain ⟨hab, hzero⟩ := hck
  set pa := max 0 (roundDownRel (1 - shearLowerGap t₁ * (1 + 1 / 2 ^ 12)))
  set pb := max 0 (min 1 (roundUpRel (1 - shearLowerGap t₀ * (1 - 1 / 2 ^ 12))))
  split at h
  · simp at h
  rename_i v hv
  split at h
  · rename_i n hn
    split_ifs at h with hv0
    obtain rfl := Option.some.inj h
    have ht₀' : (0 : ℝ) < t₀ := by
      unfold shearStripLeft at hv
      dsimp only at hv
      split_ifs at hv with hck'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hck'
      exact_mod_cast hck'.1.2
    have hpa' : (0 : ℝ) ≤ pa := by exact_mod_cast le_max_left _ _
    have hab' : (pa : ℝ) ≤ pb := by exact_mod_cast hab
    have hpb : pb ≤ 1 := max_le zero_le_one (min_le_left _ _)
    have hpb' : (pb : ℝ) ≤ 1 := by exact_mod_cast hpb
    -- the inner range splits; the zero region carries nothing
    have hsplit : ∀ t ∈ Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioc (0 : ℝ) 1, shearColumnDensity p t ≤
        (∫⁻ p in Ioc (pa : ℝ) pb, shearColumnDensity p t) +
          ∫⁻ p in Ioc (pb : ℝ) 1, shearColumnDensity p t := by
      intro t ht'
      have ht0 : 0 ≤ t := (ht₀'.trans ht'.1).le
      have h0 : ∫⁻ p in Ioc (0 : ℝ) pa, shearColumnDensity p t = 0 := by
        rcases hzero with hz | hz
        · simp [hz]
        · have hQa : 0 ≤ shearQuartic pa t₁ := cast_shearQuarticRat pa t₁ ▸ Rat.cast_nonneg.2 hz
          rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ ↦ 0) fun p hp ↦
            shearColumnDensity_eq_zero ht0 (hQa.trans (shearQuartic_le_of_left
              (hab'.trans hpb') hp.1.le hp.2 ht0 ht'.2))]
          simp
      calc ∫⁻ p in Ioc (0 : ℝ) 1, shearColumnDensity p t
          = ∫⁻ p in Ioc (0 : ℝ) pa ∪ (Ioc (pa : ℝ) pb ∪ Ioc (pb : ℝ) 1),
              shearColumnDensity p t := by
            rw [Ioc_union_Ioc_eq_Ioc hab' hpb', Ioc_union_Ioc_eq_Ioc hpa' (hab'.trans hpb')]
        _ ≤ (∫⁻ p in Ioc (0 : ℝ) pa, shearColumnDensity p t) +
              ((∫⁻ p in Ioc (pa : ℝ) pb, shearColumnDensity p t) +
                ∫⁻ p in Ioc (pb : ℝ) 1, shearColumnDensity p t) :=
            (lintegral_union_le _ _ _).trans (add_le_add le_rfl (lintegral_union_le _ _ _))
        _ = _ := by rw [h0, zero_add]
    -- the walk of cells in `w = 1 - p`
    have hwalk := le_of_cellWalk_of_subadditive
      (Φ := fun a b ↦ ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioc (1 - b) (1 - a),
        shearColumnDensity p t)
      (g := fun x : ℚ ↦ (x : ℝ)) (K := 64)
      (fun a ha b hb hab ↦ Rat.cast_le.2 hab)
      (fun a b c _ _ ↦ (lintegral_shearColumnDensity_le_add (Ioc (t₀ : ℝ) t₁)
        (a := 1 - c) (b := 1 - b) (c := 1 - a)).trans_eq (add_comm _ _))
      (fun a b hba ↦ by simp [Ioc_eq_empty (not_lt.2 (show 1 - a ≤ 1 - b by linarith))])
      (fun l u m hl hlu hm ↦ by exact_mod_cast lintegral_le_shearCellLeft hm) le_rfl
      (by linarith) hn
    have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast le_of_cellWalk hn
    have hv1 : (0 : ℝ) ≤ (ceilScaled 64 v : ℝ) / 2 ^ 64 :=
      (by exact_mod_cast hv0 : (0 : ℝ) ≤ v).trans (le_ceilScaled_real 64 v)
    simp only [Rat.cast_zero, sub_zero, Rat.cast_sub, Rat.cast_one, sub_sub_cancel] at hwalk
    calc ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioc (0 : ℝ) 1, shearColumnDensity p t
        ≤ ∫⁻ t in Ioc (t₀ : ℝ) t₁, ((∫⁻ p in Ioc (pa : ℝ) pb, shearColumnDensity p t) +
            ∫⁻ p in Ioc (pb : ℝ) 1, shearColumnDensity p t) :=
          setLIntegral_mono' measurableSet_Ioc hsplit
      _ = (∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioc (pa : ℝ) pb, shearColumnDensity p t) +
            ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioc (pb : ℝ) 1, shearColumnDensity p t :=
          lintegral_add_left (measurable_lintegral_shearColumnDensity _) _
      _ ≤ ENNReal.ofReal ((ceilScaled 64 v : ℝ) / 2 ^ 64) +
            ENNReal.ofReal (((n : ℝ) - ((0 : ℤ) : ℝ)) / 2 ^ 64) := by
          refine add_le_add ((lintegral_le_shearStripLeft hv).trans
            (ENNReal.ofReal_le_ofReal (le_ceilScaled_real 64 v))) ?_
          simpa using hwalk
      _ = ENNReal.ofReal (((ceilScaled 64 v + n : ℤ) : ℝ) / 2 ^ 64) := by
          rw [← ENNReal.ofReal_add hv1 (by simpa using div_nonneg hn0 (by positivity))]
          congr 1
          push_cast
          ring
  · simp at h

/-! ### Both sides of `p = 1` -/

/-- The transport cost of the slab `[t₀, t₁]` over all columns `p > 0`. -/
def shearSlabCost (ρ t₀ t₁ : ℚ) : Option ℤ :=
  match shearSlabLeft ρ t₀ t₁, shearSlabRight ρ t₀ t₁ with
  | some a, some b => if 0 ≤ a ∧ 0 ≤ b then some (a + b) else none
  | _, _ => none

/-- **Soundness of the slab over all columns.** -/
theorem lintegral_le_shearSlabCost {ρ t₀ t₁ : ℚ} {N : ℤ} (h : shearSlabCost ρ t₀ t₁ = some N) :
    ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioi (0 : ℝ), shearColumnDensity p t ≤
      ENNReal.ofReal (N / 2 ^ 64) := by
  unfold shearSlabCost at h
  split at h
  · rename_i a b ha hb
    split_ifs at h with hab
    obtain rfl := Option.some.inj h
    have hL := lintegral_le_shearSlabLeft ha
    have hR := lintegral_le_shearSlabRight hb
    have ha0 : (0 : ℝ) ≤ a / 2 ^ 64 := div_nonneg (by exact_mod_cast hab.1) (by positivity)
    have hb0 : (0 : ℝ) ≤ b / 2 ^ 64 := div_nonneg (by exact_mod_cast hab.2) (by positivity)
    calc ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioi (0 : ℝ), shearColumnDensity p t
        ≤ ∫⁻ t in Ioc (t₀ : ℝ) t₁, ((∫⁻ p in Ioc (0 : ℝ) 1, shearColumnDensity p t) +
            ∫⁻ p in Ioi (1 : ℝ), shearColumnDensity p t) := by
          refine lintegral_mono fun t ↦ ?_
          rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
          exact lintegral_union_le _ _ _
      _ = (∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioc (0 : ℝ) 1, shearColumnDensity p t) +
            ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioi (1 : ℝ), shearColumnDensity p t :=
          lintegral_add_left (measurable_lintegral_shearColumnDensity _) _
      _ ≤ ENNReal.ofReal (a / 2 ^ 64) + ENNReal.ofReal (b / 2 ^ 64) := add_le_add hL hR
      _ = ENNReal.ofReal (((a + b : ℤ) : ℝ) / 2 ^ 64) := by
          rw [← ENNReal.ofReal_add ha0 hb0]
          congr 1
          push_cast
          ring
  · simp at h

end IncompressibleFlow.SharpHolder
