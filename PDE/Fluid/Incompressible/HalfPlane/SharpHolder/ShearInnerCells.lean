/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearRowCells
public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearConstantCells

/-!
# The rational cells of the inner row cost

The cell walk of the first part of `C_in` runs over slabs `[q₀, q₁]` of rows and, in each slab,
over cells `[p₀, p₁] × [q₀, q₁]` from `p = 0` up to the threshold `h_c^-(q₁)`. On a cell the
evaluator checks that the sign quartic is `≥ 0` at the upper corner `(p₁, q₁)`, bounds
`T_y(p₀, q₀)` from above by `sqrtHigh` of the rational radicand, forms the affine majorant of
`horizontalShearMap_sub_le_affine` with the slopes `shearSlopesRow`, and returns the smaller of the
first- and second-order values (`shearRowCell`). The band between `h_c^-(q₁)` and `h_c^-(q₀)` is
a strip (`shearRowStrip`); beyond it the rows carry no transport.

## Main definitions

* `shearRowCell`: the bound of a cell `[p₀, p₁] × [q₀, q₁]` of the inner rows.
* `shearRowStrip`: the bound of the band at `h_c^-`, its area times a bound of the density.
* `shearRowSlab`: the bound of a slab of rows `[q₀, q₁]`, cells up to `h_c^-(q₁)` and the strip.
* `shearRowWalk`: the walk over slabs of rows from `q_A` to `q_B`.

## Main results

* `horizontalShearMap_le_sqrtHigh`: on `p² + 3q² ≤ 1`, `T_y(p, q) ≤ sqrtHigh R(p, q)`.
* `lintegral_le_shearRowCell`: the cell bound bounds the cost over the cell.
* `lintegral_le_shearRowStrip`: the strip value bounds the cost over the band.
* `lintegral_le_shearRowSlab`: the slab value bounds the cost over the slab.
* `lintegral_le_shearRowWalk`: for `0 ≤ q_A, q_B`, a walk value `N` bounds
  `∫_{(q_A, q_B]} ∫ shearRowDensity p q` by `N/2^64`.
* `lintegral_le_of_shearRowCheck`: a decided walk of the inner rows bounds the rows it covers;
  `lintegral_shearRowDensity_top`: the rows above `q = 0.5774` carry nothing.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory PDE.Analysis
open scoped ENNReal

namespace IncompressibleFlow.SharpHolder

/-! ### The row map over the rationals -/

/-- The radicand `R(p, q) = (1 + q²)(1 - 3q² - p²)/(1 + q² - p²)` over the rationals. -/
def shearRowRadicand (p q : ℚ) : ℚ := (1 + q ^ 2) * (1 - 3 * q ^ 2 - p ^ 2) / (1 + q ^ 2 - p ^ 2)

/-- On `p² + 3q² ≤ 1`, `T_y(p, q) ≤ sqrtHigh R(p, q)`. -/
theorem horizontalShearMap_le_sqrtHigh {p q : ℚ} (h : p ^ 2 + 3 * q ^ 2 ≤ 1) :
    horizontalShearMap p q ≤ sqrtHigh (shearRowRadicand p q) := by
  have hR : 0 ≤ shearRowRadicand p q :=
    div_nonneg (mul_nonneg (by positivity) (by linarith)) (by nlinarith [sq_nonneg q])
  have e : horizontalShearMap p q = Real.sqrt (shearRowRadicand p q : ℚ) := by
    rw [horizontalShearMap_eq_sqrt, shearRowRadicand]
    push_cast
    rfl
  rw [e]
  exact sqrt_le_sqrtHigh hR

/-! ### Cells -/

/-- The slopes `(λ, μ)` of the affine majorant of the rows. -/
def shearSlopesRow (p₀ p₁ q₀ q₁ T₁ : ℚ) : ℚ × ℚ :=
  (max 0 (roundDownRel (8 * p₀ * q₀ ^ 2 * (1 + q₀ ^ 2) / ((1 + q₀ ^ 2 - p₀ ^ 2) ^ 2 * (2 * T₁)))),
    max 0 (roundDownRel (2 * q₀ * (3 + 4 * p₀ ^ 2 * (1 - p₁ ^ 2) / (1 + q₁ ^ 2 - p₀ ^ 2) ^ 2) /
      (2 * T₁))))

/-- The slopes `(λ, μ)` of the rows satisfy `λ (1 + q₀² - p₀²)² (2 T₁) ≤ 8 p₀ q₀² (1 + q₀²)` and
`μ (2 T₁) ≤ 2 q₀ (3 + 4 p₀² (1 - p₁²)/(1 + q₁² - p₀²)²)`. -/
theorem shearSlopesRow_spec {p₀ p₁ q₀ q₁ T₁ : ℚ} (hp₀ : 0 ≤ p₀) (hp₁ : p₁ ≤ 1) (hp : p₀ ≤ p₁)
    (hq₀ : 0 < q₀) (h3 : p₀ ^ 2 + 3 * q₀ ^ 2 ≤ 1) (hT₁ : 0 < T₁) :
    ((shearSlopesRow p₀ p₁ q₀ q₁ T₁).1 : ℝ) * ((1 + q₀ ^ 2 - p₀ ^ 2) ^ 2 * (2 * T₁)) ≤
        8 * p₀ * q₀ ^ 2 * (1 + q₀ ^ 2) ∧
      ((shearSlopesRow p₀ p₁ q₀ q₁ T₁).2 : ℝ) * (2 * T₁) ≤
        2 * q₀ * (3 + 4 * p₀ ^ 2 * (1 - p₁ ^ 2) / (1 + q₁ ^ 2 - p₀ ^ 2) ^ 2) := by
  have hd : 0 < 1 + q₀ ^ 2 - p₀ ^ 2 := by nlinarith [pow_pos hq₀ 2]
  have hH₁ : 0 < (1 + q₀ ^ 2 - p₀ ^ 2) ^ 2 * (2 * T₁) := by positivity
  have hp₁1 : p₁ ^ 2 ≤ 1 := by nlinarith
  have h₁ := max_roundDownRel_div_mul_le (C := 8 * p₀ * q₀ ^ 2 * (1 + q₀ ^ 2)) (by positivity) hH₁
  have h₂ := max_roundDownRel_div_mul_le
    (C := 2 * q₀ * (3 + 4 * p₀ ^ 2 * (1 - p₁ ^ 2) / (1 + q₁ ^ 2 - p₀ ^ 2) ^ 2))
    (mul_nonneg (by linarith) (by
      have : 0 ≤ 4 * p₀ ^ 2 * (1 - p₁ ^ 2) / (1 + q₁ ^ 2 - p₀ ^ 2) ^ 2 :=
        div_nonneg (mul_nonneg (by positivity) (by linarith)) (sq_nonneg _)
      linarith)) (by linarith : (0 : ℚ) < 2 * T₁)
  simp only [shearSlopesRow]
  exact ⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩

/-- On a cell on one side of `p = 1` and for `α ≥ 0`, the corner sum of the primitives of `-α Δ`
is at most `-α shearMassLow`. -/
theorem cornerSum_le_neg_mul_shearMassLow {α : ℚ} (hα : 0 ≤ α) {p₀ p₁ t₀ t₁ : ℚ}
    (hp₀ : 0 ≤ p₀) (hp : p₀ ≤ p₁) (h1 : 0 ≤ (p₀ - 1) * (p₁ - 1)) (ht₀ : 0 < t₀) (ht : t₀ ≤ t₁) :
    cornerSum (fun p t ↦ shearCorner (-(α : ℝ) + 0) (-0) (-0) (p + 1) t -
        shearCorner (-(α : ℝ) - 0) (-0) (-0) (p - 1) t) p₀ p₁ t₀ t₁ ≤
      α * -shearMassLow p₀ p₁ t₀ t₁ := by
  have hplus := (shearAnglePair_spec (a₀ := p₀ + 1) (a₁ := p₁ + 1) ht₀ ht (by linarith)
    (mul_nonneg (by linarith) (by linarith))).1
  have hminus := (shearAnglePair_spec (a₀ := p₀ - 1) (a₁ := p₁ - 1) ht₀ ht (by linarith) h1).2
  push_cast at hplus hminus
  have e : cornerSum (fun p t ↦ shearCorner (-(α : ℝ) + 0) (-0) (-0) (p + 1) t -
        shearCorner (-(α : ℝ) - 0) (-0) (-0) (p - 1) t) p₀ p₁ t₀ t₁ =
      α * -(cornerSum (fun a t ↦ Real.arctan (a / t) / 2) ((p₀ : ℝ) + 1) (p₁ + 1) t₀ t₁ -
        cornerSum (fun a t ↦ Real.arctan (a / t) / 2) ((p₀ : ℝ) - 1) (p₁ - 1) t₀ t₁) := by
    simp only [cornerSum, shearCorner]
    ring
  rw [e]
  simp only [shearMassLow]
  push_cast
  exact mul_le_mul_of_nonneg_left (by linarith) (by exact_mod_cast hα)

/-- The first-order value of a row cell: `(c₀ + r²)/(2r)` times the mass of `-Δ`,
`c₀ = T₁ - p₀`. -/
def shearRowFirstValue (p₀ p₁ q₀ q₁ T₁ : ℚ) : ℚ :=
  (T₁ - p₀ + sqrtApproxRel (T₁ - p₀) ^ 2) / (2 * sqrtApproxRel (T₁ - p₀)) *
    -shearMassLow p₀ p₁ q₀ q₁

/-- The weight `(α, β, γ)` of the second-order value of a row cell with the slopes `λ, μ`. -/
def shearRowWeight (p₀ p₁ q₀ q₁ T₁ l m : ℚ) : ℚ × ℚ × ℚ :=
  let c₀ := T₁ - p₀
  let c₁ := 1 + l
  let r := sqrtApproxRel (max (c₀ / 4) (c₀ - c₁ * (p₁ - p₀) / 2 - m * (q₁ - q₀) / 2))
  ((c₀ + c₁ * p₀ + m * q₀ + r ^ 2) / (2 * r), -c₁ / (2 * r), -m / (2 * r))

/-- The second-order value of a row cell. -/
def shearRowSecondValue (p₀ p₁ q₀ q₁ T₁ l m : ℚ) : ℚ :=
  let w := shearRowWeight p₀ p₁ q₀ q₁ T₁ l m
  shearCellHigh (-w.1) (-w.2.1) (-w.2.2) p₀ p₁ q₀ q₁

/-- The value of a row cell: the smaller of the first- and second-order values, the latter used
when its weight is `≥ 0` at the corner `(p₁, q₁)`. -/
def shearRowValue (p₀ p₁ q₀ q₁ T₁ : ℚ) : ℚ :=
  let s := shearSlopesRow p₀ p₁ q₀ q₁ T₁
  let w := shearRowWeight p₀ p₁ q₀ q₁ T₁ s.1 s.2
  if 0 ≤ w.1 + w.2.1 * p₁ + w.2.2 * q₁ then
    min (shearRowFirstValue p₀ p₁ q₀ q₁ T₁) (shearRowSecondValue p₀ p₁ q₀ q₁ T₁ s.1 s.2)
  else shearRowFirstValue p₀ p₁ q₀ q₁ T₁

/-- **The cell bound** of `[p₀, p₁] × [q₀, q₁]` in the inner rows, after the checks. -/
def shearRowCell (q₀ q₁ p₀ p₁ : ℚ) : Option ℤ :=
  let T₁ := sqrtHigh (shearRowRadicand p₀ q₀)
  if decide (0 ≤ p₀) && decide (p₀ ≤ p₁) && decide (p₁ ≤ 1) && decide (0 < q₀) &&
      decide (q₀ ≤ q₁) && decide (p₀ ^ 2 + 3 * q₀ ^ 2 ≤ 1) &&
      decide (0 ≤ shearQuarticRat p₁ q₁) && decide (0 < T₁) && decide (p₀ ≤ T₁) then
    some (ceilScaled 64 (shearRowValue p₀ p₁ q₀ q₁ T₁))
  else none

/-- `horizontalShearMap_sub_le_affine` with the slopes `λ = μ = 0`. -/
private theorem horizontalShearMap_sub_le_of_le {p₀ p₁ q₀ q₁ T₁ : ℝ} (hp₀ : 0 ≤ p₀)
    (hp₁ : p₁ ≤ 1) (hq₀ : 0 < q₀) (hT : horizontalShearMap p₀ q₀ ≤ T₁) (hT₁ : 0 < T₁) {p q : ℝ}
    (hp : p ∈ Icc p₀ p₁) (hq : q ∈ Icc q₀ q₁) (hD : p ^ 2 + 3 * q ^ 2 ≤ 1) :
    horizontalShearMap p q - p ≤ T₁ - p₀ - (p - p₀) := by
  have h1 : 0 ≤ 1 - p₁ ^ 2 := by nlinarith [hp.1, hp.2]
  have h2 : 0 ≤ 4 * p₀ ^ 2 * (1 - p₁ ^ 2) / (1 + q₁ ^ 2 - p₀ ^ 2) ^ 2 := by positivity
  simpa using horizontalShearMap_sub_le_affine (l := 0) (m := 0) hp₀ hp₁ hq₀ hT hT₁
    (by rw [zero_mul]; positivity) (by rw [zero_mul]; positivity) hp hq hD

/-- **Soundness of a row cell.** -/
theorem lintegral_le_shearRowCell {q₀ q₁ p₀ p₁ : ℚ} {n : ℤ}
    (h : shearRowCell q₀ q₁ p₀ p₁ = some n) :
    ∫⁻ q in Ioc (q₀ : ℝ) q₁, ∫⁻ p in Ioc (p₀ : ℝ) p₁, shearRowDensity p q ≤
      ENNReal.ofReal (n / 2 ^ 64) := by
  unfold shearRowCell at h
  dsimp only at h
  split_ifs at h with hck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hp₀, hp⟩, hp₁⟩, hq₀⟩, hq⟩, h3⟩, hQ₁⟩, hT₁⟩, hpT⟩ := hck
  simp only [Option.some.injEq] at h
  subst h
  set T₁ := sqrtHigh (shearRowRadicand p₀ q₀)
  have hp₀' : (0 : ℝ) ≤ p₀ := by exact_mod_cast hp₀
  have hp' : (p₀ : ℝ) ≤ p₁ := by exact_mod_cast hp
  have hp₁' : (p₁ : ℝ) ≤ 1 := by exact_mod_cast hp₁
  have hq₀' : (0 : ℝ) < q₀ := by exact_mod_cast hq₀
  have hq' : (q₀ : ℝ) ≤ q₁ := by exact_mod_cast hq
  have hT₁' : (0 : ℝ) < T₁ := by exact_mod_cast hT₁
  have h3' : (p₀ : ℝ) ^ 2 + 3 * (q₀ : ℝ) ^ 2 ≤ 1 := by exact_mod_cast h3
  have hT : horizontalShearMap p₀ q₀ ≤ (T₁ : ℝ) := horizontalShearMap_le_sqrtHigh h3
  have hQ : ∀ p ∈ Icc (p₀ : ℝ) p₁, ∀ q ∈ Icc (q₀ : ℝ) q₁, 0 ≤ shearQuartic p q :=
    fun p hp q hq ↦ (cast_shearQuarticRat p₁ q₁ ▸ Rat.cast_nonneg.2 hQ₁).trans
      (shearQuartic_le_of_left hp₁' (hp₀'.trans hp.1) hp.2 (hq₀'.le.trans hq.1) hq.2)
  have hh1 : 0 ≤ ((p₀ : ℚ) - 1) * (p₁ - 1) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  -- the region where the bounds are used
  have hD : ∀ p ∈ Icc (p₀ : ℝ) p₁, ∀ q ∈ Icc (q₀ : ℝ) q₁, 0 < p → p < lowerShearThreshold q →
      p ^ 2 + 3 * q ^ 2 ≤ 1 := by
    intro p hp q hq hp0 hlt
    obtain ⟨-, h3q⟩ := lt_horizontalShearMap_of_mem (hq₀'.trans_le hq.1) hp0 hlt
    exact (sq_add_three_mul_sq_lt_one (hq₀'.trans_le hq.1) h3q hp0.le hlt).le
  -- the first-order value
  have hfirst : ∫⁻ q in Ioc (q₀ : ℝ) q₁, ∫⁻ p in Ioc (p₀ : ℝ) p₁, shearRowDensity p q ≤
      ENNReal.ofReal (shearRowFirstValue p₀ p₁ q₀ q₁ T₁) := by
    set r := sqrtApproxRel (T₁ - p₀)
    have hr : 0 < r := sqrtApproxRel_pos _
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    have hα : 0 ≤ (T₁ - p₀ + r ^ 2) / (2 * r) :=
      div_nonneg (add_nonneg (sub_nonneg.2 hpT) (sq_nonneg r)) (by linarith)
    have hα' : (0 : ℝ) ≤ (((T₁ - p₀ + r ^ 2) / (2 * r) : ℚ) : ℝ) := by exact_mod_cast hα
    refine (lintegral_shearRowDensity_cell_le (α := (((T₁ - p₀ + r ^ 2) / (2 * r) : ℚ) : ℝ))
      (β := 0) (γ := 0) (r := r) hp₀' hp' hq₀' hq' hr' hQ
      (fun p _ q _ ↦ by simpa using hα') (fun p hp q hq hp0 hlt ↦ ?_)).trans ?_
    · have hL := horizontalShearMap_sub_le_of_le hp₀' hp₁' hq₀' hT hT₁' hp hq
        (hD p hp q hq hp0 hlt)
      push_cast
      simp only [zero_mul, add_zero]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      linarith [hp.1]
    · exact ENNReal.ofReal_le_ofReal (by
        simpa only [shearRowFirstValue, Rat.cast_mul, Rat.cast_neg] using
          cornerSum_le_neg_mul_shearMassLow hα hp₀ hp hh1 hq₀ hq)
  -- the second-order value
  set s := shearSlopesRow p₀ p₁ q₀ q₁ T₁
  set w := shearRowWeight p₀ p₁ q₀ q₁ T₁ s.1 s.2
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal (le_ceilScaled_real 64 _))
  unfold shearRowValue
  dsimp only
  split_ifs with hw
  · have hsecond : ∫⁻ q in Ioc (q₀ : ℝ) q₁, ∫⁻ p in Ioc (p₀ : ℝ) p₁, shearRowDensity p q ≤
        ENNReal.ofReal (shearRowSecondValue p₀ p₁ q₀ q₁ T₁ s.1 s.2) := by
      obtain ⟨hl', hm'⟩ := shearSlopesRow_spec (q₁ := q₁) hp₀ hp₁ hp hq₀ h3 hT₁
      set l := s.1
      set m := s.2
      set r := sqrtApproxRel (max ((T₁ - p₀) / 4) ((T₁ - p₀) - (1 + l) * (p₁ - p₀) / 2 -
        m * (q₁ - q₀) / 2))
      have hr : 0 < r := sqrtApproxRel_pos _
      have hr' : (0 : ℝ) < r := by exact_mod_cast hr
      have hwe : w = (((T₁ - p₀) + (1 + l) * p₀ + m * q₀ + r ^ 2) / (2 * r),
          -(1 + l) / (2 * r), -m / (2 * r)) := rfl
      have hl0 : 0 ≤ l := le_max_left _ _
      have hm0 : 0 ≤ m := le_max_left _ _
      -- the weight is affine and decreasing, so `≥ 0` on the cell
      have hW0 : ∀ p ∈ Icc (p₀ : ℝ) p₁, ∀ q ∈ Icc (q₀ : ℝ) q₁,
          0 ≤ (w.1 : ℝ) + (w.2.1 : ℝ) * p + (w.2.2 : ℝ) * q := by
        intro p hp q hq
        have hw' : (0 : ℝ) ≤ (w.1 : ℝ) + (w.2.1 : ℝ) * p₁ + (w.2.2 : ℝ) * q₁ := by
          exact_mod_cast hw
        have hb : w.2.1 ≤ 0 := by
          rw [hwe]
          exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
        have hc : w.2.2 ≤ 0 := by
          rw [hwe]
          exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
        linarith [mul_le_mul_of_nonpos_left hp.2 (Rat.cast_nonpos.2 hb),
          mul_le_mul_of_nonpos_left hq.2 (Rat.cast_nonpos.2 hc)]
      refine (lintegral_shearRowDensity_cell_le (α := (w.1 : ℝ)) (β := (w.2.1 : ℝ))
        (γ := (w.2.2 : ℝ)) (r := r) hp₀' hp' hq₀' hq' hr' hQ hW0
        (fun p hp q hq hp0 hlt ↦ ?_)).trans ?_
      · have hL := horizontalShearMap_sub_le_affine hp₀' hp₁' hq₀' hT hT₁' hl' hm' hp hq
          (hD p hp q hq hp0 hlt)
        have e : (w.1 : ℝ) + (w.2.1 : ℝ) * p + (w.2.2 : ℝ) * q =
            ((T₁ - p₀) - (1 + l) * (p - p₀) - m * (q - q₀) + r ^ 2) / (2 * r) := by
          rw [hwe]
          push_cast
          field_simp
          ring
        rw [e]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        linarith
      · have h' := cornerSum_le_shearCellHigh (-w.1) (-w.2.1) (-w.2.2) hp₀ hp hh1 hq₀ hq
        simp only [Rat.cast_neg, sub_neg_eq_add, ← sub_eq_add_neg] at h'
        exact ENNReal.ofReal_le_ofReal h'
    rcases min_choice (shearRowFirstValue p₀ p₁ q₀ q₁ T₁)
      (shearRowSecondValue p₀ p₁ q₀ q₁ T₁ s.1 s.2) with hmin | hmin <;> rw [hmin]
    exacts [hfirst, hsecond]
  · exact hfirst

/-! ### The strip at `h_c^-` and the slabs of rows -/

/-- The strip value of the band `[p_a, p_b] × [q₀, q₁]` at `h_c^-`: the area times
`2 p_b max(0, Q(p_a, q₀)) / (((p_a + 1)² + q₀²)² ((1 - p_b)² + q₀²)²)` times an upper bound of
`(T_y(p_a, q₀) - p_a)^{1/2}`. -/
def shearRowStrip (q₀ q₁ pa pb : ℚ) : Option ℚ :=
  if decide (0 ≤ pa) && decide (pa ≤ pb) && decide (pb ≤ 1) && decide (0 < q₀) &&
      decide (q₀ ≤ q₁) && decide (pa ^ 2 + 3 * q₀ ^ 2 ≤ 1) then
    some ((pb - pa) * (q₁ - q₀) * (2 * pb * max 0 (shearQuarticRat pa q₀) /
      (((pa + 1) ^ 2 + q₀ ^ 2) ^ 2 * ((1 - pb) ^ 2 + q₀ ^ 2) ^ 2) *
        sqrtHigh (max 0 (sqrtHigh (shearRowRadicand pa q₀) - pa))))
  else none

/-- **Soundness of the strip of rows.** -/
theorem lintegral_le_shearRowStrip {q₀ q₁ pa pb v : ℚ} (h : shearRowStrip q₀ q₁ pa pb = some v) :
    ∫⁻ q in Ioc (q₀ : ℝ) q₁, ∫⁻ p in Ioc (pa : ℝ) pb, shearRowDensity p q ≤
      ENNReal.ofReal v := by
  unfold shearRowStrip at h
  split_ifs at h with hck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨⟨⟨hpa, hab⟩, hpb⟩, hq₀⟩, hq⟩, h3⟩ := hck
  simp only [Option.some.injEq] at h
  subst h
  set Th := sqrtHigh (shearRowRadicand pa q₀)
  have hTh := sqrtHigh_pos (show 0 ≤ shearRowRadicand pa q₀ from
    div_nonneg (mul_nonneg (by positivity) (by linarith)) (by nlinarith [sq_nonneg q₀]))
  have hpa' : (0 : ℝ) ≤ pa := by exact_mod_cast hpa
  have hab' : (pa : ℝ) ≤ pb := by exact_mod_cast hab
  have hpb' : (pb : ℝ) ≤ 1 := by exact_mod_cast hpb
  have hq₀' : (0 : ℝ) < q₀ := by exact_mod_cast hq₀
  have hTh' : (0 : ℝ) < Th := by exact_mod_cast hTh
  have hT : horizontalShearMap pa q₀ ≤ (Th : ℝ) := horizontalShearMap_le_sqrtHigh h3
  have hP₁ : 0 < (pa + 1) ^ 2 + q₀ ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hq₀ 2)
  have hP₂ : 0 < (1 - pb) ^ 2 + q₀ ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hq₀ 2)
  set Dm : ℚ := ((pa + 1) ^ 2 + q₀ ^ 2) ^ 2 * ((1 - pb) ^ 2 + q₀ ^ 2) ^ 2 with hDm
  have hDm0 : 0 < Dm := by positivity
  set D : ℚ := 2 * pb * max 0 (shearQuarticRat pa q₀) / Dm with hD
  have hD0 : 0 ≤ D := div_nonneg (mul_nonneg (by linarith) (le_max_left _ _)) hDm0.le
  refine (lintegral_shearRowDensity_strip_le (D := D)
    (φ := ((max 0 (Th - pa) : ℚ) : ℝ)) hab' (by exact_mod_cast hD0)
    (fun p hp q hq' hp0 hlt ↦ ?_)).trans (ENNReal.ofReal_le_ofReal ?_)
  · have hq0 : 0 < q := hq₀'.trans hq'.1
    have hp1 : p ≤ 1 := hp.2.trans hpb'
    have hΔ := shearDifference_nonpos_of_lt_lowerShearThreshold hq0 hp0.le hlt
    have h₁ : (p + 1) ^ 2 + q ^ 2 ≠ 0 := by positivity
    have h₂ : (p - 1) ^ 2 + q ^ 2 ≠ 0 := by positivity
    have hden : 0 < ((p + 1) ^ 2 + q ^ 2) ^ 2 * ((p - 1) ^ 2 + q ^ 2) ^ 2 := by positivity
    have hQle : shearQuartic p q ≤ shearQuartic pa q₀ :=
      shearQuartic_le_of_left hp1 hpa' hp.1.le hq₀'.le hq'.1.le
    constructor
    · have hneg : -shearDifference p q =
          2 * p * shearQuartic p q / (((p + 1) ^ 2 + q ^ 2) ^ 2 * ((p - 1) ^ 2 + q ^ 2) ^ 2) := by
        rw [shearDifference_eq h₁ h₂]
        ring
      rw [abs_of_nonpos hΔ, hneg]
      have hDm' : (Dm : ℝ) ≤ ((p + 1) ^ 2 + q ^ 2) ^ 2 * ((p - 1) ^ 2 + q ^ 2) ^ 2 := by
        rw [hDm]
        push_cast
        gcongr ?_ ^ 2 * ?_ ^ 2
        · nlinarith [hq'.1, hp.1]
        · nlinarith [hq'.1, hp.2]
      have hnum : 2 * p * shearQuartic p q ≤ 2 * pb * max 0 (shearQuartic pa q₀) := by
        linarith [mul_le_mul_of_nonneg_left (hQle.trans (le_max_right 0 _)) hp0.le,
          mul_le_mul_of_nonneg_right hp.2 (le_max_left 0 (shearQuartic pa q₀))]
      have hDm'0 : (0 : ℝ) < Dm := by exact_mod_cast hDm0
      rw [hD]
      push_cast
      rw [cast_shearQuarticRat]
      calc 2 * p * shearQuartic p q / (((p + 1) ^ 2 + q ^ 2) ^ 2 * ((p - 1) ^ 2 + q ^ 2) ^ 2)
          ≤ 2 * pb * max 0 (shearQuartic pa q₀) /
              (((p + 1) ^ 2 + q ^ 2) ^ 2 * ((p - 1) ^ 2 + q ^ 2) ^ 2) :=
            div_le_div_of_nonneg_right hnum hden.le
        _ ≤ 2 * pb * max 0 (shearQuartic pa q₀) / Dm :=
            div_le_div_of_nonneg_left (mul_nonneg (by linarith) (le_max_left _ _)) hDm'0 hDm'
        _ = _ := by rw [hDm]
    · obtain ⟨hT', h3q⟩ := lt_horizontalShearMap_of_mem hq0 hp0 hlt
      have hL := horizontalShearMap_sub_le_of_le (q₁ := q) hpa' hp1 hq₀' hT hTh'
        ⟨hp.1.le, le_rfl⟩ ⟨hq'.1.le, le_rfl⟩ (sq_add_three_mul_sq_lt_one hq0 h3q hp0.le hlt).le
      rw [abs_of_neg (by linarith), neg_sub]
      push_cast
      have : (0 : ℝ) ≤ p - pa := by linarith [hp.1]
      calc horizontalShearMap p q - p ≤ (Th : ℝ) - pa := by linarith
        _ ≤ max 0 ((Th : ℝ) - pa) := le_max_right _ _
  · have hφ : (0 : ℚ) ≤ max 0 (Th - pa) := le_max_left _ _
    have hs := sqrt_le_sqrtHigh hφ
    have hA : (0 : ℝ) ≤ ((pb : ℝ) - pa) * ((q₁ : ℝ) - q₀) :=
      mul_nonneg (by linarith) (by exact_mod_cast sub_nonneg.2 hq)
    push_cast
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by exact_mod_cast hD0)) hA
    exact_mod_cast hs

/-- **The slab of rows** `[q₀, q₁]`: the cells from `p = 0` to `p_a ≈ h_c^-(q₁)`, with the ratio
`ρ`, and the strip from `p_a` to `p_b ≈ h_c^-(q₀)`. -/
def shearRowSlab (ρ q₀ q₁ : ℚ) : Option ℤ :=
  let pa := max 0 (roundDownRel (1 - shearLowerGap q₁ * (1 + 1 / 2 ^ 12)))
  let pb := min 1 (roundUpRel (1 - shearLowerGap q₀ * (1 - 1 / 2 ^ 12)))
  if decide (0 < q₀) && decide (q₀ ≤ q₁) && decide (pa ≤ pb) &&
      decide (shearQuarticRat pb q₀ ≤ 0) then
    match shearRowStrip q₀ q₁ pa pb with
    | none => none
    | some v =>
      match cellWalk (shearNextRow ρ) (shearRowCell q₀ q₁) 100000 0 pa 0 with
      | some n => if 0 ≤ v then some (ceilScaled 64 v + n) else none
      | none => none
  else none

/-- For a set `S`, `q ↦ ∫⁻ p in S, shearRowDensity p q` is measurable. -/
theorem measurable_lintegral_shearRowDensity (S : Set ℝ) :
    Measurable fun q ↦ ∫⁻ p in S, shearRowDensity p q :=
  (measurable_shearRowDensity.comp measurable_swap).lintegral_prod_right'

/-- The iterated integral of the row density over `(a, c]` in `p` is at most the sum of those over
`(a, b]` and `(b, c]`. -/
theorem lintegral_shearRowDensity_le_add (Z : Set ℝ) {a b c : ℝ} :
    ∫⁻ q in Z, ∫⁻ p in Ioc a c, shearRowDensity p q ≤
      (∫⁻ q in Z, ∫⁻ p in Ioc a b, shearRowDensity p q) +
        ∫⁻ q in Z, ∫⁻ p in Ioc b c, shearRowDensity p q := by
  rw [← lintegral_add_left (measurable_lintegral_shearRowDensity _)]
  exact lintegral_mono fun q ↦
    (lintegral_mono_set Ioc_subset_Ioc_union_Ioc).trans (lintegral_union_le _ _ _)

/-- **Soundness of the slab of rows.** -/
theorem lintegral_le_shearRowSlab {ρ q₀ q₁ : ℚ} {N : ℤ} (h : shearRowSlab ρ q₀ q₁ = some N) :
    ∫⁻ q in Ioc (q₀ : ℝ) q₁, ∫⁻ p, shearRowDensity p q ≤ ENNReal.ofReal (N / 2 ^ 64) := by
  unfold shearRowSlab at h
  dsimp only at h
  split_ifs at h with hck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨hq₀, hq⟩, hab⟩, hQb⟩ := hck
  set pa := max 0 (roundDownRel (1 - shearLowerGap q₁ * (1 + 1 / 2 ^ 12)))
  set pb := min 1 (roundUpRel (1 - shearLowerGap q₀ * (1 - 1 / 2 ^ 12)))
  split at h
  · simp at h
  rename_i v hv
  split at h
  · rename_i n hn
    split_ifs at h with hv0
    simp only [Option.some.injEq] at h
    subst h
    have hpa : 0 ≤ pa := le_max_left _ _
    have hq₀' : (0 : ℝ) < q₀ := by exact_mod_cast hq₀
    have hpb0 : (0 : ℝ) ≤ pb := by exact_mod_cast hpa.trans hab
    have hpa' : (0 : ℝ) ≤ pa := by exact_mod_cast hpa
    have hab' : (pa : ℝ) ≤ pb := by exact_mod_cast hab
    have hQb' : shearQuartic pb q₀ ≤ 0 := by
      rw [← cast_shearQuarticRat]
      exact_mod_cast hQb
    have hsplit : ∀ q ∈ Ioc (q₀ : ℝ) q₁, ∫⁻ p, shearRowDensity p q ≤
        (∫⁻ p in Ioc (0 : ℝ) pa, shearRowDensity p q) +
          ∫⁻ p in Ioc (pa : ℝ) pb, shearRowDensity p q := by
      intro q hq'
      have hq0 : 0 < q := hq₀'.trans hq'.1
      have hlow : lowerShearThreshold q ≤ pb := by
        rcases le_or_gt (3 * q ^ 2) 1 with h3 | h3
        · exact lowerShearThreshold_le_of_shearQuartic_nonpos hq0.le h3 hpb0
            ((shearQuartic_le_of_le hq₀'.le hq'.1.le).trans hQb')
        · rw [lowerShearThreshold_eq_zero hq0.le h3.le]
          exact hpb0
      have hsub : (univ : Set ℝ) = Iic 0 ∪ (Ioc (0 : ℝ) pa ∪ (Ioc (pa : ℝ) pb ∪ Ioi (pb : ℝ))) := by
        rw [Ioc_union_Ioi_eq_Ioi hab', Ioc_union_Ioi_eq_Ioi hpa', Iic_union_Ioi]
      have h0 : ∫⁻ p in Iic 0, shearRowDensity p q = 0 :=
        (setLIntegral_congr_fun measurableSet_Iic (g := fun _ ↦ 0) fun p hp ↦
          indicator_of_notMem (fun hs ↦ absurd hs.1 (not_lt.2 hp)) _).trans lintegral_zero
      have h0' : ∫⁻ p in Ioi (pb : ℝ), shearRowDensity p q = 0 :=
        (setLIntegral_congr_fun measurableSet_Ioi (g := fun _ ↦ 0) fun p hp ↦
          shearRowDensity_eq_zero_of_le (hlow.trans hp.le)).trans lintegral_zero
      calc ∫⁻ p, shearRowDensity p q
          = ∫⁻ p in Iic 0 ∪ (Ioc (0 : ℝ) pa ∪ (Ioc (pa : ℝ) pb ∪ Ioi (pb : ℝ))),
              shearRowDensity p q := by rw [← hsub, Measure.restrict_univ]
        _ ≤ (∫⁻ p in Iic 0, shearRowDensity p q) + ((∫⁻ p in Ioc (0 : ℝ) pa,
              shearRowDensity p q) + ((∫⁻ p in Ioc (pa : ℝ) pb, shearRowDensity p q) +
                ∫⁻ p in Ioi (pb : ℝ), shearRowDensity p q)) :=
            (lintegral_union_le _ _ _).trans (add_le_add le_rfl
              ((lintegral_union_le _ _ _).trans (add_le_add le_rfl (lintegral_union_le _ _ _))))
        _ = _ := by rw [h0, h0', zero_add, add_zero]
    have hwalk := le_of_cellWalk_of_subadditive
      (Φ := fun a b ↦ ∫⁻ q in Ioc (q₀ : ℝ) q₁, ∫⁻ p in Ioc a b, shearRowDensity p q)
      (g := fun x : ℚ ↦ (x : ℝ)) (K := 64)
      (fun a ha b hb hab ↦ by simp only; exact_mod_cast hab)
      (fun _ _ _ _ _ ↦ lintegral_shearRowDensity_le_add _)
      (fun a b hba ↦ by simp [Ioc_eq_empty (not_lt.2 hba)])
      (fun l u m hl hlu hm ↦ lintegral_le_shearRowCell hm) le_rfl hpa hn
    have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast le_of_cellWalk hn
    have hv1 : (0 : ℝ) ≤ (ceilScaled 64 v : ℝ) / 2 ^ 64 :=
      (by exact_mod_cast hv0 : (0 : ℝ) ≤ v).trans (le_ceilScaled_real 64 v)
    calc ∫⁻ q in Ioc (q₀ : ℝ) q₁, ∫⁻ p, shearRowDensity p q
        ≤ ∫⁻ q in Ioc (q₀ : ℝ) q₁, ((∫⁻ p in Ioc (0 : ℝ) pa, shearRowDensity p q) +
            ∫⁻ p in Ioc (pa : ℝ) pb, shearRowDensity p q) :=
          setLIntegral_mono' measurableSet_Ioc hsplit
      _ = (∫⁻ q in Ioc (q₀ : ℝ) q₁, ∫⁻ p in Ioc (0 : ℝ) pa, shearRowDensity p q) +
            ∫⁻ q in Ioc (q₀ : ℝ) q₁, ∫⁻ p in Ioc (pa : ℝ) pb, shearRowDensity p q :=
          lintegral_add_left (measurable_lintegral_shearRowDensity _) _
      _ ≤ ENNReal.ofReal (((n : ℝ) - ((0 : ℤ) : ℝ)) / 2 ^ 64) +
            ENNReal.ofReal ((ceilScaled 64 v : ℝ) / 2 ^ 64) := by
          refine add_le_add (by simpa using hwalk) ?_
          exact (lintegral_le_shearRowStrip hv).trans
            (ENNReal.ofReal_le_ofReal (le_ceilScaled_real 64 v))
      _ = ENNReal.ofReal (((ceilScaled 64 v + n : ℤ) : ℝ) / 2 ^ 64) := by
          rw [← ENNReal.ofReal_add (by simpa using div_nonneg hn0 (by positivity)) hv1]
          congr 1
          push_cast
          ring
  · simp at h

/-- **The walk over slabs of rows** from `q_A` to `q_B`, with the ratios `ρ` in `p` and `ρ_q`
in `q`. -/
def shearRowWalk (ρ ρq qA qB : ℚ) : Option ℤ :=
  cellWalk (shearNextHeight ρq) (shearRowSlab ρ) 100000 qA qB 0

/-- **Soundness of the walk over slabs of rows**: for `0 ≤ q_A, q_B`, a walk value `N` bounds
`∫_{(q_A, q_B]} ∫ shearRowDensity p q` by `N/2^64`. -/
theorem lintegral_le_shearRowWalk {ρ ρq qA qB : ℚ} {N : ℤ} (hA : 0 ≤ qA) (hB : 0 ≤ qB)
    (h : shearRowWalk ρ ρq qA qB = some N) :
    ∫⁻ q in Ioc (qA : ℝ) qB, ∫⁻ p, shearRowDensity p q ≤ ENNReal.ofReal (N / 2 ^ 64) := by
  have := lintegral_le_of_cellWalk (F := fun q ↦ ∫⁻ p, shearRowDensity p q)
    (g := fun x : ℚ ↦ (x : ℝ)) (K := 64)
    (fun a ha b hb hab ↦ by simp only; exact_mod_cast hab)
    (fun l u m hl hlu hm ↦ lintegral_le_shearRowSlab hm) hA hB h
  simpa using this

/-- A decided walk over slabs of rows bounds the rows it covers. -/
theorem lintegral_le_of_shearRowCheck {ρ ρq qA qB b : ℚ} (hA : 0 ≤ qA) (hB : 0 ≤ qB)
    (h : walkLe (shearRowWalk ρ ρq qA qB) b = true) :
    ∫⁻ q in Ioc (qA : ℝ) qB, ∫⁻ p, shearRowDensity p q ≤ ENNReal.ofReal b := by
  obtain ⟨n, hn, hle⟩ := walkLe_spec h
  exact (lintegral_le_shearRowWalk hA hB hn).trans (ENNReal.ofReal_le_ofReal hle)

/-- A row with `3q² ≥ 1` carries nothing. -/
theorem lintegral_eq_zero_of_shearRowDensity {q : ℝ} (hq : 0 ≤ q) (h3 : 1 ≤ 3 * q ^ 2) :
    ∫⁻ p, shearRowDensity p q = 0 := by
  have h0 := lowerShearThreshold_eq_zero hq h3
  have hpt : ∀ p, shearRowDensity p q = 0 := fun p ↦ by
    unfold shearRowDensity
    rw [h0, Ioo_self, indicator_empty]
  simp only [hpt, lintegral_zero]

/-- Above `q = 0.5774` the inner region is empty. -/
theorem lintegral_shearRowDensity_top :
    ∫⁻ q in Ioi (5774 / 10 ^ 4 : ℝ), ∫⁻ p, shearRowDensity p q = 0 := by
  refine (setLIntegral_congr_fun measurableSet_Ioi (g := fun _ ↦ 0) fun q hq ↦ ?_).trans
    (by simp)
  have hq0 : (0 : ℝ) ≤ q := le_trans (by norm_num) (le_of_lt hq)
  have h3 : 1 ≤ 3 * q ^ 2 := by
    have : (5774 / 10 ^ 4 : ℝ) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (by norm_num) (le_of_lt hq) 2
    nlinarith
  have h0 := lintegral_eq_zero_of_shearRowDensity hq0 h3
  exact h0

end IncompressibleFlow.SharpHolder
