/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.StrainCostTails
public import PDE.Analysis.SpecialFunctions.Trigonometric.ArctanEnclosure
public import PDE.Analysis.SpecialFunctions.Log.RationalBounds

/-!
# The rational cells of the transport cost of `C₁(b)`

The cell walk for the integral `∫ M(s₂) ds₂` of `strainConstant` runs over slabs `[z₀, z₁]` in
`s₂` and, in each slab, over cells `[x, x'] × [z₀, z₁]` in `s₁` to the right of the sign
threshold. On a cell it

* certifies `T₀ ≤ T(x', z₀)` and `T(x, z₁) ≤ T₁` by the sign of the cubic (`strainCubicRat`) at
  candidates from Newton's method in rationals (`strainMapLow`, `strainMapHigh`);
* forms the affine majorant `s₁ - T ≤ (x' - T₀) - (1 + λ₁)(x' - s₁) - λ₂ (s₂ - z₀)` from the
  divided differences of `T`;
* bounds the corner sum of `cornerSum_strainCell_eq` by rational enclosures: the masses through the
  cross ratios and `2e/(2 + e) ≤ log (1 + e) ≤ e (2 + e)/(2 (1 + e))`, the moments through
  arctangents of the differences of the arguments (`atanPair`);
* and returns the smaller of this second-order bound and the first-order bound
  `(x' - T₀ + r²)/(2r)` times the mass (`strainCellBound`).

## Main definitions

* `strainMapLow`, `strainMapHigh`: rational candidate bounds of the threshold map `T(s₁, s₂)`
  from Newton's method.
* `strainCellBound`: the bound of one cell `[x, x'] × [z₀, z₁]`.
* `strainSlab`: the check of one slab `[z₀, z₁] × (-∞, 2^30]`, an integer bound on the grid
  `2^-64`.
* `strainBottomSlab`: the check of the bottom slab `[1/2 + 2^-31, 2^30] × (0, 2^-17]`.
* `strainSlabWalk`: the walk over slabs from `z_A` to `z_B`.

## Main results

* `le_strainMap_of_lowOk`, `strainMap_le_of_highOk`: candidates passing the cubic sign checks are
  lower and upper bounds of `T(s₁, s₂)`.
* `lintegral_le_strainCellBound`: the cell bound bounds the cost integral over the cell.
* `lintegral_le_strainSlab`: the slab check bounds the cost over the slab.
* `lintegral_le_strainBottomSlab`: a value `N` of the bottom check bounds the cost over
  `(0, 2^-17] × (1/2 + 2^-31, 2^30]` by `N/2^64`.
* `lintegral_le_strainSlabWalk`: for `0 ≤ z_A, z_B`, a walk value `N` bounds the cost over
  `(z_A, z_B] × (-∞, 2^30]` by `N/2^64`.
* `lintegral_bottom_le`: the bottom slab of the strain cost with its corner strip.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory PDE.Analysis
open scoped ENNReal

namespace IncompressibleFlow.SharpHolder

/-! ### Rational evaluations and their meaning -/

/-- `16 s₁ strainCubic s₁ s₂ t` over the rationals. -/
def strainCubicRat (s₁ s₂ t : ℚ) : ℚ :=
  16 * s₁ * t ^ 3 + 16 * s₁ ^ 2 * t ^ 2 + 16 * s₁ * t * (s₁ ^ 2 - 1 / 2 + 2 * s₂ ^ 2) -
    (4 * s₂ ^ 2 + 1) ^ 2

/-- For `s₁ ≠ 0`, `strainCubicRat s₁ s₂ t` is `16 s₁ strainCubic s₁ s₂ t` over the reals. -/
theorem cast_strainCubicRat {s₁ : ℚ} (h : s₁ ≠ 0) (s₂ t : ℚ) :
    ((strainCubicRat s₁ s₂ t : ℚ) : ℝ) = 16 * s₁ * strainCubic s₁ s₂ t := by
  have h' : (s₁ : ℝ) ≠ 0 := by exact_mod_cast h
  simp only [strainCubicRat, strainCubic]
  push_cast
  field_simp

/-- The derivative in `t` of `strainCubicRat`. -/
def strainCubicRatDeriv (s₁ s₂ t : ℚ) : ℚ :=
  48 * s₁ * t ^ 2 + 32 * s₁ ^ 2 * t + 16 * s₁ * (s₁ ^ 2 - 1 / 2 + 2 * s₂ ^ 2)

/-- Rounding down to the grid `2^-32`. -/
def floor32 (q : ℚ) : ℚ := (⌊q * 2 ^ 32⌋ : ℚ) / 2 ^ 32

/-- Rounding down to the grid `2^-32` does not increase a rational: `floor32 q ≤ q`. -/
theorem floor32_le (q : ℚ) : floor32 q ≤ q := by
  rw [floor32, div_le_iff₀ (by positivity)]
  exact Int.floor_le _

/-- Newton's method for the root of the cubic, from above, on the grid `2^-64`. -/
def strainNewton (s₁ s₂ : ℚ) : ℕ → ℚ → ℚ
  | 0, t => t
  | n + 1, t =>
    let d := strainCubicRatDeriv s₁ s₂ t
    if 0 < d then
      let t' := roundUp64 (t - strainCubicRat s₁ s₂ t / d)
      if t - t' ≤ t / 2 ^ 50 + 1 / 2 ^ 63 then t' else strainNewton s₁ s₂ n t'
    else t

/-- A starting point above the root: `min((4 s₂² + 1)/(4 s₁), T̂)` with
`T̂ = (4 s₂² + 1)² / (16 s₁ (s₁² - 1/2 + 2 s₂²))` when the denominator is positive. -/
def strainMapStart (s₁ s₂ : ℚ) : ℚ :=
  let a := (4 * s₂ ^ 2 + 1) / (4 * s₁)
  let L := s₁ ^ 2 - 1 / 2 + 2 * s₂ ^ 2
  if 0 < L then min a ((4 * s₂ ^ 2 + 1) ^ 2 / (16 * s₁ * L)) else a

/-- The Newton approximation of `T(s₁, s₂)`, started at `min(c, strainMapStart)`. -/
def strainMapApprox (s₁ s₂ c : ℚ) : ℚ :=
  strainNewton s₁ s₂ 30 (roundUp64 (min c (strainMapStart s₁ s₂)))

/-- The candidate lower bound of `T(s₁, s₂)`. -/
def strainMapLow (s₁ s₂ c : ℚ) : ℚ :=
  let t := strainMapApprox s₁ s₂ c
  max 0 (t - t / 2 ^ 40 - 1 / 2 ^ 62)

/-- The candidate upper bound of `T(s₁, s₂)`. -/
def strainMapHigh (s₁ s₂ c : ℚ) : ℚ :=
  let t := strainMapApprox s₁ s₂ c
  t + t / 2 ^ 40 + 1 / 2 ^ 62

/-- The check of a lower bound `t` of `T(s₁, s₂)`. -/
def strainLowOk (s₁ s₂ t : ℚ) : Bool :=
  decide (t = 0) || decide (strainCubicRat s₁ s₂ t ≤ 0)

/-- The check of a lower bound `t` of `T(s₁, s₂)` for every `s₂ ≠ 0`, on the axis. -/
def strainAxisOk (s₁ t : ℚ) : Bool :=
  decide (t = 0) || (decide (strainCubicRat s₁ 0 t ≤ 0) && decide (t ≤ 1 / (4 * s₁)))

/-- The check of an upper bound `t` of `T(s₁, s₂)`. -/
def strainHighOk (s₁ s₂ t : ℚ) : Bool :=
  decide (0 ≤ t) && decide (0 < strainCubicRat s₁ s₂ t)

/-- For `s₁ > 0` and `s₂ ≠ 0`, a candidate `t` that passes `strainLowOk` satisfies
`t ≤ T(s₁, s₂)`. -/
theorem le_strainMap_of_lowOk {s₁ s₂ t : ℚ} (h₁ : 0 < s₁) (h₂ : (s₂ : ℝ) ≠ 0)
    (h : strainLowOk s₁ s₂ t = true) : (t : ℝ) ≤ strainMap s₁ s₂ := by
  have h₁' : (0 : ℝ) < s₁ := by exact_mod_cast h₁
  simp only [strainLowOk, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · rw [h]
    push_cast
    exact (strainMap_pos h₁' h₂).le
  · refine le_strainMap_of_strainCubic_nonpos h₁' h₂ ?_
    have h' : ((strainCubicRat s₁ s₂ t : ℚ) : ℝ) ≤ 0 := by exact_mod_cast h
    rw [cast_strainCubicRat h₁.ne'] at h'
    have : (0 : ℝ) < 16 * s₁ := by positivity
    by_contra hc
    push Not at hc
    have := mul_pos this hc
    linarith

/-- For `s₁ > 0`, a candidate `t` that passes `strainAxisOk` satisfies `t ≤ T(s₁, s₂)` for every
`s₂`. -/
theorem le_strainMap_of_axisOk {s₁ t : ℚ} {s₂ : ℝ} (h₁ : 0 < s₁)
    (h : strainAxisOk s₁ t = true) : (t : ℝ) ≤ strainMap s₁ s₂ := by
  have h₁' : (0 : ℝ) < s₁ := by exact_mod_cast h₁
  refine le_strainMap_of_forall_ne_zero h₁' (fun s₂ h₂ ↦ ?_) s₂
  simp only [strainAxisOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨hc, ht⟩
  · rw [h]
    push_cast
    exact (strainMap_pos h₁' h₂).le
  · refine le_strainMap_of_axis h₁' ?_ ?_
    · have : ((t : ℚ) : ℝ) ≤ ((1 / (4 * s₁) : ℚ) : ℝ) := by exact_mod_cast ht
      simpa using this
    · have h' : ((strainCubicRat s₁ 0 t : ℚ) : ℝ) ≤ 0 := by exact_mod_cast hc
      rw [cast_strainCubicRat h₁.ne'] at h'
      push_cast at h'
      have : (0 : ℝ) < 16 * s₁ := by positivity
      by_contra hc'
      push Not at hc'
      have := mul_pos this hc'
      linarith

/-- For `s₁ > 0` and `s₂ ≠ 0`, a candidate `t` that passes `strainHighOk` satisfies
`T(s₁, s₂) ≤ t`. -/
theorem strainMap_le_of_highOk {s₁ s₂ t : ℚ} (h₁ : 0 < s₁) (h₂ : (s₂ : ℝ) ≠ 0)
    (h : strainHighOk s₁ s₂ t = true) : strainMap s₁ s₂ ≤ (t : ℝ) := by
  have h₁' : (0 : ℝ) < s₁ := by exact_mod_cast h₁
  simp only [strainHighOk, Bool.and_eq_true, decide_eq_true_eq] at h
  refine (strainMap_lt_of_strainCubic_pos h₁' h₂ (by exact_mod_cast h.1) ?_).le
  have h' : (0 : ℝ) < ((strainCubicRat s₁ s₂ t : ℚ) : ℝ) := by exact_mod_cast h.2
  rw [cast_strainCubicRat h₁.ne'] at h'
  exact pos_of_mul_pos_right h' (by positivity)

/-- The mass bound `e (2 + e) / (8 (1 + e))` from `e ≥ ρ - 1`. -/
def massHi (e : ℚ) : ℚ := e * (2 + e) / (8 * (1 + e))

/-- The mass bound `e / (2 (2 + e))` from `e ≤ ρ - 1`. -/
def massLo (e : ℚ) : ℚ := e / (2 * (2 + e))

/-- For `1 ≤ ρ ≤ 1 + e`, `(log ρ)/4 ≤ e (2 + e)/(8 (1 + e))`. -/
theorem log_div_four_le_massHi {ρ : ℝ} {e : ℚ} (hρ : 1 ≤ ρ) (he : ρ - 1 ≤ e) :
    Real.log ρ / 4 ≤ massHi e := by
  have h := Real.log_le_half_sub_inv hρ
  have he0 : (0 : ℝ) ≤ e := by linarith
  have hρ0 : 0 < ρ := by linarith
  simp only [massHi]
  push_cast
  have key : (ρ - ρ⁻¹) / 2 / 4 ≤ (e : ℝ) * (2 + e) / (8 * (1 + e)) := by
    rw [div_div, div_le_div_iff₀ (by norm_num) (by positivity)]
    have this : ρ - ρ⁻¹ ≤ ((1 + (e : ℝ)) - (1 + (e : ℝ))⁻¹) := by
      have h1 : ρ ≤ 1 + e := by linarith
      have h2 : (1 + (e : ℝ))⁻¹ ≤ ρ⁻¹ := inv_anti₀ hρ0 h1
      linarith
    have e2 : ((1 + (e : ℝ)) - (1 + (e : ℝ))⁻¹) * (8 * (1 + e)) = 8 * (e * (2 + e)) := by
      field_simp
      ring
    have := mul_le_mul_of_nonneg_right this (by positivity : (0:ℝ) ≤ 8 * (1 + e))
    linarith
  linarith

/-- For `0 ≤ e ≤ ρ - 1`, `e/(2 (2 + e)) ≤ (log ρ)/4`. -/
theorem massLo_le_log_div_four {ρ : ℝ} {e : ℚ} (he0 : 0 ≤ e) (he : e ≤ ρ - 1) :
    (massLo e : ℝ) ≤ Real.log ρ / 4 := by
  have hρ : 1 ≤ ρ := by have : (0 : ℝ) ≤ e := by exact_mod_cast he0
                        linarith
  have h := Real.two_mul_sub_div_add_le_log hρ
  have he0' : (0 : ℝ) ≤ e := by exact_mod_cast he0
  simp only [massLo]
  push_cast
  have : (e : ℝ) / (2 * (2 + e)) ≤ 2 * (ρ - 1) / (ρ + 1) / 4 := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by nlinarith)]
    nlinarith
  linarith

/-! ### Rational forms of the cell quantities -/

/-- The cross ratio over the rationals. -/
def strainCrossRat (u₀ u₁ z₀ z₁ : ℚ) : ℚ :=
  (u₀ ^ 2 + z₁ ^ 2) * (u₁ ^ 2 + z₀ ^ 2) / ((u₁ ^ 2 + z₁ ^ 2) * (u₀ ^ 2 + z₀ ^ 2))

/-- `strainCrossRat` is the cross ratio `strainCross` over the reals. -/
theorem cast_strainCrossRat (u₀ u₁ z₀ z₁ : ℚ) :
    ((strainCrossRat u₀ u₁ z₀ z₁ : ℚ) : ℝ) = strainCross u₀ u₁ z₀ z₁ := by
  simp only [strainCrossRat, strainCross]
  push_cast
  ring

/-- The argument `z / (z² + u (u + 1))` of the unit shifts. -/
def strainQ (u z : ℚ) : ℚ := z / (z ^ 2 + u * (u + 1))

/-- The argument `(a - b)/(1 + a b)` of a difference of arctangents. -/
def atanDiff (a b : ℚ) : ℚ := (a - b) / (1 + a * b)

/-- The argument `u (z₁ - z₀)/(u² + z₀ z₁)` of `arctan (z₁/u) - arctan (z₀/u)`. -/
def strainG (u z₀ z₁ : ℚ) : ℚ := u * (z₁ - z₀) / (u ^ 2 + z₀ * z₁)

/-- For `c > 0` and `t₀, t₁ ≥ 0`, `arctan (t₁/c) - arctan (t₀/c)` is the arctangent of
`c (t₁ - t₀)/(c² + t₀ t₁)`, the real form of `strainG c t₀ t₁`. -/
theorem arctan_sub_arctan_div {c t₀ t₁ : ℝ} (hc : 0 < c) (ht₀ : 0 ≤ t₀) (ht₁ : 0 ≤ t₁) :
    Real.arctan (t₁ / c) - Real.arctan (t₀ / c) =
      Real.arctan (c * (t₁ - t₀) / (c ^ 2 + t₀ * t₁)) := by
  rw [arctan_sub_arctan (by positivity)]
  congr 1
  have h1 : c ^ 2 + t₀ * t₁ ≠ 0 := by positivity
  have h2 := hc.ne'
  field_simp

/-- The second unit shift through the first: `σ₂(u, z) = arctan (z/u)/2 - ((u + 1)/2) arctan q`. -/
theorem strainShift₂_eq {u z : ℝ} (hu : 0 < u) (hz : 0 < z) :
    strainShift₂ u z = Real.arctan (z / u) / 2 -
      (u + 1) / 2 * Real.arctan (z / (z ^ 2 + u * (u + 1))) := by
  have h := arctan_sub_arctan (a := z / u) (b := z / (u + 1)) (by positivity)
  have e : (z / u - z / (u + 1)) / (1 + z / u * (z / (u + 1))) = z / (z ^ 2 + u * (u + 1)) := by
    field_simp
    ring
  rw [e] at h
  unfold strainShift₂
  linear_combination (-(u + 1) / 2) * h

/-- The first moment shifts as one arctangent per height. -/
theorem cornerSum_strainShift₁_eq {x x' z₀ z₁ : ℚ} (hx : 1 / 2 < x) (hx' : x ≤ x')
    (hz₀ : 0 < z₀) (hz : z₀ ≤ z₁) :
    cornerSum (fun s₁ z ↦ strainShift₁ (s₁ - 1 / 2) z) x x' z₀ z₁ =
      (z₁ : ℝ) / 2 * Real.arctan (atanDiff (strainQ (x' - 1 / 2) z₁) (strainQ (x - 1 / 2) z₁)) -
        (z₀ : ℝ) / 2 * Real.arctan (atanDiff (strainQ (x' - 1 / 2) z₀)
          (strainQ (x - 1 / 2) z₀)) := by
  have hu₀ : (0 : ℝ) < x - 1 / 2 := by
    have h := (Rat.cast_lt (K := ℝ)).2 hx
    push_cast at h
    linarith
  have hu₁ : (0 : ℝ) < x' - 1 / 2 := by
    have : (x : ℝ) ≤ x' := by exact_mod_cast hx'
    linarith
  have hz₀' : (0 : ℝ) < z₀ := by exact_mod_cast hz₀
  have hz₁' : (0 : ℝ) < z₁ := by
    have : (z₀ : ℝ) ≤ z₁ := by exact_mod_cast hz
    linarith
  have key : ∀ z : ℝ, 0 < z → Real.arctan (z / (z ^ 2 + (x' - 1 / 2) * (x' - 1 / 2 + 1))) -
      Real.arctan (z / (z ^ 2 + (x - 1 / 2) * (x - 1 / 2 + 1))) =
      Real.arctan ((z / (z ^ 2 + (x' - 1 / 2) * (x' - 1 / 2 + 1)) -
        z / (z ^ 2 + (x - 1 / 2) * (x - 1 / 2 + 1))) /
        (1 + z / (z ^ 2 + (x' - 1 / 2) * (x' - 1 / 2 + 1)) *
          (z / (z ^ 2 + (x - 1 / 2) * (x - 1 / 2 + 1))))) := fun z hz ↦
    arctan_sub_arctan (by positivity)
  simp only [cornerSum, strainShift₁, atanDiff, strainQ]
  push_cast
  rw [← key z₁ hz₁', ← key z₀ hz₀']
  ring

/-- `1/2 < x` over the rationals gives `1/2 < x` over the reals. -/
private theorem cast_half_lt {x : ℚ} (hx : 1 / 2 < x) : (1 / 2 : ℝ) < x := by
  simpa using (Rat.cast_lt (K := ℝ)).2 hx

/-- The second moment shifts as one arctangent for the angular part and one per column. -/
theorem cornerSum_strainShift₂_eq {x x' z₀ z₁ : ℚ} (hx : 1 / 2 < x) (hx' : x ≤ x')
    (hz₀ : 0 < z₀) (hz : z₀ ≤ z₁) :
    cornerSum (fun s₁ z ↦ strainShift₂ (s₁ - 1 / 2) z) x x' z₀ z₁ =
      Real.arctan (atanDiff (strainG (x' - 1 / 2) z₀ z₁) (strainG (x - 1 / 2) z₀ z₁)) / 2 -
        (((x' : ℝ) - 1 / 2 + 1) / 2 * Real.arctan (atanDiff (strainQ (x' - 1 / 2) z₁)
            (strainQ (x' - 1 / 2) z₀)) -
          ((x : ℝ) - 1 / 2 + 1) / 2 * Real.arctan (atanDiff (strainQ (x - 1 / 2) z₁)
            (strainQ (x - 1 / 2) z₀))) := by
  have hu₀ : (0 : ℝ) < x - 1 / 2 := sub_pos.2 (cast_half_lt hx)
  have hu₁ : (0 : ℝ) < x' - 1 / 2 := hu₀.trans_le (sub_le_sub_right (by exact_mod_cast hx') _)
  have hz₀' : (0 : ℝ) < z₀ := by exact_mod_cast hz₀
  have hz₁' : (0 : ℝ) < z₁ := hz₀'.trans_le (by exact_mod_cast hz)
  have hσ := fun (u z : ℝ) (hu : 0 < u) (hz : 0 < z) ↦ strainShift₂_eq hu hz
  have hq : ∀ u : ℝ, 0 < u → Real.arctan (z₁ / (z₁ ^ 2 + u * (u + 1))) -
      Real.arctan (z₀ / (z₀ ^ 2 + u * (u + 1))) =
      Real.arctan ((z₁ / (z₁ ^ 2 + u * (u + 1)) - z₀ / (z₀ ^ 2 + u * (u + 1))) /
        (1 + z₁ / (z₁ ^ 2 + u * (u + 1)) * (z₀ / (z₀ ^ 2 + u * (u + 1))))) := fun u hu ↦
    arctan_sub_arctan (by positivity)
  have hgg : Real.arctan ((x' - 1 / 2) * (z₁ - z₀) / ((x' - 1 / 2) ^ 2 + z₀ * z₁)) -
      Real.arctan ((x - 1 / 2) * (z₁ - z₀) / ((x - 1 / 2) ^ 2 + z₀ * z₁)) =
      Real.arctan (((x' - 1 / 2) * (z₁ - z₀) / ((x' - 1 / 2) ^ 2 + z₀ * z₁) -
        (x - 1 / 2) * (z₁ - z₀) / ((x - 1 / 2) ^ 2 + z₀ * z₁)) /
        (1 + (x' - 1 / 2) * (z₁ - z₀) / ((x' - 1 / 2) ^ 2 + z₀ * z₁) *
          ((x - 1 / 2) * (z₁ - z₀) / ((x - 1 / 2) ^ 2 + z₀ * z₁)))) := by
    have hzz : (0 : ℝ) ≤ z₁ - z₀ := sub_nonneg.2 (by exact_mod_cast hz)
    exact arctan_sub_arctan (by positivity)
  simp only [cornerSum, atanDiff, strainQ, strainG]
  push_cast
  rw [hσ _ _ hu₁ hz₁', hσ _ _ hu₀ hz₁', hσ _ _ hu₁ hz₀', hσ _ _ hu₀ hz₀', ← hgg,
    ← hq _ hu₁, ← hq _ hu₀, ← arctan_sub_arctan_div hu₁ hz₀'.le hz₁'.le,
    ← arctan_sub_arctan_div hu₀ hz₀'.le hz₁'.le]
  ring

/-! ### The cell values -/

/-- A positive rational near `√q`. -/
def sqrtApprox (q : ℚ) : ℚ := max (1 / 2 ^ 40) (sqrtBelow 30 q)

/-- The approximation of `√q` is positive. -/
theorem sqrtApprox_pos (q : ℚ) : 0 < sqrtApprox q :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

/-- The slopes `(λ₁, λ₂)` of the affine majorant from the divided differences. -/
def strainSlopes (z₀ z₁ x x' T₀ T₁ : ℚ) : ℚ × ℚ :=
  let D := 16 * x' * (3 * T₁ ^ 2 + 2 * x' * T₁ + x' ^ 2 + 2 * z₁ ^ 2 - 1 / 2)
  (max 0 (floor32 (16 * T₀ * (T₀ ^ 2 + 2 * T₀ * x + 3 * x ^ 2 + 2 * z₀ ^ 2 - 1 / 2) / D)),
    max 0 (floor32 (2 * z₀ * max 0 (32 * z₀ ^ 2 + 8 - 32 * x' * T₁) / D)))

/-- `cr₀ / cr₁ - 1` for the cell. -/
def strainMassExcess (z₀ z₁ x x' : ℚ) : ℚ :=
  strainCrossRat (x - 1 / 2) (x' - 1 / 2) z₀ z₁ / strainCrossRat (x + 1 / 2) (x' + 1 / 2) z₀ z₁ - 1

/-- `cr₁ - 1` for the cell. -/
def strainShiftExcess (z₀ z₁ x x' : ℚ) : ℚ :=
  strainCrossRat (x + 1 / 2) (x' + 1 / 2) z₀ z₁ - 1

/-- The radius of the tangent bound of the second-order value. -/
def strainRadius (z₀ z₁ x x' c₀ c₁ c₂ : ℚ) : ℚ :=
  sqrtApprox (max (c₀ / 4) (c₀ - c₁ * (x' - x) / 2 - c₂ * (z₁ - z₀) / 2))

/-- The rational lower bound of the first-moment corner sum `S₁`. -/
def strainShift₁Low (z₀ z₁ x x' : ℚ) : ℚ :=
  z₁ / 2 * (atanPair (atanDiff (strainQ (x' - 1 / 2) z₁) (strainQ (x - 1 / 2) z₁))).1 -
    z₀ / 2 * (atanPair (atanDiff (strainQ (x' - 1 / 2) z₀) (strainQ (x - 1 / 2) z₀))).2

/-- The rational upper bound of the second-moment corner sum `S₂`. -/
def strainShift₂High (z₀ z₁ x x' : ℚ) : ℚ :=
  (atanPair (atanDiff (strainG (x' - 1 / 2) z₀ z₁) (strainG (x - 1 / 2) z₀ z₁))).2 / 2 -
    ((x' - 1 / 2 + 1) / 2 * (atanPair (atanDiff (strainQ (x' - 1 / 2) z₁)
        (strainQ (x' - 1 / 2) z₀))).1 -
      (x - 1 / 2 + 1) / 2 * (atanPair (atanDiff (strainQ (x - 1 / 2) z₁)
        (strainQ (x - 1 / 2) z₀))).2)

/-- The second-order value of a cell with the lower bound `T₀` and slopes `l₁, l₂`. -/
def strainSecondValue (z₀ z₁ x x' T₀ l₁ l₂ : ℚ) : ℚ :=
  let c₀ := x' - T₀
  let c₁ := 1 + l₁
  let r := strainRadius z₀ z₁ x x' c₀ c₁ l₂
  let p₀ := (c₀ + r ^ 2 - c₁ * x' + l₂ * z₀) / (2 * r)
  let p₁ := c₁ / (2 * r)
  let α := p₀ + p₁ / 2
  let e := strainMassExcess z₀ z₁ x x'
  α * (if 0 ≤ α then massHi (roundUpRel e) else massLo (roundDownRel e)) +
    p₁ * (massHi (roundUpRel (strainShiftExcess z₀ z₁ x x')) - strainShift₁Low z₀ z₁ x x') +
    l₂ / (2 * r) * strainShift₂High z₀ z₁ x x'

/-- The first-order value of a cell with the lower bound `T₀`. -/
def strainFirstValue (z₀ z₁ x x' T₀ : ℚ) : ℚ :=
  let c₀ := x' - T₀
  let r := sqrtApprox c₀
  (c₀ + r ^ 2) / (2 * r) * massHi (roundUpRel (strainMassExcess z₀ z₁ x x'))

/-- **The cell bound** of `[x, x'] × [z₀, z₁]`, with `c` an upper bound of the threshold used to
start Newton's method: the smaller of the first- and second-order values, after the checks. -/
def strainCellBound (c z₀ z₁ x x' : ℚ) : Option ℚ :=
  let T₀ := strainMapLow x' z₀ c
  let T₁ := strainMapHigh x z₁ c
  if strainLowOk x' z₀ T₀ && strainHighOk x z₁ T₁ && decide (T₀ ≤ x') && decide (c ≤ x) &&
      decide (1 / 2 < x) && decide (x ≤ x') && decide (0 < z₀) && decide (z₀ ≤ z₁) &&
      decide (0 ≤ strainMassExcess z₀ z₁ x x') && decide (0 ≤ strainShiftExcess z₀ z₁ x x') then
    some (roundUpRel (min (strainFirstValue z₀ z₁ x x' T₀)
      (strainSecondValue z₀ z₁ x x' T₀ (strainSlopes z₀ z₁ x x' T₀ T₁).1
        (strainSlopes z₀ z₁ x x' T₀ T₁).2)))
  else none

/-- The cell bound on the bottom slab `[x, x'] × (0, z₁]`: the first-order value with the lower
bound `T₀` certified on the axis. -/
def strainBottomBound (c z₁ x x' : ℚ) : Option ℚ :=
  let T₀ := strainMapLow x' 0 c
  if strainAxisOk x' T₀ && decide (T₀ ≤ x') && decide (c ≤ x) && decide (1 / 2 < x) &&
      decide (x ≤ x') && decide (0 ≤ z₁) && decide (0 ≤ strainMassExcess 0 z₁ x x') then
    some (roundUpRel (strainFirstValue 0 z₁ x x' T₀))
  else none

/-! ### Soundness of the cells -/

/-- The cast of the mass ratio is `1 + e`. -/
theorem cast_strainMassExcess (z₀ z₁ x x' : ℚ) :
    strainCross ((x : ℝ) - 1 / 2) ((x' : ℝ) - 1 / 2) z₀ z₁ /
        strainCross ((x : ℝ) + 1 / 2) ((x' : ℝ) + 1 / 2) z₀ z₁ =
      1 + (strainMassExcess z₀ z₁ x x' : ℝ) := by
  simp only [strainMassExcess]
  push_cast
  rw [cast_strainCrossRat, cast_strainCrossRat]
  push_cast
  ring

/-- The cross ratio at the abscissae `x + 1/2`, `x' + 1/2` is `1 + strainShiftExcess`. -/
theorem cast_strainShiftExcess (z₀ z₁ x x' : ℚ) :
    strainCross ((x : ℝ) + 1 / 2) ((x' : ℝ) + 1 / 2) z₀ z₁ =
      1 + (strainShiftExcess z₀ z₁ x x' : ℝ) := by
  simp only [strainShiftExcess]
  push_cast
  rw [cast_strainCrossRat]
  push_cast
  ring

/-- `(1/4) log (cr₀/cr₁) ≤ massHi (roundUpRel e)`. -/
theorem log_strainCross_le_massHi {z₀ z₁ x x' : ℚ} (he : 0 ≤ strainMassExcess z₀ z₁ x x') :
    Real.log (strainCross ((x : ℝ) - 1 / 2) ((x' : ℝ) - 1 / 2) z₀ z₁ /
        strainCross ((x : ℝ) + 1 / 2) ((x' : ℝ) + 1 / 2) z₀ z₁) / 4 ≤
      (massHi (roundUpRel (strainMassExcess z₀ z₁ x x')) : ℝ) := by
  rw [cast_strainMassExcess]
  have he' : (0 : ℝ) ≤ strainMassExcess z₀ z₁ x x' := by exact_mod_cast he
  refine log_div_four_le_massHi (by linarith) ?_
  linarith [(Rat.cast_le (K := ℝ)).2 (le_roundUpRel (strainMassExcess z₀ z₁ x x'))]

/-- **The first-order cell.** -/
theorem lintegral_le_strainFirstValue {z₀ z₁ x x' T₀ : ℚ} (hx : 1 / 2 < x) (hxx : x ≤ x')
    (hz₀ : 0 ≤ z₀) (hz : z₀ ≤ z₁) (hfull : strainThreshold z₁ ≤ x)
    (hT : ∀ s₁ ∈ Icc (x : ℝ) x', ∀ s₂ ∈ Ioc (z₀ : ℝ) z₁, (T₀ : ℝ) ≤ strainMap s₁ s₂)
    (hT₀x : T₀ ≤ x') (he : 0 ≤ strainMassExcess z₀ z₁ x x') :
    ∫⁻ s₂ in Ioc (z₀ : ℝ) z₁, ∫⁻ s₁ in Ioc (x : ℝ) x', strainCostIntegrand s₂ s₁ ≤
      ENNReal.ofReal (strainFirstValue z₀ z₁ x x' T₀) := by
  set r := sqrtApprox (x' - T₀)
  have hr : (0 : ℝ) < r := by exact_mod_cast sqrtApprox_pos _
  have hφ₀ : (0 : ℝ) ≤ ((x' - T₀ : ℚ) : ℝ) := by exact_mod_cast sub_nonneg.2 hT₀x
  have h := lintegral_strainCostIntegrand_cell_le_const (x₀ := x) (x₁ := x') (z₀ := z₀)
    (z₁ := z₁) (φ₀ := ((x' - T₀ : ℚ) : ℝ)) (r := r) (cast_half_lt hx) (by exact_mod_cast hxx)
    (by exact_mod_cast hz₀) (by exact_mod_cast hz) hfull (fun s₁ hs₁ s₂ hs₂ ↦ by
      have := hT s₁ hs₁ s₂ hs₂
      push_cast
      linarith [hs₁.2]) hφ₀ hr
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  simp only [strainFirstValue]
  push_cast
  have hφ' : (0 : ℝ) ≤ (x' : ℝ) - T₀ := by push_cast at hφ₀; exact hφ₀
  refine mul_le_mul_of_nonneg_left ?_
    (div_nonneg (add_nonneg hφ' (sq_nonneg _)) (by positivity))
  exact_mod_cast log_strainCross_le_massHi he

/-- The slopes satisfy the hypotheses of `sub_strainMap_le_affine`. -/
theorem strainSlopes_spec {z₀ z₁ x x' T₀ T₁ : ℚ} (hx : 1 / 2 < x) (hT₀0 : 0 ≤ T₀)
    (hz₀ : 0 < z₀) :
    0 ≤ (strainSlopes z₀ z₁ x x' T₀ T₁).1 ∧ 0 ≤ (strainSlopes z₀ z₁ x x' T₀ T₁).2 ∧
    ((strainSlopes z₀ z₁ x x' T₀ T₁).1 : ℝ) * strainDenomBound x' z₁ T₁ ≤
      16 * T₀ * ((T₀ : ℝ) ^ 2 + 2 * T₀ * x + 3 * x ^ 2 + 2 * z₀ ^ 2 - 1 / 2) ∧
    ((strainSlopes z₀ z₁ x x' T₀ T₁).2 : ℝ) * strainDenomBound x' z₁ T₁ ≤
      2 * z₀ * max 0 (32 * (z₀ : ℝ) ^ 2 + 8 - 32 * x' * T₁) := by
  set D : ℚ := 16 * x' * (3 * T₁ ^ 2 + 2 * x' * T₁ + x' ^ 2 + 2 * z₁ ^ 2 - 1 / 2)
  set A : ℚ := 16 * T₀ * (T₀ ^ 2 + 2 * T₀ * x + 3 * x ^ 2 + 2 * z₀ ^ 2 - 1 / 2)
  set B : ℚ := 2 * z₀ * max 0 (32 * z₀ ^ 2 + 8 - 32 * x' * T₁)
  have hD : (strainDenomBound x' z₁ T₁ : ℝ) = (D : ℝ) := by
    simp only [strainDenomBound, D]
    push_cast
    ring
  have hA0 : 0 ≤ A := by
    have : 1 / 4 < x ^ 2 := by nlinarith
    have : 0 ≤ T₀ ^ 2 + 2 * T₀ * x + 3 * x ^ 2 + 2 * z₀ ^ 2 - 1 / 2 := by nlinarith
    positivity
  have hB0 : 0 ≤ B := by positivity
  have key : ∀ C : ℚ, 0 ≤ C → max 0 (floor32 (C / D)) * D ≤ C := by
    intro C hC
    rcases le_or_gt D 0 with hD0 | hD0
    · exact (mul_nonpos_of_nonneg_of_nonpos (le_max_left _ _) hD0).trans hC
    · exact (mul_le_mul_of_nonneg_right (max_le (div_nonneg hC hD0.le) (floor32_le _))
        hD0.le).trans_eq (div_mul_cancel₀ C hD0.ne')
  refine ⟨le_max_left _ _, le_max_left _ _, ?_, ?_⟩ <;> rw [hD] <;> simp only [strainSlopes, D]
  · simpa [A, D] using (Rat.cast_le (K := ℝ)).2 (key A hA0)
  · simpa [B, D] using (Rat.cast_le (K := ℝ)).2 (key B hB0)

/-- **The second-order cell.** -/
theorem lintegral_le_strainSecondValue {z₀ z₁ x x' T₀ T₁ : ℚ} (hx : 1 / 2 < x) (hxx : x ≤ x')
    (hz₀ : 0 < z₀) (hz : z₀ ≤ z₁) (hfull : strainThreshold z₁ ≤ x)
    (hT₀ : (T₀ : ℝ) ≤ strainMap x' z₀) (hT₁ : strainMap x z₁ ≤ T₁) (hT₀0 : 0 ≤ T₀)
    (he : 0 ≤ strainMassExcess z₀ z₁ x x') (he₁ : 0 ≤ strainShiftExcess z₀ z₁ x x') :
    ∫⁻ s₂ in Ioc (z₀ : ℝ) z₁, ∫⁻ s₁ in Ioc (x : ℝ) x', strainCostIntegrand s₂ s₁ ≤
      ENNReal.ofReal (strainSecondValue z₀ z₁ x x' T₀ (strainSlopes z₀ z₁ x x' T₀ T₁).1
        (strainSlopes z₀ z₁ x x' T₀ T₁).2) := by
  obtain ⟨hl₁0, hl₂0, hl₁, hl₂⟩ := strainSlopes_spec (z₁ := z₁) (x' := x') (T₁ := T₁) hx hT₀0 hz₀
  set l₁ := (strainSlopes z₀ z₁ x x' T₀ T₁).1
  set l₂ := (strainSlopes z₀ z₁ x x' T₀ T₁).2
  have hx' : (1 / 2 : ℝ) < x := cast_half_lt hx
  have hxx' : (x : ℝ) ≤ x' := by exact_mod_cast hxx
  have hz₀' : (0 : ℝ) < z₀ := by exact_mod_cast hz₀
  have hz' : (z₀ : ℝ) ≤ z₁ := by exact_mod_cast hz
  set r := strainRadius z₀ z₁ x x' (x' - T₀) (1 + l₁) l₂
  have hr : (0 : ℝ) < r := by exact_mod_cast sqrtApprox_pos _
  have hL : ∀ s₁ ∈ Icc (x : ℝ) x', ∀ s₂ ∈ Icc (z₀ : ℝ) z₁, s₁ - strainMap s₁ s₂ ≤
      ((x' - T₀ : ℚ) : ℝ) - ((1 + l₁ : ℚ) : ℝ) * (x' - s₁) - (l₂ : ℝ) * (s₂ - z₀) := by
    intro s₁ hs₁ s₂ hs₂
    have := sub_strainMap_le_affine hx'.le hz₀' hs₁ hs₂ hT₀ hT₁ (by exact_mod_cast hT₀0) hl₁
      (by exact_mod_cast hl₁0) hl₂ (by exact_mod_cast hl₂0)
    push_cast
    linarith
  have hcell := lintegral_strainCostIntegrand_cell_le hxx' hz₀' hz' hfull hL hr
  rw [cornerSum_strainCell_eq _ _ _ hx' hxx' hz₀' hz', cornerSum_strainShift₁_eq hx hxx hz₀ hz,
    cornerSum_strainShift₂_eq hx hxx hz₀ hz] at hcell
  refine hcell.trans (ENNReal.ofReal_le_ofReal ?_)
  -- the real quantities and their rational bounds
  have hM := log_strainCross_le_massHi he
  have hMlo : (massLo (roundDownRel (strainMassExcess z₀ z₁ x x')) : ℝ) ≤
      Real.log (strainCross ((x : ℝ) - 1 / 2) ((x' : ℝ) - 1 / 2) z₀ z₁ /
        strainCross ((x : ℝ) + 1 / 2) ((x' : ℝ) + 1 / 2) z₀ z₁) / 4 := by
    rw [cast_strainMassExcess]
    refine massLo_le_log_div_four (roundDownRel_nonneg he) ?_
    linarith [(Rat.cast_le (K := ℝ)).2 (roundDownRel_le (strainMassExcess z₀ z₁ x x'))]
  have hL1 : Real.log (strainCross ((x : ℝ) + 1 / 2) ((x' : ℝ) + 1 / 2) z₀ z₁) / 4 ≤
      (massHi (roundUpRel (strainShiftExcess z₀ z₁ x x')) : ℝ) := by
    rw [cast_strainShiftExcess]
    have he₁' : (0 : ℝ) ≤ strainShiftExcess z₀ z₁ x x' := by exact_mod_cast he₁
    refine log_div_four_le_massHi (by linarith) ?_
    linarith [(Rat.cast_le (K := ℝ)).2 (le_roundUpRel (strainShiftExcess z₀ z₁ x x'))]
  have hS₁ : (strainShift₁Low z₀ z₁ x x' : ℝ) ≤
      (z₁ : ℝ) / 2 * Real.arctan (atanDiff (strainQ (x' - 1 / 2) z₁) (strainQ (x - 1 / 2) z₁)) -
        (z₀ : ℝ) / 2 * Real.arctan (atanDiff (strainQ (x' - 1 / 2) z₀)
          (strainQ (x - 1 / 2) z₀)) := by
    simp only [strainShift₁Low]
    push_cast
    have h₁ := atanPair_fst_le (atanDiff (strainQ (x' - 1 / 2) z₁) (strainQ (x - 1 / 2) z₁))
    have h₀ := le_atanPair_snd (atanDiff (strainQ (x' - 1 / 2) z₀) (strainQ (x - 1 / 2) z₀))
    have hz₁0 : (0 : ℝ) ≤ z₁ / 2 := by linarith
    have hz₀0 : (0 : ℝ) ≤ z₀ / 2 := by linarith
    linarith [mul_le_mul_of_nonneg_left h₁ hz₁0, mul_le_mul_of_nonneg_left h₀ hz₀0]
  have hS₂ : Real.arctan (atanDiff (strainG (x' - 1 / 2) z₀ z₁) (strainG (x - 1 / 2) z₀ z₁)) / 2 -
        (((x' : ℝ) - 1 / 2 + 1) / 2 * Real.arctan (atanDiff (strainQ (x' - 1 / 2) z₁)
            (strainQ (x' - 1 / 2) z₀)) -
          ((x : ℝ) - 1 / 2 + 1) / 2 * Real.arctan (atanDiff (strainQ (x - 1 / 2) z₁)
            (strainQ (x - 1 / 2) z₀))) ≤ (strainShift₂High z₀ z₁ x x' : ℝ) := by
    simp only [strainShift₂High]
    push_cast
    have hF := le_atanPair_snd (atanDiff (strainG (x' - 1 / 2) z₀ z₁) (strainG (x - 1 / 2) z₀ z₁))
    have hG₁ := atanPair_fst_le (atanDiff (strainQ (x' - 1 / 2) z₁) (strainQ (x' - 1 / 2) z₀))
    have hG₀ := le_atanPair_snd (atanDiff (strainQ (x - 1 / 2) z₁) (strainQ (x - 1 / 2) z₀))
    have hu₁ : (0 : ℝ) ≤ ((x' : ℝ) - 1 / 2 + 1) / 2 := by linarith
    have hu₀ : (0 : ℝ) ≤ ((x : ℝ) - 1 / 2 + 1) / 2 := by linarith
    linarith [mul_le_mul_of_nonneg_left hG₁ hu₁, mul_le_mul_of_nonneg_left hG₀ hu₀]
  -- combine
  simp only [strainSecondValue, strainCellWeight]
  set M := Real.log (strainCross ((x : ℝ) - 1 / 2) ((x' : ℝ) - 1 / 2) z₀ z₁ /
    strainCross ((x : ℝ) + 1 / 2) ((x' : ℝ) + 1 / 2) z₀ z₁) / 4
  generalize hα : ((x' - T₀ : ℚ) + r ^ 2 - (1 + l₁) * x' + l₂ * z₀) / (2 * r) +
    (1 + l₁) / (2 * r) / 2 = α
  have hαr : ((((x' - T₀ : ℚ) : ℝ) + (r : ℝ) ^ 2 - ((1 + l₁ : ℚ) : ℝ) * x' + l₂ * z₀) /
      (2 * r) + ((1 + l₁ : ℚ) : ℝ) / (2 * r) / 2) = (α : ℝ) := by
    rw [← hα]; push_cast; ring
  have hp₁ : (0 : ℝ) ≤ ((1 + l₁ : ℚ) : ℝ) / (2 * r) :=
    div_nonneg (Rat.cast_nonneg.2 (by linarith)) (by positivity)
  have hq₂ : (0 : ℝ) ≤ (l₂ : ℝ) / (2 * r) := div_nonneg (Rat.cast_nonneg.2 hl₂0) (by positivity)
  have hMterm : (α : ℝ) * M ≤ ((α * (if 0 ≤ α then massHi (roundUpRel (strainMassExcess z₀ z₁ x x'))
      else massLo (roundDownRel (strainMassExcess z₀ z₁ x x'))) : ℚ) : ℝ) := by
    split_ifs with hα0
    · push_cast
      exact mul_le_mul_of_nonneg_left hM (by exact_mod_cast hα0)
    · push_cast
      exact mul_le_mul_of_nonpos_left hMlo (by exact_mod_cast (not_le.1 hα0).le)
  have hr' : strainRadius z₀ z₁ x x' (x' - T₀) (1 + l₁) l₂ = r := rfl
  have key : ∀ a b c a' b' c' : ℝ, a ≤ a' → b ≤ b' → -c ≤ c' → a + b - c ≤ a' + b' + c' :=
    fun a b c a' b' c' h₁ h₂ h₃ ↦ by linarith
  have hcast3 : ∀ a b c : ℚ, ((a + b + c : ℚ) : ℝ) = (a : ℝ) + b + c := fun _ _ _ ↦ by
    push_cast; ring
  rw [hr', hcast3]
  refine key _ _ _ _ _ _ ?_ ?_ ?_
  · rw [hαr]
    exact hMterm
  · push_cast
    push_cast at hp₁
    exact mul_le_mul_of_nonneg_left (by linarith) hp₁
  · push_cast
    rw [neg_div, neg_mul, neg_neg]
    exact mul_le_mul_of_nonneg_left hS₂ hq₂

/-- **Soundness of one cell**: the cell bound bounds the cell integral, provided the starting value
`c` lies above the threshold at the top of the slab. -/
theorem lintegral_le_strainCellBound {c z₀ z₁ x x' U : ℚ} (hc : strainThreshold z₁ ≤ c)
    (h : strainCellBound c z₀ z₁ x x' = some U) :
    ∫⁻ s₂ in Ioc (z₀ : ℝ) z₁, ∫⁻ s₁ in Ioc (x : ℝ) x', strainCostIntegrand s₂ s₁ ≤
      ENNReal.ofReal U := by
  unfold strainCellBound at h
  dsimp only at h
  split_ifs at h with hck
  obtain rfl := Option.some.inj h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hlow, hhigh⟩, hT₀x⟩, hcx⟩, hx⟩, hxx⟩, hz₀⟩, hz⟩, he⟩, he₁⟩ := hck
  have hz₀' : (0 : ℝ) < z₀ := by exact_mod_cast hz₀
  have hx0 : (0 : ℚ) < x := by linarith
  have hfull : strainThreshold z₁ ≤ x := hc.trans (by exact_mod_cast hcx)
  have hT₀ := le_strainMap_of_lowOk (hx0.trans_le hxx) hz₀'.ne' hlow
  have hz₁' : (z₁ : ℝ) ≠ 0 := (hz₀'.trans_le (by exact_mod_cast hz)).ne'
  have hT₁ := strainMap_le_of_highOk hx0 hz₁' hhigh
  have hT₀0 : 0 ≤ strainMapLow x' z₀ c := le_max_left _ _
  have h₁ : ∫⁻ s₂ in Ioc (z₀ : ℝ) z₁, ∫⁻ s₁ in Ioc (x : ℝ) x', strainCostIntegrand s₂ s₁ ≤
      ENNReal.ofReal (strainFirstValue z₀ z₁ x x' (strainMapLow x' z₀ c)) := by
    exact lintegral_le_strainFirstValue hx hxx hz₀.le hz hfull (fun s₁ hs₁ s₂ hs₂ ↦ hT₀.trans
      (strainMap_mem_cell (by exact_mod_cast hx0) hz₀' hs₁ (Ioc_subset_Icc_self hs₂)).1) hT₀x he
  have h₂ := lintegral_le_strainSecondValue (T₁ := strainMapHigh x z₁ c) hx hxx hz₀ hz hfull hT₀
    hT₁ hT₀0 he he₁
  refine (le_min h₁ h₂).trans ?_
  rw [← ENNReal.ofReal_min]
  exact ENNReal.ofReal_le_ofReal (by exact_mod_cast le_roundUpRel _)

/-- **Soundness of one bottom cell** `[x, x'] × (0, z₁]`. -/
theorem lintegral_le_strainBottomBound {c z₁ x x' U : ℚ} (hc : strainThreshold z₁ ≤ c)
    (h : strainBottomBound c z₁ x x' = some U) :
    ∫⁻ s₂ in Ioc (0 : ℝ) z₁, ∫⁻ s₁ in Ioc (x : ℝ) x', strainCostIntegrand s₂ s₁ ≤
      ENNReal.ofReal U := by
  unfold strainBottomBound at h
  dsimp only at h
  split_ifs at h with hck
  obtain rfl := Option.some.inj h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨⟨⟨⟨haxis, hT₀x⟩, hcx⟩, hx⟩, hxx⟩, hz₁⟩, he⟩ := hck
  have hx0 : (0 : ℚ) < x := by linarith
  have hfull : strainThreshold z₁ ≤ x := hc.trans (by exact_mod_cast hcx)
  have h₁ := lintegral_le_strainFirstValue (z₀ := 0) hx hxx le_rfl hz₁ hfull
    (fun s₁ hs₁ s₂ hs₂ ↦ by
      have hs₂0 : (0 : ℝ) < s₂ := by simpa using hs₂.1
      have hx' : (0 : ℝ) < x := by exact_mod_cast hx0
      have hT := le_strainMap_of_axisOk (s₂ := s₂) (hx0.trans_le hxx) haxis
      exact hT.trans ((strictAntiOn_strainMap hs₂0).antitoneOn (hx'.trans_le hs₁.1)
        (hx'.trans_le (hs₁.1.trans hs₁.2)) hs₁.2)) hT₀x he
  push_cast at h₁
  refine h₁.trans (ENNReal.ofReal_le_ofReal ?_)
  exact_mod_cast le_roundUpRel _

/-! ### Slabs -/

/-- For a set `S`, `s₂ ↦ ∫⁻ s₁ in S, strainCostIntegrand s₂ s₁` is measurable. -/
theorem measurable_lintegral_strainCostIntegrand (S : Set ℝ) :
    Measurable fun s₂ ↦ ∫⁻ s₁ in S, strainCostIntegrand s₂ s₁ :=
  measurable_strainCost_integrand.lintegral_prod_right'

/-- Two lower integrals over `s₂` of inner lower integrals add. -/
theorem lintegral_lintegral_le_add (Z : Set ℝ) {a b c : ℝ} :
    ∫⁻ s₂ in Z, ∫⁻ s₁ in Ioc a c, strainCostIntegrand s₂ s₁ ≤
      (∫⁻ s₂ in Z, ∫⁻ s₁ in Ioc a b, strainCostIntegrand s₂ s₁) +
        ∫⁻ s₂ in Z, ∫⁻ s₁ in Ioc b c, strainCostIntegrand s₂ s₁ := by
  rw [← lintegral_add_left (measurable_lintegral_strainCostIntegrand _)]
  exact lintegral_mono fun s₂ ↦
    (lintegral_mono_set Ioc_subset_Ioc_union_Ioc).trans (lintegral_union_le _ _ _)

/-- The upper end of the walks in `s₁`, `2^30`. -/
def strainWalkEnd : ℚ := 2 ^ 30

/-- The next node in `s₁` in a slab: the offsets from `c` grow from `d₀` by the ratio `3/32` while
they lie in `[z₁/16, 16 z₁]` and by `1/2` outside, on the grid `2^-40`. -/
def strainSlabNext (c d₀ z₁ x : ℚ) : ℚ :=
  let o := x - c
  if o < d₀ then c + d₀
  else
    let ρ : ℚ := if o * 16 < z₁ ∨ 16 * z₁ < o then 1 / 2 else 3 / 32
    c + (⌈(o + o * ρ) * 2 ^ 40⌉ : ℚ) / 2 ^ 40

/-- The integer cell of the walk in a slab. -/
def strainSlabCell (c z₀ z₁ x x' : ℚ) : Option ℤ :=
  match strainCellBound c z₀ z₁ x x' with
  | some U => some (ceilScaled 64 U)
  | none => none

/-- The rational form of `strainStripBound`. -/
def strainStripBoundRat (fl fu z₀ z₁ : ℚ) : ℚ :=
  z₁ * (3 * (fu ^ 2 - fl ^ 2) * (fu ^ 2 + z₁ ^ 2 + 1 / 12)) /
    (((fl + 1 / 2) ^ 2 + z₀ ^ 2) ^ 2 * ((fl - 1 / 2) ^ 2 + z₀ ^ 2) ^ 2)

/-- The bound of the strip `[f⁻, f⁺] × [z₀, z₁]` of a slab. -/
def strainStripValue (fl fu z₀ z₁ : ℚ) : Option ℚ :=
  let T₀ := strainMapLow fu z₀ fu
  if strainLowOk fu z₀ T₀ && decide (T₀ ≤ fu) && decide (1 / 2 ≤ fl) && decide (fl ≤ fu) &&
      decide (0 < z₀) && decide (z₀ ≤ z₁) then
    let φ₁ := fu - T₀
    let r := sqrtApprox φ₁
    some ((z₁ - z₀) * ((fu - fl) * (strainStripBoundRat fl fu z₀ z₁ * ((φ₁ + r ^ 2) / (2 * r)))))
  else none

/-- **Soundness of the strip**: if `f⁻ ≤ f(z₀)`, a strip value `v` bounds the cost over
`(z₀, z₁] × (f⁻, f⁺]`. -/
theorem lintegral_le_strainStripValue {fl fu z₀ z₁ v : ℚ} (hfl : (fl : ℝ) ≤ strainThreshold z₀)
    (h : strainStripValue fl fu z₀ z₁ = some v) :
    ∫⁻ s₂ in Ioc (z₀ : ℝ) z₁, ∫⁻ s₁ in Ioc (fl : ℝ) fu, strainCostIntegrand s₂ s₁ ≤
      ENNReal.ofReal v := by
  unfold strainStripValue at h
  dsimp only at h
  split_ifs at h with hck
  obtain rfl := Option.some.inj h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨⟨⟨hlow, hT₀⟩, hfl'⟩, hff⟩, hz₀⟩, hz⟩ := hck
  have hz₀' : (0 : ℝ) < z₀ := by exact_mod_cast hz₀
  have hfu0 : (0 : ℚ) < fu := by linarith
  have hT := le_strainMap_of_lowOk hfu0 hz₀'.ne' hlow
  set T₀ := strainMapLow fu z₀ fu
  set r := sqrtApprox (fu - T₀)
  have hr : (0 : ℝ) < r := by exact_mod_cast sqrtApprox_pos _
  have hfl'' : (1 / 2 : ℝ) ≤ fl := by simpa using (Rat.cast_le (K := ℝ)).2 hfl'
  have h₁ := lintegral_strainCostIntegrand_strip_le (fl := fl) (fu := fu) (z₀ := z₀) (z₁ := z₁)
    (φ₁ := ((fu - T₀ : ℚ) : ℝ)) (r := r) hfl''
    (by exact_mod_cast hff) hz₀' (by exact_mod_cast hz) hfl (fun s₁ hs₁ s₂ hs₂ ↦ by
      have := sub_strainMap_le_corner (lt_of_lt_of_le (by norm_num) (hfl''.trans hs₁.1)) hs₁.2
        hz₀' hs₂.1
      push_cast
      linarith) (by exact_mod_cast sub_nonneg.2 hT₀) hr
  refine h₁.trans (le_of_eq ?_)
  congr 1
  simp only [strainStripBound, strainStripBoundRat]
  push_cast
  ring

/-- **The slab check** of `[z₀, z₁] × (-∞, 2^30]`: the threshold bounds `f⁻ ≤ f(z₀)` and
`f(z₁) ≤ f⁺`, the strip `[f⁻, f⁺]` and the walk of cells from `f⁺` to `2^30`; the result is an
integer bound on the grid `2^-64`. -/
def strainSlab (z₀ z₁ : ℚ) : Option ℤ :=
  let fl := thresholdLow z₀
  let fu := thresholdGuess true z₁
  if (decide (fl ≤ 1 / 2) || decide (0 < strainQuarticRat fl z₀)) && decide (0 ≤ fu) &&
      decide (strainQuarticRat fu z₁ < 0) && decide (fu ≤ strainWalkEnd) then
    match strainStripValue fl fu z₀ z₁ with
    | none => none
    | some v =>
      match cellWalk (strainSlabNext fu (max (fu - fl) (z₁ / 2 ^ 8)) z₁)
          (strainSlabCell fu z₀ z₁) 100000 fu strainWalkEnd 0 with
      | some n => if 0 ≤ v then some (ceilScaled 64 v + n) else none
      | none => none
  else none

/-- The cost integrand vanishes at and below the threshold `f(s₂)`. -/
private theorem strainCostIntegrand_eq_zero {s₂ s₁ : ℝ} (h : s₁ ≤ strainThreshold s₂) :
    strainCostIntegrand s₂ s₁ = 0 := by
  unfold strainCostIntegrand
  exact indicator_of_notMem (by simpa using h) _

/-- **Soundness of the slab check.** -/
theorem lintegral_le_strainSlab {z₀ z₁ : ℚ} {N : ℤ} (h : strainSlab z₀ z₁ = some N) :
    ∫⁻ s₂ in Ioc (z₀ : ℝ) z₁, ∫⁻ s₁ in Iic (strainWalkEnd : ℝ), strainCostIntegrand s₂ s₁ ≤
      ENNReal.ofReal (N / 2 ^ 64) := by
  unfold strainSlab at h
  dsimp only at h
  split_ifs at h with hck
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨hfl, hfu0⟩, hfu⟩, hfuR⟩ := hck
  set fl := thresholdLow z₀
  set fu := thresholdGuess true z₁
  split at h
  · simp at h
  rename_i v hv
  split at h
  · rename_i n hn
    split_ifs at h with hv0
    obtain rfl := Option.some.inj h
    -- the strip and threshold facts
    have hfl' : (fl : ℝ) ≤ strainThreshold z₀ := le_strainThreshold_of_quartic <| hfl.imp id
      fun h ↦ ⟨le_trans (by norm_num) (le_max_left _ _), cast_strainQuarticRat fl z₀ ▸
        Rat.cast_pos.2 h⟩
    have hfu' : strainThreshold z₁ ≤ (fu : ℝ) := strainThreshold_le_of_quartic hfu0
      (cast_strainQuarticRat fu z₁ ▸ Rat.cast_lt_zero.2 hfu)
    -- the strip check gives `0 < z₀` and `f⁻ ≤ f⁺`
    obtain ⟨hff, hz₀'⟩ : (fl : ℝ) ≤ fu ∧ (0 : ℝ) < z₀ := by
      unfold strainStripValue at hv
      dsimp only at hv
      split_ifs at hv with hck'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hck'
      exact ⟨by exact_mod_cast hck'.1.1.2, by exact_mod_cast hck'.1.2⟩
    -- split the inner range
    have hsplit : ∀ s₂ ∈ Ioc (z₀ : ℝ) z₁, ∫⁻ s₁ in Iic (strainWalkEnd : ℝ),
        strainCostIntegrand s₂ s₁ ≤ (∫⁻ s₁ in Ioc (fl : ℝ) fu, strainCostIntegrand s₂ s₁) +
          ∫⁻ s₁ in Ioc (fu : ℝ) strainWalkEnd, strainCostIntegrand s₂ s₁ := by
      intro s₂ hs₂
      have hf : (fl : ℝ) ≤ strainThreshold s₂ := hfl'.trans (monotoneOn_strainThreshold
        (show (z₀ : ℝ) ∈ Ici 0 from hz₀'.le) (show s₂ ∈ Ici 0 from (hz₀'.trans hs₂.1).le)
        hs₂.1.le)
      have h0 : ∫⁻ s₁ in Iic (fl : ℝ), strainCostIntegrand s₂ s₁ = 0 := by
        rw [setLIntegral_congr_fun (measurableSet_Iic : MeasurableSet (Iic (fl : ℝ)))
          (g := fun _ ↦ 0)
          (fun t ht ↦ strainCostIntegrand_eq_zero ((show t ≤ fl from ht).trans hf))]
        simp
      calc ∫⁻ s₁ in Iic (strainWalkEnd : ℝ), strainCostIntegrand s₂ s₁
          = ∫⁻ s₁ in Iic (fl : ℝ) ∪ (Ioc (fl : ℝ) fu ∪ Ioc (fu : ℝ) strainWalkEnd),
              strainCostIntegrand s₂ s₁ := by
            rw [Ioc_union_Ioc_eq_Ioc hff (by exact_mod_cast hfuR),
              Iic_union_Ioc_eq_Iic (hff.trans (by exact_mod_cast hfuR))]
        _ ≤ (∫⁻ s₁ in Iic (fl : ℝ), strainCostIntegrand s₂ s₁) +
              ((∫⁻ s₁ in Ioc (fl : ℝ) fu, strainCostIntegrand s₂ s₁) +
                ∫⁻ s₁ in Ioc (fu : ℝ) strainWalkEnd, strainCostIntegrand s₂ s₁) :=
            (lintegral_union_le _ _ _).trans (add_le_add le_rfl (lintegral_union_le _ _ _))
        _ = _ := by rw [h0, zero_add]
    -- the walk of cells
    have hwalk := le_of_cellWalk_of_subadditive
      (Φ := fun a b ↦ ∫⁻ s₂ in Ioc (z₀ : ℝ) z₁, ∫⁻ s₁ in Ioc a b, strainCostIntegrand s₂ s₁)
      (g := fun q : ℚ ↦ (q : ℝ)) (K := 64)
      (fun a ha b hb hab ↦ Rat.cast_le.2 hab)
      (fun _ _ _ _ _ ↦ lintegral_lintegral_le_add _)
      (fun a b hba ↦ by simp [Ioc_eq_empty (not_lt.2 hba)])
      (fun l u m hl hlu hm ↦ by
        unfold strainSlabCell at hm
        split at hm
        · rename_i U hU
          obtain rfl := Option.some.inj hm
          exact (lintegral_le_strainCellBound hfu' hU).trans
            (ENNReal.ofReal_le_ofReal (le_ceilScaled_real 64 U))
        · simp at hm) (by exact_mod_cast hfu0) (by norm_num [strainWalkEnd]) hn
    have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast le_of_cellWalk hn
    have hv1 : (0 : ℝ) ≤ (ceilScaled 64 v : ℝ) / 2 ^ 64 :=
      (by exact_mod_cast hv0 : (0 : ℝ) ≤ v).trans (le_ceilScaled_real 64 v)
    calc ∫⁻ s₂ in Ioc (z₀ : ℝ) z₁, ∫⁻ s₁ in Iic (strainWalkEnd : ℝ), strainCostIntegrand s₂ s₁
        ≤ ∫⁻ s₂ in Ioc (z₀ : ℝ) z₁, ((∫⁻ s₁ in Ioc (fl : ℝ) fu, strainCostIntegrand s₂ s₁) +
            ∫⁻ s₁ in Ioc (fu : ℝ) strainWalkEnd, strainCostIntegrand s₂ s₁) :=
          setLIntegral_mono' measurableSet_Ioc hsplit
      _ = (∫⁻ s₂ in Ioc (z₀ : ℝ) z₁, ∫⁻ s₁ in Ioc (fl : ℝ) fu, strainCostIntegrand s₂ s₁) +
            ∫⁻ s₂ in Ioc (z₀ : ℝ) z₁, ∫⁻ s₁ in Ioc (fu : ℝ) strainWalkEnd,
              strainCostIntegrand s₂ s₁ :=
          lintegral_add_left (measurable_lintegral_strainCostIntegrand _) _
      _ ≤ ENNReal.ofReal ((ceilScaled 64 v : ℝ) / 2 ^ 64) +
            ENNReal.ofReal (((n : ℝ) - ((0 : ℤ) : ℝ)) / 2 ^ 64) :=
          add_le_add ((lintegral_le_strainStripValue hfl' hv).trans
            (ENNReal.ofReal_le_ofReal (le_ceilScaled_real 64 v))) hwalk
      _ = ENNReal.ofReal (((ceilScaled 64 v + n : ℤ) : ℝ) / 2 ^ 64) := by
          rw [← ENNReal.ofReal_add hv1 (by simpa using div_nonneg hn0 (by positivity))]
          congr 1
          push_cast
          ring
  · simp at h

/-! ### The bottom slab and the walk over slabs -/

/-- The height `2^-17` of the bottom slab. -/
def strainBottomHeight : ℚ := 1 / 2 ^ 17

/-- The width `2^-31` of the corner strip of the bottom slab. -/
def strainCornerWidth : ℚ := 1 / 2 ^ 31

/-- The next node of the bottom slab: the offsets `s₁ - 1/2` grow by `3/32` up to `16 · 2^-17`
and by `1/2` beyond, on the grid `2^-48`. -/
def strainBottomNext (x : ℚ) : ℚ :=
  let o := x - 1 / 2
  let ρ : ℚ := if 16 * strainBottomHeight < o then 1 / 2 else 3 / 32
  1 / 2 + (⌈(o + o * ρ) * 2 ^ 48⌉ : ℚ) / 2 ^ 48

/-- The integer cell of the bottom walk. -/
def strainBottomCell (c z₁ x x' : ℚ) : Option ℤ :=
  match strainBottomBound c z₁ x x' with
  | some U => some (ceilScaled 64 U)
  | none => none

/-- **The bottom check**: the walk over `[1/2 + 2^-31, 2^30] × (0, 2^-17]`. -/
def strainBottomSlab : Option ℤ :=
  let fb := thresholdGuess true strainBottomHeight
  if decide (0 ≤ fb) && decide (strainQuarticRat fb strainBottomHeight < 0) then
    cellWalk strainBottomNext (strainBottomCell fb strainBottomHeight) 100000
      (1 / 2 + strainCornerWidth) strainWalkEnd 0
  else none

/-- **Soundness of the bottom check**: a value `N` bounds the cost over
`(0, 2^-17] × (1/2 + 2^-31, 2^30]` by `N/2^64`. -/
theorem lintegral_le_strainBottomSlab {N : ℤ} (h : strainBottomSlab = some N) :
    ∫⁻ s₂ in Ioc (0 : ℝ) strainBottomHeight, ∫⁻ s₁ in Ioc ((1 / 2 + strainCornerWidth : ℚ) : ℝ)
      strainWalkEnd, strainCostIntegrand s₂ s₁ ≤ ENNReal.ofReal (N / 2 ^ 64) := by
  unfold strainBottomSlab at h
  dsimp only at h
  split_ifs at h with hck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨hfb0, hfb⟩ := hck
  have hfb' : strainThreshold strainBottomHeight ≤
      ((thresholdGuess true strainBottomHeight : ℚ) : ℝ) := strainThreshold_le_of_quartic hfb0
    (cast_strainQuarticRat _ strainBottomHeight ▸ Rat.cast_lt_zero.2 hfb)
  have := le_of_cellWalk_of_subadditive
    (Φ := fun a b ↦ ∫⁻ s₂ in Ioc (0 : ℝ) strainBottomHeight, ∫⁻ s₁ in Ioc a b,
      strainCostIntegrand s₂ s₁)
    (g := fun q : ℚ ↦ (q : ℝ)) (K := 64)
    (fun a ha b hb hab ↦ Rat.cast_le.2 hab)
    (fun _ _ _ _ _ ↦ lintegral_lintegral_le_add _)
    (fun a b hba ↦ by simp [Ioc_eq_empty (not_lt.2 hba)])
    (fun l u m hl hlu hm ↦ by
      unfold strainBottomCell at hm
      split at hm
      · rename_i U hU
        obtain rfl := Option.some.inj hm
        exact (lintegral_le_strainBottomBound hfb' hU).trans
          (ENNReal.ofReal_le_ofReal (le_ceilScaled_real 64 U))
      · simp at hm) (by norm_num [strainCornerWidth]) (by norm_num [strainWalkEnd]) h
  simpa using this

/-- The next height of the walk over slabs, `z (1 + 3/32)` on the grid `2^-48`. -/
def strainSlabHeightNext (z : ℚ) : ℚ := (⌈(z + z * (3 / 32)) * 2 ^ 48⌉ : ℚ) / 2 ^ 48

/-- **The walk over slabs** from `z_A` to `z_B`. -/
def strainSlabWalk (zA zB : ℚ) : Option ℤ :=
  cellWalk strainSlabHeightNext strainSlab 10000 zA zB 0

/-- **Soundness of the walk over slabs**: for `0 ≤ z_A, z_B`, a walk value `N` bounds the cost
over `(z_A, z_B] × (-∞, 2^30]` by `N/2^64`. -/
theorem lintegral_le_strainSlabWalk {zA zB : ℚ} {N : ℤ} (hA : 0 ≤ zA) (hB : 0 ≤ zB)
    (h : strainSlabWalk zA zB = some N) :
    ∫⁻ s₂ in Ioc (zA : ℝ) zB, ∫⁻ s₁ in Iic (strainWalkEnd : ℝ), strainCostIntegrand s₂ s₁ ≤
      ENNReal.ofReal (N / 2 ^ 64) := by
  have := lintegral_le_of_cellWalk (F := fun s₂ ↦ ∫⁻ s₁ in Iic (strainWalkEnd : ℝ),
      strainCostIntegrand s₂ s₁) (g := fun q : ℚ ↦ (q : ℝ)) (K := 64)
    (fun a ha b hb hab ↦ Rat.cast_le.2 hab)
    (fun l u m hl hlu hm ↦ lintegral_le_strainSlab hm) hA hB h
  simpa using this

/-- The check that a walk succeeded with a bound at most `q`. -/
def walkLe (o : Option ℤ) (q : ℚ) : Bool :=
  match o with
  | some n => decide ((n : ℚ) / 2 ^ 64 ≤ q)
  | none => false

/-- A walk that passes `walkLe o q` returned some `n` with `n/2^64 ≤ q`. -/
theorem walkLe_spec {o : Option ℤ} {q : ℚ} (h : walkLe o q = true) :
    ∃ n : ℤ, o = some n ∧ (n : ℝ) / 2 ^ 64 ≤ q := by
  cases o with
  | none => simp [walkLe] at h
  | some n =>
    refine ⟨n, rfl, ?_⟩
    simp only [walkLe, decide_eq_true_eq] at h
    exact_mod_cast h

/-- The bottom slab with its corner strip. -/
theorem lintegral_bottom_le {N : ℤ} (h : strainBottomSlab = some N) :
    ∫⁻ s₂ in Ioc (0 : ℝ) strainBottomHeight, ∫⁻ s₁ in Iic (strainWalkEnd : ℝ),
        strainCostIntegrand s₂ s₁ ≤
      ENNReal.ofReal (1 / 2 ^ 15) + ENNReal.ofReal (N / 2 ^ 64) := by
  have hc : ((1 / 2 + strainCornerWidth : ℚ) : ℝ) = 1 / 2 + 1 / 2 ^ 31 := by
    simp [strainCornerWidth]
  have hsplit : ∀ s₂ ∈ Ioc (0 : ℝ) strainBottomHeight, ∫⁻ s₁ in Iic (strainWalkEnd : ℝ),
      strainCostIntegrand s₂ s₁ ≤
        (∫⁻ s₁ in Ioc (1 / 2 : ℝ) (1 / 2 + 1 / 2 ^ 31), strainCostIntegrand s₂ s₁) +
          ∫⁻ s₁ in Ioc ((1 / 2 + strainCornerWidth : ℚ) : ℝ) strainWalkEnd,
            strainCostIntegrand s₂ s₁ := by
    intro s₂ hs₂
    have h0 : ∫⁻ s₁ in Iic (1 / 2 : ℝ), strainCostIntegrand s₂ s₁ = 0 := by
      rw [setLIntegral_congr_fun (measurableSet_Iic : MeasurableSet (Iic (1 / 2 : ℝ)))
        (g := fun _ ↦ 0) (fun t ht ↦ by
          unfold strainCostIntegrand
          exact indicator_of_notMem (by
            simp only [mem_Ioi, not_lt]
            exact (show t ≤ 1 / 2 from ht).trans (one_half_le_strainThreshold _)) _)]
      simp
    calc ∫⁻ s₁ in Iic (strainWalkEnd : ℝ), strainCostIntegrand s₂ s₁
        = ∫⁻ s₁ in Iic (1 / 2 : ℝ) ∪ (Ioc (1 / 2 : ℝ) (1 / 2 + 1 / 2 ^ 31) ∪
            Ioc ((1 / 2 + strainCornerWidth : ℚ) : ℝ) strainWalkEnd),
              strainCostIntegrand s₂ s₁ := by
          rw [hc, Ioc_union_Ioc_eq_Ioc (by norm_num) (by norm_num [strainWalkEnd]),
            Iic_union_Ioc_eq_Iic (by norm_num [strainWalkEnd])]
      _ ≤ (∫⁻ s₁ in Iic (1 / 2 : ℝ), strainCostIntegrand s₂ s₁) +
            ((∫⁻ s₁ in Ioc (1 / 2 : ℝ) (1 / 2 + 1 / 2 ^ 31), strainCostIntegrand s₂ s₁) +
              ∫⁻ s₁ in Ioc ((1 / 2 + strainCornerWidth : ℚ) : ℝ) strainWalkEnd,
                strainCostIntegrand s₂ s₁) :=
          (lintegral_union_le _ _ _).trans (add_le_add le_rfl (lintegral_union_le _ _ _))
      _ = _ := by rw [h0, zero_add]
  have hcorner := lintegral_strainCostIntegrand_corner_le (z₁ := (strainBottomHeight : ℝ))
    (show (0 : ℝ) < 1 / 2 ^ 31 by norm_num)
  have hsq : Real.sqrt (2 * (1 / 2 ^ 31 : ℝ)) = 1 / 2 ^ 15 := by
    rw [show (2 : ℝ) * (1 / 2 ^ 31) = (1 / 2 ^ 15) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [hsq] at hcorner
  calc ∫⁻ s₂ in Ioc (0 : ℝ) strainBottomHeight, ∫⁻ s₁ in Iic (strainWalkEnd : ℝ),
        strainCostIntegrand s₂ s₁
      ≤ ∫⁻ s₂ in Ioc (0 : ℝ) strainBottomHeight,
          ((∫⁻ s₁ in Ioc (1 / 2 : ℝ) (1 / 2 + 1 / 2 ^ 31), strainCostIntegrand s₂ s₁) +
            ∫⁻ s₁ in Ioc ((1 / 2 + strainCornerWidth : ℚ) : ℝ) strainWalkEnd,
              strainCostIntegrand s₂ s₁) := setLIntegral_mono' measurableSet_Ioc hsplit
    _ = (∫⁻ s₂ in Ioc (0 : ℝ) strainBottomHeight,
          ∫⁻ s₁ in Ioc (1 / 2 : ℝ) (1 / 2 + 1 / 2 ^ 31), strainCostIntegrand s₂ s₁) +
        ∫⁻ s₂ in Ioc (0 : ℝ) strainBottomHeight,
          ∫⁻ s₁ in Ioc ((1 / 2 + strainCornerWidth : ℚ) : ℝ) strainWalkEnd,
            strainCostIntegrand s₂ s₁ :=
        lintegral_add_left (measurable_lintegral_strainCostIntegrand _) _
    _ ≤ _ := add_le_add hcorner (lintegral_le_strainBottomSlab h)

end IncompressibleFlow.SharpHolder
