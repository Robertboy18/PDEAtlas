/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearCostCells
public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.StrainConstantCells

/-!
# The rational cells of the shear column cost

The cell walk of the shear column cost runs over slabs `[t₀, t₁]` in the height and, in each
slab, over cells `[p₀, p₁] × [t₀, t₁]` in the column variable to the right of `p = 1`, up to the
sign threshold `h⁺(t₀)`. On a cell the evaluator

* checks that the sign quartic is `≤ 0` at the two lower corners (`shearQuartic_le_max`);
* certifies `T₀ ≤ T(p₀, t₁)` and `T(p₁, t₀) ≤ T₁` by the sign of the cubic at candidates from
  Newton's method in rationals (`shearMapLow`, `shearMapApprox`);
* forms the affine majorant of `sub_shearMap_le_affine_right` with the slopes `shearSlopesRight`;
* bounds the corner sums of `integral_integral_shearDifference_affine` by rational enclosures of
  the arctangents (`atanPair`) and of the logarithms (`logLow`, `logHigh`);
* and returns the smaller of the first-order value `(t₁ - T₀ + r²)/(2r)` times the mass and the
  second-order value (`shearCellRight`).

The band between `h⁺(t₀)` and `h⁺(t₁)` is a strip bounded by its area (`shearStripRight`), and to
the right of `h⁺(t₁)` the density vanishes.

## Main definitions

* `shearMapApprox`, `shearMapLow`: Newton approximations of the transport map `T(p, t)` in
  rationals.
* `shearCellRight`: the bound of a cell `[p₀, p₁] × [t₀, t₁]` to the right of `p = 1`.
* `shearStripRight`: the bound of the band at the threshold, its area times a bound of the
  density.
* `shearSlabRight`: the bound of a slab `[t₀, t₁]`, cells up to `h⁺(t₀)` and the strip beyond.
* `shearOuterWalk`: the walk over slabs from `t_A` to `t_B`.

## Main results

* `le_shearMap_of_shearLowOk`, `shearMap_le_of_shearHighOk`: for `t > 0`, candidates passing the
  cubic sign checks are lower and upper bounds of `T(p, t)`.
* `lintegral_le_shearCellRight`: the cell bound bounds the cost over the cell.
* `lintegral_le_shearStripRight`: the strip value bounds the cost over the band.
* `lintegral_le_shearSlabRight`: the slab value bounds the cost over the slab.
* `lintegral_le_shearOuterWalk`: for `0 ≤ t_A, t_B`, a walk value `N` bounds
  `∫_{(t_A, t_B]} ∫_{p > 1} shearColumnDensity p t` by `N/2^64`.
* `lintegral_le_of_shearOuterCheck`: a decided walk of the outer columns bounds the heights it
  covers.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory PDE.Analysis
open scoped ENNReal

namespace IncompressibleFlow.SharpHolder

/-! ### The map and the quartic over the rationals -/

/-- `t P(p, t, T)` over the rationals. -/
def shearCubicRat (p t T : ℚ) : ℚ :=
  t * T ^ 3 + t ^ 2 * T ^ 2 + t * T * (t ^ 2 + 2 + 2 * p ^ 2) - (p ^ 2 - 1) ^ 2

/-- For `t ≠ 0`, `shearCubicRat p t T` is `t P(p, t, T)` over the reals. -/
theorem cast_shearCubicRat {t : ℚ} (ht : t ≠ 0) (p T : ℚ) :
    ((shearCubicRat p t T : ℚ) : ℝ) = t * shearCubic p t T := by
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  rw [mul_shearCubic_eq _ ht']
  simp only [shearCubicRat]
  push_cast
  ring

/-- The derivative in `T` of `shearCubicRat`. -/
def shearCubicRatDeriv (p t T : ℚ) : ℚ :=
  3 * t * T ^ 2 + 2 * t ^ 2 * T + t * (t ^ 2 + 2 + 2 * p ^ 2)

/-- Newton's method for the root of the cubic from above, rounded up to about fifty bits. -/
def shearNewton (p t : ℚ) : ℕ → ℚ → ℚ
  | 0, T => T
  | n + 1, T =>
    let d := shearCubicRatDeriv p t T
    if 0 < d then
      let T' := roundUpRel (T - shearCubicRat p t T / d)
      if T' < T - T / 2 ^ 46 then shearNewton p t n T' else min T T'
    else T

/-- The Newton approximation of `T(p, t)` from the upper bound `(p² - 1)² / (t (t² + 2 + 2 p²))`. -/
def shearMapApprox (p t : ℚ) : ℚ :=
  shearNewton p t 60 (roundUpRel ((p ^ 2 - 1) ^ 2 / (t * (t ^ 2 + 2 + 2 * p ^ 2))))

/-- The candidate lower bound of `T(p, t)`. -/
def shearMapLow (p t : ℚ) : ℚ :=
  max 0 (roundDownRel (shearMapApprox p t - shearMapApprox p t / 2 ^ 40))

/-- The check of a lower bound `T` of `T(p, t)`. -/
def shearLowOk (p t T : ℚ) : Bool :=
  decide (T = 0) || (decide (0 ≤ T) && decide (shearCubicRat p t T ≤ 0))

/-- The check of an upper bound `T` of `T(p, t)`. -/
def shearHighOk (p t T : ℚ) : Bool :=
  decide (0 ≤ T) && decide (0 ≤ shearCubicRat p t T)

/-- For `t > 0`, a candidate `T` that passes `shearLowOk` is a lower bound: `T ≤ T(p, t)`. -/
theorem le_shearMap_of_shearLowOk {p t T : ℚ} (ht : 0 < t) (h : shearLowOk p t T = true) :
    (T : ℝ) ≤ shearMap p t := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  simp only [shearLowOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨h0, h⟩
  · rw [h]
    push_cast
    exact shearMap_nonneg ht'
  · refine le_shearMap_of_shearCubic_nonpos ht' (by exact_mod_cast h0) ?_
    have h' : ((shearCubicRat p t T : ℚ) : ℝ) ≤ 0 := by exact_mod_cast h
    rw [cast_shearCubicRat ht.ne'] at h'
    by_contra hc
    push Not at hc
    have := mul_pos ht' hc
    linarith

/-- For `t > 0`, a candidate `T` that passes `shearHighOk` is an upper bound: `T(p, t) ≤ T`. -/
theorem shearMap_le_of_shearHighOk {p t T : ℚ} (ht : 0 < t) (h : shearHighOk p t T = true) :
    shearMap p t ≤ T := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  simp only [shearHighOk, Bool.and_eq_true, decide_eq_true_eq] at h
  refine shearMap_le_of_shearCubic_nonneg ht' (by exact_mod_cast h.1) ?_
  have h' : (0 : ℝ) ≤ ((shearCubicRat p t T : ℚ) : ℝ) := by exact_mod_cast h.2
  rw [cast_shearCubicRat ht.ne'] at h'
  exact nonneg_of_mul_nonneg_right (by linarith) ht'

/-- The sign quartic over the rationals. -/
def shearQuarticRat (p t : ℚ) : ℚ :=
  p ^ 4 - 2 * p ^ 2 * t ^ 2 - 2 * p ^ 2 - 3 * t ^ 4 - 2 * t ^ 2 + 1

/-- `shearQuarticRat p t` is the sign quartic `Q(p, t)` over the reals. -/
theorem cast_shearQuarticRat (p t : ℚ) :
    ((shearQuarticRat p t : ℚ) : ℝ) = shearQuartic p t := by
  simp only [shearQuarticRat, shearQuartic]
  push_cast
  ring

/-! ### Enclosures of the corner sums -/

/-- The argument of the angular corner sum `cornerSum_shearAngle_eq`. -/
def shearAngleArg (a₀ a₁ t₀ t₁ : ℚ) : ℚ :=
  (a₁ - a₀) * (t₁ - t₀) * (a₀ * a₁ - t₀ * t₁) /
    ((t₁ ^ 2 + a₀ * a₁) * (t₀ ^ 2 + a₀ * a₁) + t₀ * t₁ * (a₁ - a₀) ^ 2)

/-- An enclosure of the angular corner sum `cornerSum (arctan (a/t)/2)`. -/
def shearAnglePair (a₀ a₁ t₀ t₁ : ℚ) : ℚ × ℚ :=
  let e := atanPair (shearAngleArg a₀ a₁ t₀ t₁)
  (e.1 / 2, e.2 / 2)

/-- For `0 < t₀ ≤ t₁`, `a₀ ≤ a₁` and `a₀ a₁ ≥ 0`, `shearAnglePair` encloses the corner sum of
`arctan (a/t)/2` over `[a₀, a₁] × [t₀, t₁]`. -/
theorem shearAnglePair_spec {a₀ a₁ t₀ t₁ : ℚ} (ht₀ : 0 < t₀) (ht : t₀ ≤ t₁) (ha : a₀ ≤ a₁)
    (h : 0 ≤ a₀ * a₁) :
    ((shearAnglePair a₀ a₁ t₀ t₁).1 : ℝ) ≤
        cornerSum (fun a t ↦ Real.arctan (a / t) / 2) a₀ a₁ t₀ t₁ ∧
      cornerSum (fun a t ↦ Real.arctan (a / t) / 2) a₀ a₁ t₀ t₁ ≤
        (shearAnglePair a₀ a₁ t₀ t₁).2 := by
  have e := cornerSum_shearAngle_eq (a₀ := a₀) (a₁ := a₁) (t₀ := t₀) (t₁ := t₁)
    (by exact_mod_cast ht₀) (by exact_mod_cast ht) (by exact_mod_cast ha) (by exact_mod_cast h)
  have harg : ((shearAngleArg a₀ a₁ t₀ t₁ : ℚ) : ℝ) =
      ((a₁ : ℝ) - a₀) * (t₁ - t₀) * (a₀ * a₁ - t₀ * t₁) /
        ((t₁ ^ 2 + a₀ * a₁) * (t₀ ^ 2 + a₀ * a₁) + t₀ * t₁ * (a₁ - a₀) ^ 2) := by
    simp only [shearAngleArg]
    push_cast
    ring
  rw [e, ← harg]
  have h1 := atanPair_fst_le (shearAngleArg a₀ a₁ t₀ t₁)
  have h2 := le_atanPair_snd (shearAngleArg a₀ a₁ t₀ t₁)
  simp only [shearAnglePair]
  push_cast
  constructor <;> linarith

/-- An enclosure of the corner sum of `(t/4) log (a² + t²)`. -/
def shearLogTPair (a₀ a₁ t₀ t₁ : ℚ) : ℚ × ℚ :=
  let R₁ := (a₁ ^ 2 + t₁ ^ 2) / (a₀ ^ 2 + t₁ ^ 2)
  let R₀ := (a₁ ^ 2 + t₀ ^ 2) / (a₀ ^ 2 + t₀ ^ 2)
  (t₁ / 4 * logLow R₁ - t₀ / 4 * logHigh R₀, t₁ / 4 * logHigh R₁ - t₀ / 4 * logLow R₀)

/-- For `0 < t₀ ≤ t₁`, `shearLogTPair` encloses the corner sum of `(t/4) log (a² + t²)` over
`[a₀, a₁] × [t₀, t₁]`. -/
theorem shearLogTPair_spec {a₀ a₁ t₀ t₁ : ℚ} (ht₀ : 0 < t₀) (ht : t₀ ≤ t₁) :
    ((shearLogTPair a₀ a₁ t₀ t₁).1 : ℝ) ≤
        cornerSum (fun a t ↦ t / 4 * Real.log (a ^ 2 + t ^ 2)) a₀ a₁ t₀ t₁ ∧
      cornerSum (fun a t ↦ t / 4 * Real.log (a ^ 2 + t ^ 2)) a₀ a₁ t₀ t₁ ≤
        (shearLogTPair a₀ a₁ t₀ t₁).2 := by
  have ht₁ : 0 < t₁ := ht₀.trans_le ht
  rw [cornerSum_shearLogT_eq (by exact_mod_cast ht₀) (by exact_mod_cast ht)]
  have hR₁ : 0 < (a₁ ^ 2 + t₁ ^ 2) / (a₀ ^ 2 + t₁ ^ 2) := by positivity
  have hR₀ : 0 < (a₁ ^ 2 + t₀ ^ 2) / (a₀ ^ 2 + t₀ ^ 2) := by positivity
  have l₁ := logLow_le hR₁
  have u₁ := le_logHigh hR₁
  have l₀ := logLow_le hR₀
  have u₀ := le_logHigh hR₀
  push_cast at l₁ u₁ l₀ u₀
  have ht₀' : (0 : ℝ) < t₀ := by exact_mod_cast ht₀
  have ht₁' : (0 : ℝ) < t₁ := by exact_mod_cast ht₁
  simp only [shearLogTPair]
  push_cast
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left l₁ ht₁'.le, mul_le_mul_of_nonneg_left u₀ ht₀'.le]
  · nlinarith [mul_le_mul_of_nonneg_left u₁ ht₁'.le, mul_le_mul_of_nonneg_left l₀ ht₀'.le]

/-- An enclosure of the corner sum of `(a/4) log (a² + t²)`. -/
def shearLogAPair (a₀ a₁ t₀ t₁ : ℚ) : ℚ × ℚ :=
  let S₁ := (a₁ ^ 2 + t₁ ^ 2) / (a₁ ^ 2 + t₀ ^ 2)
  let S₀ := (a₀ ^ 2 + t₁ ^ 2) / (a₀ ^ 2 + t₀ ^ 2)
  let l₁ := logLow S₁
  let h₁ := logHigh S₁
  let l₀ := logLow S₀
  let h₀ := logHigh S₀
  (mulLow (a₁ / 4) l₁ h₁ - mulHigh (a₀ / 4) l₀ h₀, mulHigh (a₁ / 4) l₁ h₁ - mulLow (a₀ / 4) l₀ h₀)

/-- For `0 < t₀ ≤ t₁`, `shearLogAPair` encloses the corner sum of `(a/4) log (a² + t²)` over
`[a₀, a₁] × [t₀, t₁]`. -/
theorem shearLogAPair_spec {a₀ a₁ t₀ t₁ : ℚ} (ht₀ : 0 < t₀) (ht : t₀ ≤ t₁) :
    ((shearLogAPair a₀ a₁ t₀ t₁).1 : ℝ) ≤
        cornerSum (fun a t ↦ a / 4 * Real.log (a ^ 2 + t ^ 2)) a₀ a₁ t₀ t₁ ∧
      cornerSum (fun a t ↦ a / 4 * Real.log (a ^ 2 + t ^ 2)) a₀ a₁ t₀ t₁ ≤
        (shearLogAPair a₀ a₁ t₀ t₁).2 := by
  have ht₁ : 0 < t₁ := ht₀.trans_le ht
  rw [cornerSum_shearLogA_eq (by exact_mod_cast ht₀) (by exact_mod_cast ht)]
  have hS₁ : 0 < (a₁ ^ 2 + t₁ ^ 2) / (a₁ ^ 2 + t₀ ^ 2) := by positivity
  have hS₀ : 0 < (a₀ ^ 2 + t₁ ^ 2) / (a₀ ^ 2 + t₀ ^ 2) := by positivity
  have l₁ := logLow_le hS₁
  have u₁ := le_logHigh hS₁
  have l₀ := logLow_le hS₀
  have u₀ := le_logHigh hS₀
  push_cast at l₁ u₁ l₀ u₀
  have c₁ := mulLow_le_mul (c := a₁ / 4) l₁ u₁
  have d₁ := mul_le_mulHigh (c := a₁ / 4) l₁ u₁
  have c₀ := mulLow_le_mul (c := a₀ / 4) l₀ u₀
  have d₀ := mul_le_mulHigh (c := a₀ / 4) l₀ u₀
  push_cast at c₁ d₁ c₀ d₀
  simp only [shearLogAPair]
  push_cast
  constructor <;> linarith

/-- An enclosure of `cornerSum (shearCorner α β γ)`. -/
def shearCornerPair (α β γ a₀ a₁ t₀ t₁ : ℚ) : ℚ × ℚ :=
  let A := shearAnglePair a₀ a₁ t₀ t₁
  let L := shearLogTPair a₀ a₁ t₀ t₁
  let G := shearLogAPair a₀ a₁ t₀ t₁
  (mulLow α A.1 A.2 + mulLow β L.1 L.2 - mulHigh γ G.1 G.2,
    mulHigh α A.1 A.2 + mulHigh β L.1 L.2 - mulLow γ G.1 G.2)

/-- For `0 < t₀ ≤ t₁`, `a₀ ≤ a₁` and `a₀ a₁ ≥ 0`, `shearCornerPair α β γ` encloses
`cornerSum (shearCorner α β γ)` over `[a₀, a₁] × [t₀, t₁]`. -/
theorem shearCornerPair_spec (α β γ : ℚ) {a₀ a₁ t₀ t₁ : ℚ} (ht₀ : 0 < t₀) (ht : t₀ ≤ t₁)
    (ha : a₀ ≤ a₁) (h : 0 ≤ a₀ * a₁) :
    ((shearCornerPair α β γ a₀ a₁ t₀ t₁).1 : ℝ) ≤ cornerSum (shearCorner α β γ) a₀ a₁ t₀ t₁ ∧
      cornerSum (shearCorner α β γ) a₀ a₁ t₀ t₁ ≤ (shearCornerPair α β γ a₀ a₁ t₀ t₁).2 := by
  obtain ⟨A₁, A₂⟩ := shearAnglePair_spec ht₀ ht ha h
  obtain ⟨L₁, L₂⟩ := shearLogTPair_spec (a₀ := a₀) (a₁ := a₁) ht₀ ht
  obtain ⟨G₁, G₂⟩ := shearLogAPair_spec (a₀ := a₀) (a₁ := a₁) ht₀ ht
  have a₁ := mulLow_le_mul (c := α) A₁ A₂
  have a₂ := mul_le_mulHigh (c := α) A₁ A₂
  have b₁ := mulLow_le_mul (c := β) L₁ L₂
  have b₂ := mul_le_mulHigh (c := β) L₁ L₂
  have g₁ := mulLow_le_mul (c := γ) G₁ G₂
  have g₂ := mul_le_mulHigh (c := γ) G₁ G₂
  rw [cornerSum_shearCorner]
  simp only [shearCornerPair]
  push_cast
  constructor <;> linarith

/-- The upper bound of the cell integral `∫∫ Δ (α + β p + γ t)`. -/
def shearCellHigh (α β γ p₀ p₁ t₀ t₁ : ℚ) : ℚ :=
  (shearCornerPair (α - β) β γ (p₀ + 1) (p₁ + 1) t₀ t₁).2 -
    (shearCornerPair (α + β) β γ (p₀ - 1) (p₁ - 1) t₀ t₁).1

/-- On a cell `[p₀, p₁] × [t₀, t₁]` with `0 ≤ p₀`, `(p₀ - 1)(p₁ - 1) ≥ 0` and `t₀ > 0`, the corner
sum of the two shifted primitives of `Δ (α + β p + γ t)` is at most `shearCellHigh`. -/
theorem cornerSum_le_shearCellHigh (α β γ : ℚ) {p₀ p₁ t₀ t₁ : ℚ} (hp₀ : 0 ≤ p₀) (hp : p₀ ≤ p₁)
    (h1 : 0 ≤ (p₀ - 1) * (p₁ - 1)) (ht₀ : 0 < t₀) (ht : t₀ ≤ t₁) :
    cornerSum (fun p t ↦ shearCorner ((α : ℝ) - β) β γ (p + 1) t -
        shearCorner ((α : ℝ) + β) β γ (p - 1) t) p₀ p₁ t₀ t₁ ≤
      shearCellHigh α β γ p₀ p₁ t₀ t₁ := by
  have hplus := (shearCornerPair_spec (α - β) β γ (a₀ := p₀ + 1) (a₁ := p₁ + 1) ht₀ ht
    (by linarith) (mul_nonneg (by linarith) (by linarith))).2
  have hminus := (shearCornerPair_spec (α + β) β γ (a₀ := p₀ - 1) (a₁ := p₁ - 1) ht₀ ht
    (by linarith) h1).1
  push_cast at hplus hminus
  have e : cornerSum (fun p t ↦ shearCorner ((α : ℝ) - β) β γ (p + 1) t -
        shearCorner ((α : ℝ) + β) β γ (p - 1) t) p₀ p₁ t₀ t₁ =
      cornerSum (shearCorner ((α : ℝ) - β) β γ) ((p₀ : ℝ) + 1) (p₁ + 1) t₀ t₁ -
        cornerSum (shearCorner ((α : ℝ) + β) β γ) ((p₀ : ℝ) - 1) (p₁ - 1) t₀ t₁ := by
    simp only [cornerSum]
    ring
  rw [e]
  simp only [shearCellHigh]
  push_cast
  linarith

/-- The upper bound of the mass `∫∫ Δ` of a cell. -/
def shearMassHigh (p₀ p₁ t₀ t₁ : ℚ) : ℚ :=
  (shearAnglePair (p₀ + 1) (p₁ + 1) t₀ t₁).2 - (shearAnglePair (p₀ - 1) (p₁ - 1) t₀ t₁).1

/-- The lower bound of the mass `∫∫ Δ` of a cell. -/
def shearMassLow (p₀ p₁ t₀ t₁ : ℚ) : ℚ :=
  (shearAnglePair (p₀ + 1) (p₁ + 1) t₀ t₁).1 - (shearAnglePair (p₀ - 1) (p₁ - 1) t₀ t₁).2

/-- On a cell on one side of `p = 1` and for `α ≥ 0`, the corner sum of the primitives of `α Δ`
is at most `α shearMassHigh`. -/
theorem cornerSum_le_mul_shearMassHigh {α : ℚ} (hα : 0 ≤ α) {p₀ p₁ t₀ t₁ : ℚ} (hp₀ : 0 ≤ p₀)
    (hp : p₀ ≤ p₁) (h1 : 0 ≤ (p₀ - 1) * (p₁ - 1)) (ht₀ : 0 < t₀) (ht : t₀ ≤ t₁) :
    cornerSum (fun p t ↦ shearCorner ((α : ℝ) - 0) 0 0 (p + 1) t -
        shearCorner ((α : ℝ) + 0) 0 0 (p - 1) t) p₀ p₁ t₀ t₁ ≤
      α * shearMassHigh p₀ p₁ t₀ t₁ := by
  have hplus := (shearAnglePair_spec (a₀ := p₀ + 1) (a₁ := p₁ + 1) ht₀ ht (by linarith)
    (mul_nonneg (by linarith) (by linarith))).2
  have hminus := (shearAnglePair_spec (a₀ := p₀ - 1) (a₁ := p₁ - 1) ht₀ ht (by linarith) h1).1
  push_cast at hplus hminus
  have e : cornerSum (fun p t ↦ shearCorner ((α : ℝ) - 0) 0 0 (p + 1) t -
        shearCorner ((α : ℝ) + 0) 0 0 (p - 1) t) p₀ p₁ t₀ t₁ =
      α * (cornerSum (fun a t ↦ Real.arctan (a / t) / 2) ((p₀ : ℝ) + 1) (p₁ + 1) t₀ t₁ -
        cornerSum (fun a t ↦ Real.arctan (a / t) / 2) ((p₀ : ℝ) - 1) (p₁ - 1) t₀ t₁) := by
    simp only [cornerSum, shearCorner]
    ring
  rw [e]
  simp only [shearMassHigh]
  push_cast
  exact mul_le_mul_of_nonneg_left (by linarith) (by exact_mod_cast hα)

/-! ### Cells to the right of `p = 1` -/

/-- `max 0 (roundDownRel (C / H)) H ≤ C` for `C ≥ 0` and `H > 0`. -/
theorem max_roundDownRel_div_mul_le {C H : ℚ} (hC : 0 ≤ C) (hH : 0 < H) :
    max 0 (roundDownRel (C / H)) * H ≤ C := by
  rcases le_total (roundDownRel (C / H)) 0 with h | h
  · rw [max_eq_left h, zero_mul]
    exact hC
  · rw [max_eq_right h]
    calc roundDownRel (C / H) * H ≤ C / H * H :=
          mul_le_mul_of_nonneg_right (roundDownRel_le _) hH.le
      _ = C := div_mul_cancel₀ C hH.ne'

/-- The slopes `(λ, μ)` of the affine majorant to the right of `p = 1`. -/
def shearSlopesRight (p₀ p₁ t₀ t₁ T₀ T₁ : ℚ) : ℚ × ℚ :=
  let H := t₁ * (3 * T₁ ^ 2 + 2 * t₁ * T₁ + t₁ ^ 2 + (2 + 2 * p₁ ^ 2))
  (max 0 (roundDownRel (T₀ * (3 * t₀ ^ 2 + 2 * T₀ * t₀ + T₀ ^ 2 + (2 + 2 * p₀ ^ 2)) / H)),
    max 0 (roundDownRel (2 * p₀ * max 0 (2 * p₀ ^ 2 - 2 - 2 * t₁ * T₁) / H)))

/-- The slopes `(λ, μ)` are nonnegative, and their products with
`H = t₁ (3 T₁² + 2 t₁ T₁ + t₁² + 2 + 2 p₁²)` are at most `T₀ (3 t₀² + 2 T₀ t₀ + T₀² + 2 + 2 p₀²)`
and `2 p₀ max(0, 2 p₀² - 2 - 2 t₁ T₁)`. -/
theorem shearSlopesRight_spec {p₀ p₁ t₀ t₁ T₀ T₁ : ℚ} (hp₀ : 0 ≤ p₀) (ht₁ : 0 < t₁)
    (hT₀ : 0 ≤ T₀) (hT₁ : 0 ≤ T₁) :
    0 ≤ (shearSlopesRight p₀ p₁ t₀ t₁ T₀ T₁).1 ∧ 0 ≤ (shearSlopesRight p₀ p₁ t₀ t₁ T₀ T₁).2 ∧
      ((shearSlopesRight p₀ p₁ t₀ t₁ T₀ T₁).1 : ℝ) *
          (t₁ * (3 * T₁ ^ 2 + 2 * t₁ * T₁ + t₁ ^ 2 + (2 + 2 * p₁ ^ 2))) ≤
        T₀ * (3 * t₀ ^ 2 + 2 * T₀ * t₀ + T₀ ^ 2 + (2 + 2 * p₀ ^ 2)) ∧
      ((shearSlopesRight p₀ p₁ t₀ t₁ T₀ T₁).2 : ℝ) *
          (t₁ * (3 * T₁ ^ 2 + 2 * t₁ * T₁ + t₁ ^ 2 + (2 + 2 * p₁ ^ 2))) ≤
        2 * (p₀ : ℝ) * max 0 (2 * (p₀ : ℝ) ^ 2 - 2 - 2 * t₁ * T₁) := by
  have hH : 0 < t₁ * (3 * T₁ ^ 2 + 2 * t₁ * T₁ + t₁ ^ 2 + (2 + 2 * p₁ ^ 2)) :=
    mul_pos ht₁ (by nlinarith [sq_nonneg T₁, sq_nonneg t₁, sq_nonneg p₁, mul_nonneg ht₁.le hT₁])
  have h₁ := max_roundDownRel_div_mul_le
    (C := T₀ * (3 * t₀ ^ 2 + 2 * T₀ * t₀ + T₀ ^ 2 + (2 + 2 * p₀ ^ 2)))
    (mul_nonneg hT₀ (by nlinarith [sq_nonneg (T₀ + t₀), sq_nonneg t₀, sq_nonneg p₀])) hH
  have h₂ := max_roundDownRel_div_mul_le
    (C := 2 * p₀ * max 0 (2 * p₀ ^ 2 - 2 - 2 * t₁ * T₁))
    (mul_nonneg (by linarith) (le_max_left _ _)) hH
  refine ⟨le_max_left _ _, le_max_left _ _, ?_, ?_⟩ <;> simp only [shearSlopesRight]
  · exact_mod_cast h₁
  · exact_mod_cast h₂

/-- The first-order value `(c₀ + r²)/(2r)` times the mass, `c₀ = t₁ - T₀`. -/
def shearFirstValue (p₀ p₁ t₀ t₁ T₀ : ℚ) : ℚ :=
  (t₁ - T₀ + sqrtApproxRel (t₁ - T₀) ^ 2) / (2 * sqrtApproxRel (t₁ - T₀)) *
    shearMassHigh p₀ p₁ t₀ t₁

/-- The radius of the second-order value: the square root of the majorant at the centre. -/
def shearRadius (p₀ p₁ t₀ t₁ c₀ c₁ m : ℚ) : ℚ :=
  sqrtApproxRel (max (c₀ / 4) (c₀ - c₁ * (t₁ - t₀) / 2 - m * (p₁ - p₀) / 2))

/-- The second-order value of a cell to the right of `p = 1` with the slopes `λ, μ`. -/
def shearSecondValueRight (p₀ p₁ t₀ t₁ T₀ l m : ℚ) : ℚ :=
  let c₀ := t₁ - T₀
  let c₁ := 1 + l
  let r := shearRadius p₀ p₁ t₀ t₁ c₀ c₁ m
  shearCellHigh ((c₀ - c₁ * t₁ + m * p₀ + r ^ 2) / (2 * r)) (-m / (2 * r)) (c₁ / (2 * r))
    p₀ p₁ t₀ t₁

/-- **The cell bound** of `[p₀, p₁] × [t₀, t₁]` to the right of `p = 1`, after the checks. -/
def shearCellRight (t₀ t₁ p₀ p₁ : ℚ) : Option ℤ :=
  let T₀ := shearMapLow p₀ t₁
  let T₁ := shearMapApprox p₁ t₀
  if decide (1 ≤ p₀) && decide (p₀ ≤ p₁) && decide (0 < t₀) && decide (t₀ ≤ t₁) &&
      decide (shearQuarticRat p₀ t₀ ≤ 0) && decide (shearQuarticRat p₁ t₀ ≤ 0) &&
      shearLowOk p₀ t₁ T₀ && shearHighOk p₁ t₀ T₁ && decide (T₀ ≤ t₁) then
    some (ceilScaled 64 (min (shearFirstValue p₀ p₁ t₀ t₁ T₀)
      (shearSecondValueRight p₀ p₁ t₀ t₁ T₀ (shearSlopesRight p₀ p₁ t₀ t₁ T₀ T₁).1
        (shearSlopesRight p₀ p₁ t₀ t₁ T₀ T₁).2)))
  else none

/-- **Soundness of a cell to the right of `p = 1`.** -/
theorem lintegral_le_shearCellRight {t₀ t₁ p₀ p₁ : ℚ} {n : ℤ}
    (h : shearCellRight t₀ t₁ p₀ p₁ = some n) :
    ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioc (p₀ : ℝ) p₁, shearColumnDensity p t ≤
      ENNReal.ofReal (n / 2 ^ 64) := by
  unfold shearCellRight at h
  dsimp only at h
  split_ifs at h with hck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hp₀, hp⟩, ht₀⟩, ht⟩, hQ₀⟩, hQ₁⟩, hlo⟩, hhi⟩, hT₀t⟩ := hck
  simp only [Option.some.injEq] at h
  subst h
  set T₀ := shearMapLow p₀ t₁
  set T₁ := shearMapApprox p₁ t₀
  have ht₁ : 0 < t₁ := ht₀.trans_le ht
  have hp₀' : (1 : ℝ) ≤ p₀ := by exact_mod_cast hp₀
  have hp' : (p₀ : ℝ) ≤ p₁ := by exact_mod_cast hp
  have ht₀' : (0 : ℝ) < t₀ := by exact_mod_cast ht₀
  have ht' : (t₀ : ℝ) ≤ t₁ := by exact_mod_cast ht
  have ht₁' : (0 : ℝ) < t₁ := by exact_mod_cast ht₁
  have hT₀0 : 0 ≤ T₀ := le_max_left _ _
  have hT₁0 : 0 ≤ T₁ := by
    simp only [shearHighOk, Bool.and_eq_true, decide_eq_true_eq] at hhi
    exact hhi.1
  have hTlo : (T₀ : ℝ) ≤ shearMap p₀ t₁ := le_shearMap_of_shearLowOk ht₁ hlo
  have hThi : shearMap p₁ t₀ ≤ (T₁ : ℝ) := shearMap_le_of_shearHighOk ht₀ hhi
  have hQ : ∀ p ∈ Icc (p₀ : ℝ) p₁, ∀ t ∈ Icc (t₀ : ℝ) t₁, shearQuartic p t ≤ 0 :=
    fun p hp t ht ↦ (shearQuartic_le_max (by linarith) hp ht₀'.le ht.1).trans
      (max_le (by rw [← cast_shearQuarticRat]; exact_mod_cast hQ₀)
        (by rw [← cast_shearQuarticRat]; exact_mod_cast hQ₁))
  have hTcell : ∀ p ∈ Icc (p₀ : ℝ) p₁, ∀ t ∈ Icc (t₀ : ℝ) t₁, (T₀ : ℝ) ≤ shearMap p t :=
    fun p hp t ht ↦ hTlo.trans <| (monotoneOn_shearMap_left ht₁' hp₀' (hp₀'.trans hp.1) hp.1).trans
      (antitoneOn_shearMap_right p (ht₀'.trans_le ht.1) ht₁' ht.2)
  have hh1 : 0 ≤ ((p₀ : ℚ) - 1) * (p₁ - 1) := mul_nonneg (by linarith) (by linarith)
  -- the first-order value
  have hfirst : ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioc (p₀ : ℝ) p₁, shearColumnDensity p t ≤
      ENNReal.ofReal (shearFirstValue p₀ p₁ t₀ t₁ T₀) := by
    set r := sqrtApproxRel (t₁ - T₀)
    have hr : 0 < r := sqrtApproxRel_pos _
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    have hα : 0 ≤ (t₁ - T₀ + r ^ 2) / (2 * r) :=
      div_nonneg (by nlinarith [sq_nonneg r]) (by linarith)
    refine (lintegral_shearColumnDensity_cell_le (α := (((t₁ - T₀ + r ^ 2) / (2 * r) : ℚ) : ℝ))
      (β := 0) (γ := 0) (r := r) (by linarith) hp' ht₀' ht' hr' hQ
      (fun p hp t ht ↦ ?_)).trans ?_
    · have := hTcell p hp t ht
      push_cast
      simp only [zero_mul, add_zero]
      gcongr
      linarith [ht.2]
    · exact ENNReal.ofReal_le_ofReal <| (cornerSum_le_mul_shearMassHigh hα (by linarith) hp hh1
        ht₀ ht).trans_eq (Rat.cast_mul _ _).symm
  -- the second-order value
  obtain ⟨hl0, hm0, hl', hm'⟩ := shearSlopesRight_spec (p₀ := p₀) (p₁ := p₁) (t₀ := t₀)
    (t₁ := t₁) (T₀ := T₀) (T₁ := T₁) (by linarith) ht₁ hT₀0 hT₁0
  set l := (shearSlopesRight p₀ p₁ t₀ t₁ T₀ T₁).1
  set m := (shearSlopesRight p₀ p₁ t₀ t₁ T₀ T₁).2
  have hsecond : ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioc (p₀ : ℝ) p₁, shearColumnDensity p t ≤
      ENNReal.ofReal (shearSecondValueRight p₀ p₁ t₀ t₁ T₀ l m) := by
    set r := shearRadius p₀ p₁ t₀ t₁ (t₁ - T₀) (1 + l) m
    have hr : 0 < r := sqrtApproxRel_pos _
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    refine (lintegral_shearColumnDensity_cell_le
      (α := ((((t₁ - T₀) - (1 + l) * t₁ + m * p₀ + r ^ 2) / (2 * r) : ℚ) : ℝ))
      (β := ((-m / (2 * r) : ℚ) : ℝ)) (γ := (((1 + l) / (2 * r) : ℚ) : ℝ)) (r := r)
      (by linarith) hp' ht₀' ht' hr' hQ (fun p hp t ht ↦ ?_)).trans ?_
    · have hL := sub_shearMap_le_affine_right hp₀' ht₀' (by exact_mod_cast hT₀0) hTlo hThi
        (by exact_mod_cast hl0) hl' (by exact_mod_cast hm0) hm' hp ht
      have e : ((((t₁ - T₀) - (1 + l) * t₁ + m * p₀ + r ^ 2) / (2 * r) : ℚ) : ℝ) +
          ((-m / (2 * r) : ℚ) : ℝ) * p + (((1 + l) / (2 * r) : ℚ) : ℝ) * t =
          ((t₁ - T₀) - (1 + l) * (t₁ - t) - m * (p - p₀) + r ^ 2) / (2 * r) := by
        push_cast
        field_simp
        ring
      rw [e]
      gcongr
    · exact ENNReal.ofReal_le_ofReal (cornerSum_le_shearCellHigh
        (((t₁ - T₀) - (1 + l) * t₁ + m * p₀ + r ^ 2) / (2 * r))
        (-m / (2 * r)) ((1 + l) / (2 * r)) (by linarith) hp hh1 ht₀ ht)
  -- the smaller value, rounded up
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal (le_ceilScaled_real 64 _))
  rw [Rat.cast_min, ENNReal.ofReal_mono.map_min]
  exact le_min hfirst hsecond

/-! ### The strip at the threshold and the slabs -/

/-- The strip value of the band `[p_a, p_b] × [t₀, t₁]` at the threshold to the right of `p = 1`:
the area times `2 p_b max(0, -Q(p_a, t₁)) / (((p_a + 1)² + t₀²)² ((p_a - 1)² + t₀²)²)` times an
upper bound of `(t₁ - T(p_a, t₁))^{1/2}`. -/
def shearStripRight (t₀ t₁ pa pb : ℚ) : Option ℚ :=
  let Ts := shearMapLow pa t₁
  if shearLowOk pa t₁ Ts && decide (Ts ≤ t₁) then
    some ((pb - pa) * (t₁ - t₀) * (2 * pb * max 0 (-shearQuarticRat pa t₁) /
      (((pa + 1) ^ 2 + t₀ ^ 2) ^ 2 * ((pa - 1) ^ 2 + t₀ ^ 2) ^ 2) * sqrtHigh (t₁ - Ts)))
  else none

/-- **Soundness of the strip.** -/
theorem lintegral_le_shearStripRight {t₀ t₁ pa pb v : ℚ} (ht₀ : 0 < t₀) (ht : t₀ ≤ t₁)
    (hpa : 1 ≤ pa) (hab : pa ≤ pb) (hpa2 : t₁ ^ 2 + 1 ≤ pa ^ 2)
    (h : shearStripRight t₀ t₁ pa pb = some v) :
    ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioc (pa : ℝ) pb, shearColumnDensity p t ≤
      ENNReal.ofReal v := by
  unfold shearStripRight at h
  dsimp only at h
  split_ifs at h with hck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨hlo, hTs⟩ := hck
  simp only [Option.some.injEq] at h
  subst h
  set Ts := shearMapLow pa t₁
  have ht₁ : 0 < t₁ := ht₀.trans_le ht
  have ht₀' : (0 : ℝ) < t₀ := by exact_mod_cast ht₀
  have ht₁' : (0 : ℝ) < t₁ := by exact_mod_cast ht₁
  have hpa' : (1 : ℝ) ≤ pa := by exact_mod_cast hpa
  have hab' : (pa : ℝ) ≤ pb := by exact_mod_cast hab
  have hpa2' : (t₁ : ℝ) ^ 2 + 1 ≤ (pa : ℝ) ^ 2 := by exact_mod_cast hpa2
  have hTlo : (Ts : ℝ) ≤ shearMap pa t₁ := le_shearMap_of_shearLowOk ht₁ hlo
  have hP : 0 < (pa - 1) ^ 2 + t₀ ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos ht₀ 2)
  have hP' : 0 < (pa + 1) ^ 2 + t₀ ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos ht₀ 2)
  set Dm : ℚ := ((pa + 1) ^ 2 + t₀ ^ 2) ^ 2 * ((pa - 1) ^ 2 + t₀ ^ 2) ^ 2 with hDm
  have hDm0 : 0 < Dm := by positivity
  set D : ℚ := 2 * pb * max 0 (-shearQuarticRat pa t₁) / Dm with hD
  have hD0 : 0 ≤ D := div_nonneg (mul_nonneg (by linarith) (le_max_left _ _)) hDm0.le
  refine (lintegral_shearColumnDensity_strip_le (D := D) (φ := ((t₁ - Ts : ℚ) : ℝ)) hab'
    (by exact_mod_cast hD0) (fun p hp t ht' hs ↦ ?_)).trans (ENNReal.ofReal_le_ofReal ?_)
  · have ht0 : 0 < t := ht₀'.trans ht'.1
    have hp1 : 1 ≤ p := hpa'.trans hp.1.le
    have hQneg := shearQuartic_neg_of_shearThreshold_lt hs
    have hQle : shearQuartic pa t₁ ≤ shearQuartic p t :=
      shearQuartic_le_of_right hpa2' (by linarith) hp.1.le ht0.le ht'.2
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
        gcongr ?_ ^ 2 * ?_ ^ 2 <;> nlinarith [ht'.1, hp.1]
      have hnum' : -2 * p * shearQuartic p t ≤ 2 * pb * max 0 (-shearQuartic pa t₁) := by
        have m1 : -shearQuartic p t ≤ max 0 (-shearQuartic pa t₁) :=
          (neg_le_neg hQle).trans (le_max_right _ _)
        have m2 : p ≤ pb := hp.2
        nlinarith [le_max_left 0 (-shearQuartic pa t₁)]
      rw [hD]
      push_cast
      rw [cast_shearQuarticRat]
      have hDm'0 : (0 : ℝ) < Dm := by exact_mod_cast hDm0
      calc -2 * p * shearQuartic p t / (((p + 1) ^ 2 + t ^ 2) ^ 2 * ((p - 1) ^ 2 + t ^ 2) ^ 2)
          ≤ 2 * pb * max 0 (-shearQuartic pa t₁) /
              (((p + 1) ^ 2 + t ^ 2) ^ 2 * ((p - 1) ^ 2 + t ^ 2) ^ 2) :=
            div_le_div_of_nonneg_right hnum' hden.le
        _ ≤ 2 * pb * max 0 (-shearQuartic pa t₁) / Dm :=
            div_le_div_of_nonneg_left (mul_nonneg (by linarith) (le_max_left _ _)) hDm'0 hDm'
        _ = _ := by rw [hDm]
    · have hT := shearMap_le_self_of_shearQuartic_nonpos ht0 hQneg.le
      have hT1 : shearMap p t₁ ≤ shearMap p t := antitoneOn_shearMap_right p ht0 ht₁' ht'.2
      have hT2 : shearMap pa t₁ ≤ shearMap p t₁ :=
        monotoneOn_shearMap_left ht₁' hpa' hp1 hp.1.le
      rw [abs_of_nonneg (by linarith)]
      push_cast
      linarith [ht'.2]
  · have hφ : (0 : ℚ) ≤ t₁ - Ts := sub_nonneg.2 hTs
    have hs := sqrt_le_sqrtHigh hφ
    have hA : (0 : ℝ) ≤ ((pb : ℝ) - pa) * ((t₁ : ℝ) - t₀) :=
      mul_nonneg (by linarith) (by exact_mod_cast sub_nonneg.2 ht)
    push_cast
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by exact_mod_cast hD0)) hA
    exact_mod_cast hs

/-- The next node `p + ρ max(p - 1, t₀)` of a walk to the right of `p = 1`, rounded up. -/
def shearNextRight (ρ t₀ p : ℚ) : ℚ := roundUpRel (p + ρ * max (p - 1) t₀)

/-- An approximation of `h⁺(t) - 1 = t (t + 2 (t² + 1)^{1/2}) / (h⁺(t) + 1)`, where
`h⁺(t) = (t² + 1 + 2 t (t² + 1)^{1/2})^{1/2}`; only the sign checks give it a meaning. -/
def shearUpperGap (t : ℚ) : ℚ :=
  let s := sqrtApproxRel (t ^ 2 + 1)
  t * (t + 2 * s) / (sqrtApproxRel (t ^ 2 + 1 + 2 * t * s) + 1)

/-- An approximation of `1 - h⁻(q) = (2q(q² + 1)^{1/2} - q²)/(1 + h⁻(q))`; only the sign checks
give it a meaning. -/
def shearLowerGap (q : ℚ) : ℚ :=
  let s := sqrtApproxRel (q ^ 2 + 1)
  let u := (1 + q ^ 2) * (1 - 3 * q ^ 2) / (1 + q ^ 2 + 2 * q * s)
  (2 * q * s - q ^ 2) / (1 + if 0 < u then sqrtApproxRel u else 0)

/-- **The slab** `[t₀, t₁]` to the right of `p = 1`: the cells from `p = 1` to `p_a ≈ h⁺(t₀)`,
with the ratio `ρ`, and the strip from `p_a` to `p_b ≈ h⁺(t₁)`. -/
def shearSlabRight (ρ t₀ t₁ : ℚ) : Option ℤ :=
  let pa := roundDownRel (1 + shearUpperGap t₀ * (1 - 1 / 2 ^ 12))
  let pb := roundUpRel (1 + shearUpperGap t₁ * (1 + 1 / 2 ^ 12))
  if decide (0 < t₀) && decide (t₀ ≤ t₁) && decide (1 ≤ pa) && decide (pa ≤ pb) &&
      decide (t₁ ^ 2 + 1 ≤ pa ^ 2) && decide (0 ≤ shearQuarticRat pb t₁) then
    match shearStripRight t₀ t₁ pa pb with
    | none => none
    | some v =>
      match cellWalk (shearNextRight ρ t₀) (shearCellRight t₀ t₁) 100000 1 pa 0 with
      | some n => if 0 ≤ v then some (ceilScaled 64 v + n) else none
      | none => none
  else none

/-- For a set `S`, `t ↦ ∫⁻ p in S, shearColumnDensity p t` is measurable. -/
theorem measurable_lintegral_shearColumnDensity (S : Set ℝ) :
    Measurable fun t ↦ ∫⁻ p in S, shearColumnDensity p t :=
  (measurable_shearColumnDensity.comp measurable_swap).lintegral_prod_right'

/-- Two lower integrals over `t` of inner lower integrals add. -/
theorem lintegral_shearColumnDensity_le_add (Z : Set ℝ) {a b c : ℝ} :
    ∫⁻ t in Z, ∫⁻ p in Ioc a c, shearColumnDensity p t ≤
      (∫⁻ t in Z, ∫⁻ p in Ioc a b, shearColumnDensity p t) +
        ∫⁻ t in Z, ∫⁻ p in Ioc b c, shearColumnDensity p t := by
  rw [← lintegral_add_left (measurable_lintegral_shearColumnDensity _)]
  exact lintegral_mono fun t ↦
    (lintegral_mono_set Ioc_subset_Ioc_union_Ioc).trans (lintegral_union_le _ _ _)

/-- **Soundness of the slab.** -/
theorem lintegral_le_shearSlabRight {ρ t₀ t₁ : ℚ} {N : ℤ} (h : shearSlabRight ρ t₀ t₁ = some N) :
    ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioi (1 : ℝ), shearColumnDensity p t ≤
      ENNReal.ofReal (N / 2 ^ 64) := by
  unfold shearSlabRight at h
  dsimp only at h
  split_ifs at h with hck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨⟨⟨ht₀, ht⟩, hpa⟩, hab⟩, hpa2⟩, hQb⟩ := hck
  set pa := roundDownRel (1 + shearUpperGap t₀ * (1 - 1 / 2 ^ 12))
  set pb := roundUpRel (1 + shearUpperGap t₁ * (1 + 1 / 2 ^ 12))
  split at h
  · simp at h
  rename_i v hv
  split at h
  · rename_i n hn
    split_ifs at h with hv0
    simp only [Option.some.injEq] at h
    subst h
    have ht₀' : (0 : ℝ) < t₀ := by exact_mod_cast ht₀
    have hpa' : (1 : ℝ) ≤ pa := by exact_mod_cast hpa
    have hab' : (pa : ℝ) ≤ pb := by exact_mod_cast hab
    have hpb2 : (t₁ : ℝ) ^ 2 + 1 ≤ (pb : ℝ) ^ 2 := by
      have h1 : (t₁ ^ 2 + 1 : ℚ) ≤ pb ^ 2 :=
        hpa2.trans (pow_le_pow_left₀ (by linarith) hab 2)
      exact_mod_cast h1
    have hQb' : 0 ≤ shearQuartic pb t₁ := by
      rw [← cast_shearQuarticRat]
      exact_mod_cast hQb
    -- the inner range splits; beyond `p_b` the density vanishes
    have hsplit : ∀ t ∈ Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioi (1 : ℝ), shearColumnDensity p t ≤
        (∫⁻ p in Ioc (1 : ℝ) pa, shearColumnDensity p t) +
          ∫⁻ p in Ioc (pa : ℝ) pb, shearColumnDensity p t := by
      intro t ht'
      have ht0 : 0 ≤ t := (ht₀'.trans ht'.1).le
      have h0 : ∫⁻ p in Ioi (pb : ℝ), shearColumnDensity p t = 0 := by
        rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun _ ↦ 0) fun p hp ↦
          shearColumnDensity_eq_zero ht0 (hQb'.trans (shearQuartic_le_of_right hpb2
            (by linarith) (le_of_lt hp) ht0 ht'.2))]
        simp
      rw [← Ioc_union_Ioi_eq_Ioi hpa', ← Ioc_union_Ioi_eq_Ioi hab']
      refine (lintegral_union_le _ _ _).trans (add_le_add le_rfl ?_)
      exact (lintegral_union_le _ _ _).trans_eq (by rw [h0, add_zero])
    -- the walk of cells
    have hwalk := le_of_cellWalk_of_subadditive
      (Φ := fun a b ↦ ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioc a b, shearColumnDensity p t)
      (g := fun q : ℚ ↦ (q : ℝ)) (K := 64)
      (fun a ha b hb hab ↦ by simp only; exact_mod_cast hab)
      (fun _ _ _ _ _ ↦ lintegral_shearColumnDensity_le_add _)
      (fun a b hba ↦ by simp [Ioc_eq_empty (not_lt.2 hba)])
      (fun l u m hl hlu hm ↦ lintegral_le_shearCellRight hm) (by norm_num) (by linarith) hn
    have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast le_of_cellWalk hn
    have hv1 : (0 : ℝ) ≤ (ceilScaled 64 v : ℝ) / 2 ^ 64 :=
      (by exact_mod_cast hv0 : (0 : ℝ) ≤ v).trans (le_ceilScaled_real 64 v)
    calc ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioi (1 : ℝ), shearColumnDensity p t
        ≤ ∫⁻ t in Ioc (t₀ : ℝ) t₁, ((∫⁻ p in Ioc (1 : ℝ) pa, shearColumnDensity p t) +
            ∫⁻ p in Ioc (pa : ℝ) pb, shearColumnDensity p t) :=
          setLIntegral_mono' measurableSet_Ioc hsplit
      _ = (∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioc (1 : ℝ) pa, shearColumnDensity p t) +
            ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioc (pa : ℝ) pb, shearColumnDensity p t :=
          lintegral_add_left (measurable_lintegral_shearColumnDensity _) _
      _ ≤ ENNReal.ofReal (((n : ℝ) - ((0 : ℤ) : ℝ)) / 2 ^ 64) +
            ENNReal.ofReal ((ceilScaled 64 v : ℝ) / 2 ^ 64) := by
          refine add_le_add (by simpa using hwalk) ?_
          exact (lintegral_le_shearStripRight ht₀ ht hpa hab hpa2 hv).trans
            (ENNReal.ofReal_le_ofReal (le_ceilScaled_real 64 v))
      _ = ENNReal.ofReal (((ceilScaled 64 v + n : ℤ) : ℝ) / 2 ^ 64) := by
          rw [← ENNReal.ofReal_add (by simpa using div_nonneg hn0 (by positivity)) hv1]
          congr 1
          push_cast
          ring
  · simp at h

/-- The next height `t + ρ t`, rounded up. -/
def shearNextHeight (ρ t : ℚ) : ℚ := roundUpRel (t + ρ * t)

/-- **The walk over slabs** from `t_A` to `t_B`, with the ratios `ρ` in `p` and `ρ_t` in `t`. -/
def shearOuterWalk (ρ ρt tA tB : ℚ) : Option ℤ :=
  cellWalk (shearNextHeight ρt) (shearSlabRight ρ) 100000 tA tB 0

/-- **Soundness of the walk over slabs**: for `0 ≤ t_A, t_B`, a walk value `N` bounds
`∫_{(t_A, t_B]} ∫_{p > 1} shearColumnDensity p t` by `N/2^64`. -/
theorem lintegral_le_shearOuterWalk {ρ ρt tA tB : ℚ} {N : ℤ} (hA : 0 ≤ tA) (hB : 0 ≤ tB)
    (h : shearOuterWalk ρ ρt tA tB = some N) :
    ∫⁻ t in Ioc (tA : ℝ) tB, ∫⁻ p in Ioi (1 : ℝ), shearColumnDensity p t ≤
      ENNReal.ofReal (N / 2 ^ 64) := by
  have := lintegral_le_of_cellWalk (F := fun t ↦ ∫⁻ p in Ioi (1 : ℝ), shearColumnDensity p t)
    (g := fun q : ℚ ↦ (q : ℝ)) (K := 64)
    (fun a ha b hb hab ↦ by simp only; exact_mod_cast hab)
    (fun l u m hl hlu hm ↦ lintegral_le_shearSlabRight hm) hA hB h
  simpa using this

/-- A decided walk over slabs bounds the heights it covers. -/
theorem lintegral_le_of_shearOuterCheck {ρ ρt tA tB b : ℚ} (hA : 0 ≤ tA) (hB : 0 ≤ tB)
    (h : walkLe (shearOuterWalk ρ ρt tA tB) b = true) :
    ∫⁻ t in Ioc (tA : ℝ) tB, ∫⁻ p in Ioi (1 : ℝ), shearColumnDensity p t ≤
      ENNReal.ofReal b := by
  obtain ⟨n, hn, hle⟩ := walkLe_spec h
  exact (lintegral_le_shearOuterWalk hA hB hn).trans (ENNReal.ofReal_le_ofReal hle)

end IncompressibleFlow.SharpHolder
