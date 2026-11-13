/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearLowerEnvelope

/-!
# Cell bounds of the lower cost of the horizontal estimate of `v_x`

For `0 < ℓ ≤ A ≤ u`, `S_low(10, A) ≤ 4 ∫_0^9 λ(p) dp` with the column density
`λ(p) = ∫_0^{min(u, T(p, ℓ), s_c(p))} |Δ(p, t)| t^{1/2} dt` (`shearLowerCost_le_region`,
`shearLowerDensity`). The columns `(p₀, p₁]` on one side of `p = 1` are bounded as follows.

* The cubic of `T(p, ℓ)` times `ℓ` is concave in `p²`, so a bound `T ≥ T(p, ℓ)` checked at both
  ends holds on the column (`shearMap_le_of_shearHighOk_of_mem`); likewise `Q(·, s) ≤ 0` at both
  ends gives `s_c ≤ s` (`shearThreshold_le_of_mem`). This bounds the height of the column by `c̄`.
* Below a height `c` with `Q ≥ 0` at the inner end, `Δ ≤ 0` on the column, and over a rectangle
  the mass `∫∫ |Δ|` is the corner sum (`lintegral_le_shearLowerCell`), with weight at most
  `t₁^{1/2}`.
* Elsewhere `|Δ| ≤ 2 p |Q| / (D₊² D₋²)` with `|Q| ≤ max((p² - 1)², 2 t² (p² + 1) + 3 t⁴)`
  (`abs_shearQuartic_le`), used for the bottom `(0, c/64]` and for the strip `(c, c̄]`.

The column `(1 - δ, 1 + δ]` around `p = 1` is bounded by `T(p, ℓ) ≤ (p² - 1)²/(ℓ (ℓ² + 2))` and
`|Δ| ≤ 1/(2 (p + 1)²) + 1/(2 (p - 1)²)` (`lintegral_shearLowerDensity_near_le`). Two cell walks
cover `(0, 1 - δ]` and `(1 + δ, 9]`.

## Main definitions

* `shearLowerDensity`: the column density `λ(p)` of the lower region.
* `shearLowerCell`: the corner-sum bound of a cell of a column where `Δ ≤ 0`.
* `shearLowerColumn`: the bound of a column `(p₀, p₁]` from Newton candidates of `T(·, ℓ)` and
  `s_c`.
* `shearLowerSlab`: the lower cost of a slab `ℓ ≤ A ≤ u`, on the grid `2^-64`.

## Main results

* `shearMap_le_of_shearHighOk_of_mem`: an upper bound of `T(·, ℓ)` checked at both ends of a column
  holds on the column.
* `shearThreshold_le_of_mem`: `Q(p₀, s) ≤ 0` and `Q(p₁, s) ≤ 0` give `s_c ≤ s` on `[p₀, p₁]`.
* `lintegral_le_shearLowerCell`: where `Δ ≤ 0`, a cell value `n` bounds the weighted cell integral
  of `|Δ|` by `n/2^64`.
* `lintegral_le_shearLowerColumn`: a column value `N` bounds `∫_{(p₀, p₁]} λ` by `N/2^64`.
* `lintegral_shearLowerDensity_near_le`: for `0 < δ ≤ 1`, the bound of `∫_{1-δ}^{1+δ} λ`.
* `shearLowerCost_le_shearLowerSlab`: `S_low(10, A) ≤ N/2^64` for `ℓ ≤ A ≤ u`.
* `shearLowerCost_le_shearLowerSlab_top`: with `u ≥ 8`, `S_low(10, A) ≤ N/2^64` for all `A ≥ ℓ`.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory PDE.Analysis
open scoped ENNReal

namespace IncompressibleFlow.SharpHolder

/-- The column density `λ(p) = ∫_0^{min(u, T(p, ℓ), s_c(p))} |Δ(p, t)| t^{1/2} dt` of the lower
region. -/
def shearLowerDensity (ℓ u p : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioc 0 (min u (min (shearMap p ℓ) (shearThreshold p))),
    ‖shearDifference p t‖ₑ * ENNReal.ofReal (t ^ (1 / 2 : ℝ))

/-- The integrand `|Δ(p, t)| t^{1/2}` is jointly measurable in `(p, t)`. -/
theorem measurable_shearLowerIntegrand :
    Measurable fun q : ℝ × ℝ ↦
      ‖shearDifference q.1 q.2‖ₑ * ENNReal.ofReal (q.2 ^ (1 / 2 : ℝ)) :=
  measurable_shearDifference.enorm.mul (measurable_snd.pow_const _).ennreal_ofReal

/-! ### Bounds over a column -/

/-- **The transport map over a column**: `ℓ` times the cubic of `T(p, ℓ)` is concave in `p²`, so
an upper bound of `T` checked at both ends of `[p₀, p₁]` holds on the column. -/
theorem shearMap_le_of_shearHighOk_of_mem {p₀ p₁ t T : ℚ} (ht : 0 < t) (hp₀ : 0 ≤ p₀)
    (h₀ : shearHighOk p₀ t T = true) (h₁ : shearHighOk p₁ t T = true) {p : ℝ}
    (hp : p ∈ Icc (p₀ : ℝ) p₁) : shearMap p t ≤ T := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  simp only [shearHighOk, Bool.and_eq_true, decide_eq_true_eq] at h₀ h₁
  have c₀ : (0 : ℝ) ≤ ((shearCubicRat p₀ t T : ℚ) : ℝ) := by exact_mod_cast h₀.2
  have c₁ : (0 : ℝ) ≤ ((shearCubicRat p₁ t T : ℚ) : ℝ) := by exact_mod_cast h₁.2
  simp only [shearCubicRat] at c₀ c₁
  push_cast at c₀ c₁
  have hT : (0 : ℝ) ≤ T := by exact_mod_cast h₀.1
  refine shearMap_le_of_shearCubic_nonneg ht' hT ?_
  have hp₀' : (0 : ℝ) ≤ p₀ := by exact_mod_cast hp₀
  have hs₀ : (p₀ : ℝ) ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ hp₀' hp.1 2
  have hs₁ : p ^ 2 ≤ (p₁ : ℝ) ^ 2 := pow_le_pow_left₀ (hp₀'.trans hp.1) hp.2 2
  have key : 0 ≤ (t : ℝ) * T ^ 3 + t ^ 2 * T ^ 2 + t * T * (t ^ 2 + 2 + 2 * p ^ 2) -
      (p ^ 2 - 1) ^ 2 := by
    rcases le_total (2 * (t : ℝ) * T) (p ^ 2 + (p₀ : ℝ) ^ 2 - 2) with h | h
    · have hm : 0 ≤ ((p₁ : ℝ) ^ 2 - p ^ 2) * (p ^ 2 + (p₁ : ℝ) ^ 2 - 2 - 2 * t * T) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    · have hm : 0 ≤ (p ^ 2 - (p₀ : ℝ) ^ 2) * (2 * t * T - (p ^ 2 + (p₀ : ℝ) ^ 2 - 2)) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
  rw [← mul_shearCubic_eq p ht'.ne'] at key
  exact nonneg_of_mul_nonneg_right (by linarith) ht'

/-- **The threshold over a column**: `Q(p₀, s) ≤ 0` and `Q(p₁, s) ≤ 0` give `s_c ≤ s` on
`[p₀, p₁]`. -/
theorem shearThreshold_le_of_mem {p₀ p₁ s : ℚ} (hp₀ : 0 ≤ p₀) (hs : 0 ≤ s)
    (h₀ : shearQuarticRat p₀ s ≤ 0) (h₁ : shearQuarticRat p₁ s ≤ 0) {p : ℝ}
    (hp : p ∈ Icc (p₀ : ℝ) p₁) : shearThreshold p ≤ s := by
  refine shearThreshold_le_of_shearQuartic_nonpos (by exact_mod_cast hs) ?_
  refine (shearQuartic_le_max (by exact_mod_cast hp₀) hp (by exact_mod_cast hs) le_rfl).trans ?_
  have c₀ : ((shearQuarticRat p₀ s : ℚ) : ℝ) ≤ 0 := by exact_mod_cast h₀
  have c₁ : ((shearQuarticRat p₁ s : ℚ) : ℝ) ≤ 0 := by exact_mod_cast h₁
  rw [cast_shearQuarticRat] at c₀ c₁
  exact max_le c₀ c₁

/-- `|Q(p, t)| ≤ max((p² - 1)², 2 t² (p² + 1) + 3 t⁴)`. -/
theorem abs_shearQuartic_le (p t : ℝ) :
    |shearQuartic p t| ≤ max ((p ^ 2 - 1) ^ 2) (2 * t ^ 2 * (p ^ 2 + 1) + 3 * t ^ 4) := by
  have e : shearQuartic p t = (p ^ 2 - 1) ^ 2 - (2 * t ^ 2 * (p ^ 2 + 1) + 3 * t ^ 4) := by
    simp only [shearQuartic]
    ring
  rw [e, abs_le]
  constructor
  · have : 0 ≤ (p ^ 2 - 1) ^ 2 := sq_nonneg _
    linarith [le_max_right ((p ^ 2 - 1) ^ 2) (2 * t ^ 2 * (p ^ 2 + 1) + 3 * t ^ 4)]
  · have : 0 ≤ 2 * t ^ 2 * (p ^ 2 + 1) + 3 * t ^ 4 := by positivity
    linarith [le_max_left ((p ^ 2 - 1) ^ 2) (2 * t ^ 2 * (p ^ 2 + 1) + 3 * t ^ 4)]

/-- `(p² - 1)²` is convex in `p²`: at most its larger value at the ends of `[p₀, p₁]`. -/
theorem sq_sub_one_sq_le_max {p₀ p₁ p : ℝ} (hp₀ : 0 ≤ p₀) (hp : p ∈ Icc p₀ p₁) :
    (p ^ 2 - 1) ^ 2 ≤ max ((p₀ ^ 2 - 1) ^ 2) ((p₁ ^ 2 - 1) ^ 2) := by
  have hs₀ : p₀ ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ hp₀ hp.1 2
  have hs₁ : p ^ 2 ≤ p₁ ^ 2 := pow_le_pow_left₀ (hp₀.trans hp.1) hp.2 2
  rcases le_total (p ^ 2 + p₀ ^ 2) 2 with h | h
  · have : (p ^ 2 - 1) ^ 2 ≤ (p₀ ^ 2 - 1) ^ 2 := by nlinarith
    exact this.trans (le_max_left _ _)
  · have : (p ^ 2 - 1) ^ 2 ≤ (p₁ ^ 2 - 1) ^ 2 := by nlinarith
    exact this.trans (le_max_right _ _)

/-- **The pointwise bound of the bottom and the strips**: on `[p₀, p₁] × [t₀, c]`, with
`d ≤ |p - 1|`, `|Δ| ≤ 2 p₁ max(Q₀, 2 c² (p₁² + 1) + 3 c⁴)/(((p₀ + 1)² + t₀²)² (d² + t₀²)²)`. -/
theorem abs_shearDifference_le_column {p₀ p₁ t₀ c d p t : ℝ} (hp₀ : 0 ≤ p₀)
    (hp : p ∈ Icc p₀ p₁) (ht₀ : 0 ≤ t₀) (ht : t ∈ Ioc t₀ c) (hd : 0 < d) (hdp : d ≤ |p - 1|) :
    |shearDifference p t| ≤ 2 * p₁ * max (max ((p₀ ^ 2 - 1) ^ 2) ((p₁ ^ 2 - 1) ^ 2))
      (2 * c ^ 2 * (p₁ ^ 2 + 1) + 3 * c ^ 4) /
        (((p₀ + 1) ^ 2 + t₀ ^ 2) ^ 2 * (d ^ 2 + t₀ ^ 2) ^ 2) := by
  have ht0 : 0 < t := ht₀.trans_lt ht.1
  have hp0 : 0 ≤ p := hp₀.trans hp.1
  refine abs_shearDifference_le_strip hp0 hp.2 ht0 ?_ (by positivity) ?_
  · refine (abs_shearQuartic_le p t).trans (max_le_max (sq_sub_one_sq_le_max hp₀ hp) ?_)
    have h1 : t ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ ht0.le ht.2 2
    have h2 : p ^ 2 ≤ p₁ ^ 2 := pow_le_pow_left₀ hp0 hp.2 2
    have h3 : t ^ 4 ≤ c ^ 4 := pow_le_pow_left₀ ht0.le ht.2 4
    nlinarith [mul_le_mul h1 (add_le_add_right h2 1) (by positivity) (sq_nonneg c)]
  · have ht2 : t₀ ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ ht₀ ht.1.le 2
    have hplus : (p₀ + 1) ^ 2 + t₀ ^ 2 ≤ (p + 1) ^ 2 + t ^ 2 := by nlinarith [hp.1]
    have hd2 : d ^ 2 ≤ (p - 1) ^ 2 := by
      rw [← sq_abs (p - 1)]
      exact pow_le_pow_left₀ hd.le hdp 2
    have hminus : d ^ 2 + t₀ ^ 2 ≤ (p - 1) ^ 2 + t ^ 2 := by linarith
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) hplus 2)
      (pow_le_pow_left₀ (by positivity) hminus 2) (by positivity) (by positivity)

/-- `Δ ≤ 0` to the left of `p₁ ≤ 1` below `c` when `Q(p₁, c) ≥ 0`. -/
theorem shearDifference_nonpos_of_left {p₁ c : ℚ} (h1 : p₁ ≤ 1) (hQ : 0 ≤ shearQuarticRat p₁ c)
    {p t : ℝ} (hp : 0 ≤ p) (hpp : p ≤ p₁) (ht : 0 < t) (htc : t ≤ c) :
    shearDifference p t ≤ 0 := by
  have hQ' : (0 : ℝ) ≤ shearQuartic p₁ c := by
    rw [← cast_shearQuarticRat]
    exact_mod_cast hQ
  exact shearDifference_nonpos_of_shearQuartic_nonneg hp ht
    (hQ'.trans (shearQuartic_le_of_left (by exact_mod_cast h1) hp hpp ht.le htc))

/-- `Δ ≤ 0` to the right of `p₀` with `c² + 1 ≤ p₀²` below `c` when `Q(p₀, c) ≥ 0`. -/
theorem shearDifference_nonpos_of_right {p₀ c : ℚ} (hb : c ^ 2 + 1 ≤ p₀ ^ 2) (hp₀ : 0 ≤ p₀)
    (hQ : 0 ≤ shearQuarticRat p₀ c) {p t : ℝ} (hpp : p₀ ≤ p) (ht : 0 < t) (htc : t ≤ c) :
    shearDifference p t ≤ 0 := by
  have hQ' : (0 : ℝ) ≤ shearQuartic p₀ c := by
    rw [← cast_shearQuarticRat]
    exact_mod_cast hQ
  have hb' : (c : ℝ) ^ 2 + 1 ≤ (p₀ : ℝ) ^ 2 := by exact_mod_cast hb
  have hp₀' : (0 : ℝ) ≤ p₀ := by exact_mod_cast hp₀
  exact shearDifference_nonpos_of_shearQuartic_nonneg (hp₀'.trans hpp) ht
    (hQ'.trans (shearQuartic_le_of_right hb' hp₀' hpp ht.le htc))

/-! ### The pieces of a column -/

/-- The weight `t^{1/2} ≤ w` on `(t₀, t₁]` comes out of the iterated integral. -/
theorem lintegral_lintegral_mul_sqrt_le {t₀ t₁ w : ℝ} (S : Set ℝ) (hw : t₁ ^ (1 / 2 : ℝ) ≤ w)
    (ht₀ : 0 ≤ t₀) :
    ∫⁻ t in Ioc t₀ t₁, ∫⁻ p in S, ‖shearDifference p t‖ₑ * ENNReal.ofReal (t ^ (1 / 2 : ℝ)) ≤
      ENNReal.ofReal w * ∫⁻ t in Ioc t₀ t₁, ∫⁻ p in S, ‖shearDifference p t‖ₑ := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Ioc fun t ht ↦ ?_
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]
  gcongr
  exact (Real.rpow_le_rpow (ht₀.trans ht.1.le) ht.2 (by norm_num)).trans hw

/-- **A cell of a column** where `Δ ≤ 0`: the corner sum with the weight `sqrtHigh t₁`. -/
def shearLowerCell (p₀ p₁ c t₀ t₁ : ℚ) : Option ℤ :=
  if 0 < t₀ ∧ t₁ ≤ c then some (ceilScaled 64 (sqrtHigh t₁ * -shearMassLow p₀ p₁ t₀ t₁))
  else none

/-- **Soundness of a cell.** If `Δ ≤ 0` on `[p₀, p₁] × (0, c]` and `(p₀ - 1)(p₁ - 1) ≥ 0`, a cell
value `n` bounds `∫_{(t₀, t₁]} ∫_{(p₀, p₁]} |Δ| t^{1/2}` by `n/2^64`. -/
theorem lintegral_le_shearLowerCell {p₀ p₁ c t₀ t₁ : ℚ} {n : ℤ} (hp₀ : 0 ≤ p₀) (hp : p₀ ≤ p₁)
    (h1 : 0 ≤ (p₀ - 1) * (p₁ - 1))
    (hsign : ∀ p ∈ Icc (p₀ : ℝ) p₁, ∀ t : ℝ, 0 < t → t ≤ c → shearDifference p t ≤ 0)
    (ht : t₀ < t₁) (h : shearLowerCell p₀ p₁ c t₀ t₁ = some n) :
    ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioc (p₀ : ℝ) p₁,
      ‖shearDifference p t‖ₑ * ENNReal.ofReal (t ^ (1 / 2 : ℝ)) ≤
        ENNReal.ofReal (n / 2 ^ 64) := by
  unfold shearLowerCell at h
  split_ifs at h with hc
  obtain rfl := Option.some.inj h
  have ht₀ : (0 : ℝ) < t₀ := by exact_mod_cast hc.1
  have ht' : (t₀ : ℝ) ≤ t₁ := by exact_mod_cast ht.le
  have hp' : (p₀ : ℝ) ≤ p₁ := by exact_mod_cast hp
  have hw : (t₁ : ℝ) ^ (1 / 2 : ℝ) ≤ (sqrtHigh t₁ : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact sqrt_le_sqrtHigh (by linarith [hc.1])
  have hΔ : ∀ p ∈ Icc (p₀ : ℝ) p₁, ∀ t ∈ Icc (t₀ : ℝ) t₁, shearDifference p t ≤ 0 :=
    fun p hp t ht ↦ hsign p hp t (ht₀.trans_le ht.1) (ht.2.trans (by exact_mod_cast hc.2))
  have hlow := shearMassLow_le_integral_integral_shearDifference hp₀ hp h1 hc.1 ht.le
  have hS : (0 : ℝ) ≤ sqrtHigh t₁ := by exact_mod_cast (sqrtHigh_pos (by linarith [hc.1])).le
  refine (lintegral_lintegral_mul_sqrt_le _ hw ht₀.le).trans ?_
  rw [lintegral_enorm_shearDifference_eq_of_nonpos hp' ht₀ ht' hΔ,
    ← ENNReal.ofReal_mul hS]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (sqrtHigh t₁ : ℝ) * -∫ t in (t₀ : ℝ)..t₁, ∫ p in (p₀ : ℝ)..p₁, shearDifference p t
      ≤ (sqrtHigh t₁ : ℝ) * -(shearMassLow p₀ p₁ t₀ t₁ : ℝ) :=
        mul_le_mul_of_nonneg_left (by linarith) hS
    _ = ((sqrtHigh t₁ * -shearMassLow p₀ p₁ t₀ t₁ : ℚ) : ℝ) := by push_cast; ring
    _ ≤ _ := le_ceilScaled_real 64 _

/-- **A strip of a column** from a pointwise bound `D` of `|Δ|`. -/
theorem lintegral_le_strip_mul {p₀ p₁ t₀ t₁ D w : ℝ} (hp : p₀ ≤ p₁) (hD : 0 ≤ D)
    (ht₀ : 0 ≤ t₀) (hw : t₁ ^ (1 / 2 : ℝ) ≤ w) (hw0 : 0 ≤ w)
    (hb : ∀ p ∈ Ioc p₀ p₁, ∀ t ∈ Ioc t₀ t₁, |shearDifference p t| ≤ D) :
    ∫⁻ t in Ioc t₀ t₁, ∫⁻ p in Ioc p₀ p₁,
      ‖shearDifference p t‖ₑ * ENNReal.ofReal (t ^ (1 / 2 : ℝ)) ≤
        ENNReal.ofReal (w * ((p₁ - p₀) * (t₁ - t₀) * D)) := by
  refine (lintegral_lintegral_mul_sqrt_le _ hw ht₀).trans ?_
  rw [ENNReal.ofReal_mul hw0]
  gcongr
  exact lintegral_enorm_shearDifference_le_strip hp hD hb

/-- The rational bound of a strip `(p₀, p₁] × (t₀, t₁]` with `d ≤ |p - 1|` on the column. -/
def shearLowerStrip (p₀ p₁ d t₀ t₁ : ℚ) : ℚ :=
  sqrtHigh t₁ * ((p₁ - p₀) * (t₁ - t₀) *
    (2 * p₁ * max (max ((p₀ ^ 2 - 1) ^ 2) ((p₁ ^ 2 - 1) ^ 2))
      (2 * t₁ ^ 2 * (p₁ ^ 2 + 1) + 3 * t₁ ^ 4) /
        (((p₀ + 1) ^ 2 + t₀ ^ 2) ^ 2 * (d ^ 2 + t₀ ^ 2) ^ 2)))

/-- The strip bound is nonnegative. -/
theorem shearLowerStrip_nonneg {p₀ p₁ d t₀ t₁ : ℚ} (hp₀ : 0 ≤ p₀) (hp : p₀ ≤ p₁) (ht₀ : 0 ≤ t₀)
    (ht : t₀ ≤ t₁) (hd : 0 < d) : 0 ≤ shearLowerStrip p₀ p₁ d t₀ t₁ := by
  unfold shearLowerStrip
  have h₁ := sqrtHigh_pos (ht₀.trans ht)
  have h₂ : 0 ≤ max (max ((p₀ ^ 2 - 1) ^ 2) ((p₁ ^ 2 - 1) ^ 2))
      (2 * t₁ ^ 2 * (p₁ ^ 2 + 1) + 3 * t₁ ^ 4) := le_max_of_le_right (by positivity)
  have h₃ : 0 ≤ p₁ - p₀ := by linarith
  have h₄ : 0 ≤ t₁ - t₀ := by linarith
  have h₅ : 0 ≤ p₁ := hp₀.trans hp
  positivity

/-- **Soundness of a strip.** If `d ≤ |p - 1|` on `[p₀, p₁]`, the strip bound majorizes
`∫_{(t₀, t₁]} ∫_{(p₀, p₁]} |Δ| t^{1/2}`. -/
theorem lintegral_le_shearLowerStrip {p₀ p₁ d t₀ t₁ : ℚ} (hp₀ : 0 ≤ p₀) (hp : p₀ ≤ p₁)
    (ht₀ : 0 ≤ t₀) (ht : t₀ ≤ t₁) (hd : 0 < d) (hdp : ∀ p ∈ Icc (p₀ : ℝ) p₁, (d : ℝ) ≤ |p - 1|) :
    ∫⁻ t in Ioc (t₀ : ℝ) t₁, ∫⁻ p in Ioc (p₀ : ℝ) p₁,
      ‖shearDifference p t‖ₑ * ENNReal.ofReal (t ^ (1 / 2 : ℝ)) ≤
        ENNReal.ofReal (shearLowerStrip p₀ p₁ d t₀ t₁) := by
  have hp₀' : (0 : ℝ) ≤ p₀ := by exact_mod_cast hp₀
  have ht₀' : (0 : ℝ) ≤ t₀ := by exact_mod_cast ht₀
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hw : (t₁ : ℝ) ^ (1 / 2 : ℝ) ≤ (sqrtHigh t₁ : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact sqrt_le_sqrtHigh (ht₀.trans ht)
  have hD : (0 : ℝ) ≤ 2 * (p₁ : ℝ) * max (max (((p₀ : ℝ) ^ 2 - 1) ^ 2) (((p₁ : ℝ) ^ 2 - 1) ^ 2))
      (2 * (t₁ : ℝ) ^ 2 * ((p₁ : ℝ) ^ 2 + 1) + 3 * (t₁ : ℝ) ^ 4) /
        ((((p₀ : ℝ) + 1) ^ 2 + (t₀ : ℝ) ^ 2) ^ 2 * ((d : ℝ) ^ 2 + (t₀ : ℝ) ^ 2) ^ 2) := by
    have : (0 : ℝ) ≤ p₁ := by exact_mod_cast hp₀.trans hp
    have h₂ : (0 : ℝ) ≤ max (max (((p₀ : ℝ) ^ 2 - 1) ^ 2) (((p₁ : ℝ) ^ 2 - 1) ^ 2))
        (2 * (t₁ : ℝ) ^ 2 * ((p₁ : ℝ) ^ 2 + 1) + 3 * (t₁ : ℝ) ^ 4) :=
      le_max_of_le_right (by positivity)
    positivity
  refine (lintegral_le_strip_mul (by exact_mod_cast hp) hD ht₀' hw
    (by exact_mod_cast (sqrtHigh_pos (ht₀.trans ht)).le) fun p hp' t ht' ↦
      abs_shearDifference_le_column hp₀' (Ioc_subset_Icc_self hp') ht₀' ht' hd'
        (hdp p (Ioc_subset_Icc_self hp'))).trans (le_of_eq ?_)
  unfold shearLowerStrip
  push_cast
  rfl

/-! ### A column -/

/-- An upper candidate of `s_c(x)`, checked by the sign of `Q`. -/
def shearThresholdHigh (x : ℚ) : ℚ :=
  roundUpRel (sqrtHigh (max 0 ((2 * sqrtHigh (x ^ 4 - x ^ 2 + 1) - (x ^ 2 + 1)) / 3)) *
    (1 + 1 / 2 ^ 30))

/-- A lower candidate of `s_c(x)`, checked by the sign of `Q`. -/
def shearThresholdLow (x : ℚ) : ℚ :=
  roundDownRel (sqrtLow (max 0 ((2 * sqrtLow (x ^ 4 - x ^ 2 + 1) - (x ^ 2 + 1)) / 3)) *
    (1 - 1 / 2 ^ 30))

/-- The distance `1 - p₁` or `p₀ - 1` of a column to `p = 1`. -/
def shearColumnGap (p₀ p₁ : ℚ) : ℚ := if p₁ < 1 then 1 - p₁ else p₀ - 1

/-- Left of `p = 1` the gap is `1 - p₁`. -/
theorem shearColumnGap_of_lt {p₀ p₁ : ℚ} (h : p₁ < 1) : shearColumnGap p₀ p₁ = 1 - p₁ := by
  simp [shearColumnGap, h]

/-- Right of `p = 1` the gap is `p₀ - 1`. -/
theorem shearColumnGap_of_le {p₀ p₁ : ℚ} (h : 1 ≤ p₁) : shearColumnGap p₀ p₁ = p₀ - 1 := by
  simp [shearColumnGap, not_lt.2 h]

/-- The column `(p₀, p₁]` with the candidate bounds `T ≥ T(p, ℓ)`, `s ≥ s_c(p)` on the column and
`c₀ ≤ s_c` at its inner end: cells of ratio `4/3` in `t` below `c = min(c̄, c₀)`, the bottom
`(0, c/64]` and the strip `(c, c̄]`, `c̄ = min(u, T, s)`. -/
def shearLowerColumnOf (ℓ u p₀ p₁ T s c₀ : ℚ) : Option ℤ :=
  let cbar := min u (min T s)
  let c := min cbar c₀
  let d := shearColumnGap p₀ p₁
  if decide (0 < ℓ) && decide (0 ≤ p₀) && decide (p₀ < p₁) && shearHighOk p₀ ℓ T &&
      shearHighOk p₁ ℓ T && decide (0 ≤ s) && decide (shearQuarticRat p₀ s ≤ 0) &&
      decide (shearQuarticRat p₁ s ≤ 0) && decide (0 < c) &&
      (decide (p₁ < 1) && decide (0 ≤ shearQuarticRat p₁ c₀) ||
        decide (1 < p₀) && decide (c₀ ^ 2 + 1 ≤ p₀ ^ 2) &&
          decide (0 ≤ shearQuarticRat p₀ c₀)) then
    match cellWalk (fun t ↦ roundUpRel (t * (4 / 3))) (shearLowerCell p₀ p₁ c) 1000 (c / 64) c 0
    with
    | some n => some (n + ceilScaled 64 (shearLowerStrip p₀ p₁ d 0 (c / 64) +
        shearLowerStrip p₀ p₁ d c cbar))
    | none => none
  else none

/-- **Soundness of a column.** -/
theorem lintegral_le_shearLowerColumnOf {ℓ u p₀ p₁ T s c₀ : ℚ} {N : ℤ}
    (h : shearLowerColumnOf ℓ u p₀ p₁ T s c₀ = some N) :
    ∫⁻ p in Ioc (p₀ : ℝ) p₁, shearLowerDensity ℓ u p ≤ ENNReal.ofReal (N / 2 ^ 64) := by
  unfold shearLowerColumnOf at h
  dsimp only at h
  split_ifs at h with hck
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hℓ, hp₀⟩, hp⟩, hT₀⟩, hT₁⟩, hs0⟩, hs₀⟩, hs₁⟩, hc0⟩, hside⟩ := hck
  split at h
  · rename_i m hm
    obtain rfl := Option.some.inj h
    set cbar := min u (min T s)
    set c := min cbar c₀
    set d := shearColumnGap p₀ p₁ with hd
    have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
    have hp₀' : (0 : ℝ) ≤ p₀ := by exact_mod_cast hp₀
    have hpp : (p₀ : ℝ) ≤ p₁ := by exact_mod_cast hp.le
    have hccbar : c ≤ cbar := min_le_left _ _
    have hcc₀ : c ≤ c₀ := min_le_right _ _
    -- the side of the column
    have h1 : 0 ≤ (p₀ - 1) * (p₁ - 1) := by
      rcases hside with ⟨h, _⟩ | ⟨⟨h, _⟩, _⟩ <;> nlinarith
    obtain ⟨hd0, hdp⟩ : 0 < d ∧ ∀ p ∈ Icc (p₀ : ℝ) p₁, (d : ℝ) ≤ |p - 1| := by
      rcases hside with ⟨h, _⟩ | ⟨⟨h, _⟩, _⟩
      · rw [hd, shearColumnGap_of_lt h]
        exact ⟨by linarith, fun p hp' ↦ by push_cast; linarith [neg_le_abs (p - 1), hp'.2]⟩
      · rw [hd, shearColumnGap_of_le (h.trans hp).le]
        exact ⟨by linarith, fun p hp' ↦ by push_cast; linarith [le_abs_self (p - 1), hp'.1]⟩
    have hsign : ∀ p ∈ Icc (p₀ : ℝ) p₁, ∀ t : ℝ, 0 < t → t ≤ c → shearDifference p t ≤ 0 := by
      intro p hp' t ht htc
      have htc₀ : t ≤ (c₀ : ℝ) := htc.trans (by exact_mod_cast hcc₀)
      rcases hside with ⟨h, hQ⟩ | ⟨⟨_, hb⟩, hQ⟩
      · exact shearDifference_nonpos_of_left h.le hQ (hp₀'.trans hp'.1) hp'.2 ht htc₀
      · exact shearDifference_nonpos_of_right hb hp₀ hQ hp'.1 ht htc₀
    -- the height of the column
    have hcut : ∀ p ∈ Ioc (p₀ : ℝ) p₁,
        min (u : ℝ) (min (shearMap p ℓ) (shearThreshold p)) ≤ cbar := by
      intro p hp'
      have hT := shearMap_le_of_shearHighOk_of_mem hℓ hp₀ hT₀ hT₁ (Ioc_subset_Icc_self hp')
      have hs := shearThreshold_le_of_mem hp₀ hs0 hs₀ hs₁ (Ioc_subset_Icc_self hp')
      simp only [cbar]
      push_cast
      exact min_le_min le_rfl (min_le_min hT hs)
    -- the pieces
    have hF := measurable_shearLowerIntegrand
    have hm0 : 0 ≤ m := le_of_cellWalk hm
    have hbot := lintegral_le_shearLowerStrip hp₀ hp.le le_rfl (by positivity) hd0 hdp
      (t₁ := c / 64)
    have htop := lintegral_le_shearLowerStrip hp₀ hp.le hc0.le hccbar hd0 hdp
    have hs₀' := shearLowerStrip_nonneg hp₀ hp.le le_rfl (by positivity : (0 : ℚ) ≤ c / 64) hd0
    have hs₁' := shearLowerStrip_nonneg hp₀ hp.le hc0.le hccbar hd0
    set F : ℝ → ℝ≥0∞ := fun t ↦ ∫⁻ p in Ioc (p₀ : ℝ) p₁,
      ‖shearDifference p t‖ₑ * ENNReal.ofReal (t ^ (1 / 2 : ℝ))
    have hwalk : ∫⁻ t in Ioc ((c / 64 : ℚ) : ℝ) c, F t ≤ ENNReal.ofReal (m / 2 ^ 64) := by
      simpa using lintegral_le_of_cellWalk (F := F) (g := fun q : ℚ ↦ (q : ℝ)) (K := 64)
        (fun a _ b _ hab ↦ Rat.cast_le.2 hab)
        (fun l u' n _ hlu hn ↦ lintegral_le_shearLowerCell hp₀ hp.le h1 hsign hlu hn)
        (by positivity) hc0.le hm
    calc ∫⁻ p in Ioc (p₀ : ℝ) p₁, shearLowerDensity ℓ u p
        ≤ ∫⁻ p in Ioc (p₀ : ℝ) p₁, ∫⁻ t in Ioc (0 : ℝ) cbar,
            ‖shearDifference p t‖ₑ * ENNReal.ofReal (t ^ (1 / 2 : ℝ)) :=
          setLIntegral_mono' measurableSet_Ioc fun p hp' ↦
            lintegral_mono_set (Ioc_subset_Ioc le_rfl (hcut p hp'))
      _ = ∫⁻ t in Ioc (0 : ℝ) cbar, F t := lintegral_lintegral_swap hF.aemeasurable
      _ ≤ (∫⁻ t in Ioc (0 : ℝ) ((c / 64 : ℚ) : ℝ), F t) +
          (∫⁻ t in Ioc ((c / 64 : ℚ) : ℝ) c, F t) + ∫⁻ t in Ioc (c : ℝ) cbar, F t := by
          refine (lintegral_Ioc_le_add (b := (c : ℝ)) _).trans ?_
          gcongr
          exact lintegral_Ioc_le_add _
      _ ≤ ENNReal.ofReal (shearLowerStrip p₀ p₁ d 0 (c / 64)) + ENNReal.ofReal (m / 2 ^ 64) +
          ENNReal.ofReal (shearLowerStrip p₀ p₁ d c cbar) := by
          gcongr
          · simpa using hbot
      _ ≤ ENNReal.ofReal ((m + ceilScaled 64 (shearLowerStrip p₀ p₁ d 0 (c / 64) +
          shearLowerStrip p₀ p₁ d c cbar) : ℤ) / 2 ^ 64) := by
          rw [← ENNReal.ofReal_add (by exact_mod_cast hs₀') (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by exact_mod_cast hs₁')]
          refine ENNReal.ofReal_le_ofReal ?_
          have := le_ceilScaled_real 64 (shearLowerStrip p₀ p₁ d 0 (c / 64) +
            shearLowerStrip p₀ p₁ d c cbar)
          push_cast at this ⊢
          rw [add_div]
          linarith
  · simp at h

/-- **A column** `(p₀, p₁]` with its candidates: Newton's `T(·, ℓ)` and `s_c` at the end where they
are largest (`p₀` left of `p = 1`, `p₁` right of it), and `s_c` at the inner end. -/
def shearLowerColumn (ℓ u p₀ p₁ : ℚ) : Option ℤ :=
  let pT := if p₁ < 1 then p₀ else p₁
  let pL := if p₁ < 1 then p₁ else p₀
  shearLowerColumnOf ℓ u p₀ p₁ (roundUpRel (shearMapApprox pT ℓ * (1 + 1 / 2 ^ 20)))
    (shearThresholdHigh pT) (shearThresholdLow pL)

/-- **Soundness of a column**: a column value `N` bounds `∫_{(p₀, p₁]} λ` by `N/2^64`. -/
theorem lintegral_le_shearLowerColumn {ℓ u p₀ p₁ : ℚ} {N : ℤ}
    (h : shearLowerColumn ℓ u p₀ p₁ = some N) :
    ∫⁻ p in Ioc (p₀ : ℝ) p₁, shearLowerDensity ℓ u p ≤ ENNReal.ofReal (N / 2 ^ 64) :=
  lintegral_le_shearLowerColumnOf h

/-! ### The column around `p = 1` -/

/-- `T(p, ℓ) ≤ (p² - 1)²/(ℓ (ℓ² + 2))`. -/
theorem shearMap_le_sq_div {p ℓ : ℝ} (hℓ : 0 < ℓ) :
    shearMap p ℓ ≤ (p ^ 2 - 1) ^ 2 / (ℓ * (ℓ ^ 2 + 2)) := by
  have hT := shearMap_nonneg (y₁ := p) hℓ
  have h := mul_shearCubic_eq p hℓ.ne' (shearMap p ℓ)
  rw [shearCubic_shearMap, mul_zero] at h
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg hℓ.le (pow_nonneg hT 3),
    mul_nonneg (sq_nonneg ℓ) (sq_nonneg (shearMap p ℓ)),
    mul_nonneg (mul_nonneg hℓ.le hT) (sq_nonneg p)]

/-- **The column around `p = 1`**: for `0 < δ ≤ 1`,
`∫_{1-δ}^{1+δ} λ ≤ 2δ · δ (2 + δ)(δ² + (2 + δ)²)/(2 X^{3/2})`, `X = ℓ (ℓ² + 2)`. -/
theorem lintegral_shearLowerDensity_near_le {ℓ u δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∫⁻ p in Ioc (1 - δ) (1 + δ), shearLowerDensity ℓ u p ≤
      ENNReal.ofReal (2 * δ * (δ * (2 + δ) * (δ ^ 2 + (2 + δ) ^ 2) / 2 /
        (ℓ * (ℓ ^ 2 + 2) * Real.sqrt (ℓ * (ℓ ^ 2 + 2))))) := by
  set X := ℓ * (ℓ ^ 2 + 2)
  have hX : 0 < X := by positivity
  have hsX := Real.sqrt_pos.2 hX
  set B := δ * (2 + δ) * (δ ^ 2 + (2 + δ) ^ 2) / 2 / (X * Real.sqrt X)
  have hpt : ∀ p ∈ Ioc (1 - δ) (1 + δ), shearLowerDensity ℓ u p ≤ ENNReal.ofReal B := by
    intro p hp
    by_cases hp1 : p = 1
    · subst hp1
      have h0 : min u (min (shearMap 1 ℓ) (shearThreshold 1)) ≤ 0 := by
        rw [shearMap_eq_zero_of_sq_eq_one (by norm_num),
          shearThreshold_eq_zero_of_sq_eq_one (by norm_num), min_self]
        exact min_le_right _ _
      rw [shearLowerDensity, Ioc_eq_empty (not_lt.2 h0), Measure.restrict_empty,
        lintegral_zero_measure]
      exact zero_le
    set a := |p - 1|
    set b := p + 1
    have ha : 0 < a := abs_pos.2 (sub_ne_zero.2 hp1)
    have haδ : a ≤ δ := abs_le.2 ⟨by linarith [hp.1], by linarith [hp.2]⟩
    have hb : 0 < b := by simp only [b]; linarith [hp.1]
    have hbδ : b ≤ 2 + δ := by simp only [b]; linarith [hp.2]
    set M := (p ^ 2 - 1) ^ 2 / X
    have hM : M = a ^ 2 * b ^ 2 / X := by
      simp only [M, a, b]
      rw [sq_abs]
      ring
    have hsM : Real.sqrt M = a * b / Real.sqrt X := by
      rw [hM, Real.sqrt_div' _ hX.le, Real.sqrt_mul' _ (sq_nonneg b), Real.sqrt_sq ha.le,
        Real.sqrt_sq hb.le]
    set C := 1 / (2 * b ^ 2) + 1 / (2 * a ^ 2)
    have hcut : min u (min (shearMap p ℓ) (shearThreshold p)) ≤ M :=
      (min_le_right _ _).trans ((min_le_left _ _).trans (shearMap_le_sq_div hℓ))
    calc shearLowerDensity ℓ u p
        ≤ ∫⁻ t in Ioc 0 M, ENNReal.ofReal (C * Real.sqrt M) := by
          refine (lintegral_mono_set (Ioc_subset_Ioc le_rfl hcut)).trans ?_
          refine setLIntegral_mono' measurableSet_Ioc fun t ht ↦ ?_
          rw [ENNReal.ofReal_mul (by positivity), ← ofReal_norm, Real.norm_eq_abs]
          gcongr
          · rw [shearDifference]
            refine (abs_sub _ _).trans (add_le_add ?_ ?_)
            · refine (abs_shearDensity_le _ t).trans ?_
              exact div_le_div_of_nonneg_left zero_le_one (by positivity)
                (by nlinarith [sq_nonneg t])
            · refine (abs_shearDensity_le _ t).trans ?_
              refine div_le_div_of_nonneg_left zero_le_one (by positivity) ?_
              have : a ^ 2 = (p - 1) ^ 2 := sq_abs _
              nlinarith [sq_nonneg t]
          · rw [← Real.sqrt_eq_rpow]
            exact Real.sqrt_le_sqrt ht.2
      _ = ENNReal.ofReal (C * Real.sqrt M * M) := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero,
            ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal B := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hsM, hM]
          have e : C * (a * b / Real.sqrt X) * (a ^ 2 * b ^ 2 / X) =
              a * b * (a ^ 2 + b ^ 2) / 2 / (X * Real.sqrt X) := by
            simp only [C]
            field_simp
          rw [e]
          simp only [B]
          have h₁ := pow_le_pow_left₀ ha.le haδ 2
          have h₂ := pow_le_pow_left₀ hb.le hbδ 2
          gcongr
  calc ∫⁻ p in Ioc (1 - δ) (1 + δ), shearLowerDensity ℓ u p
      ≤ ∫⁻ p in Ioc (1 - δ) (1 + δ), ENNReal.ofReal B := setLIntegral_mono' measurableSet_Ioc hpt
    _ = ENNReal.ofReal (2 * δ * B) := by
        rw [setLIntegral_const, Real.volume_Ioc, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-! ### The lower cost of a slab -/

/-- The columns left of `p = 1`: width `1/8` up to `p = 1/2`, then ratio `2/3` in `1 - p`. -/
def shearLowerNextLeft (p : ℚ) : ℚ :=
  if p < 1 / 2 then p + 1 / 8 else roundUpRel (1 - (1 - p) * (2 / 3))

/-- The columns right of `p = 1`: ratio `3/2` in `p - 1` up to `p = 5/4`, width `1/16` up to
`p = 4` and `1/8` beyond. -/
def shearLowerNextRight (p : ℚ) : ℚ :=
  if p < 5 / 4 then roundUpRel (1 + 3 / 2 * (p - 1)) else if p < 4 then p + 1 / 16 else p + 1 / 8

/-- The bound of the column `(1 - 2^-12, 1 + 2^-12]`. -/
def shearLowerNear (ℓ : ℚ) : ℚ :=
  2 * (1 / 2 ^ 12) * ((1 / 2 ^ 12) * (2 + 1 / 2 ^ 12) * ((1 / 2 ^ 12) ^ 2 + (2 + 1 / 2 ^ 12) ^ 2) /
    2 / (ℓ * (ℓ ^ 2 + 2) * sqrtLow (ℓ * (ℓ ^ 2 + 2))))

/-- **The lower cost of a slab** `ℓ ≤ A ≤ u`, on the grid `2^-64`. -/
def shearLowerSlab (ℓ u : ℚ) : Option ℤ :=
  if 0 < ℓ then
    match cellWalk shearLowerNextLeft (shearLowerColumn ℓ u) 100 0 (1 - 1 / 2 ^ 12) 0,
      cellWalk shearLowerNextRight (shearLowerColumn ℓ u) 1000 (1 + 1 / 2 ^ 12) 9 0 with
    | some a, some b => some (4 * (a + b + ceilScaled 64 (shearLowerNear ℓ)))
    | _, _ => none
  else none

/-- The region integral `4 ∫_0^9 λ` is at most the slab bound. -/
theorem lintegral_shearLowerDensity_le {ℓ u : ℚ} {N : ℤ} (h : shearLowerSlab ℓ u = some N) :
    4 * ∫⁻ p in Ioc (0 : ℝ) 9, shearLowerDensity ℓ u p ≤ ENNReal.ofReal (N / 2 ^ 64) := by
  unfold shearLowerSlab at h
  split_ifs at h with hℓ
  split at h
  · rename_i a b ha hb
    obtain rfl := Option.some.inj h
    have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
    have hmono : MonotoneOn (fun q : ℚ ↦ (q : ℝ)) (Ici 0) := fun x _ y _ hxy ↦ Rat.cast_le.2 hxy
    have hL := lintegral_le_of_cellWalk (F := shearLowerDensity ℓ u) (K := 64) hmono
      (fun l u' n _ _ hn ↦ lintegral_le_shearLowerColumn hn) le_rfl (by norm_num) ha
    have hR := lintegral_le_of_cellWalk (F := shearLowerDensity ℓ u) (K := 64) hmono
      (fun l u' n _ _ hn ↦ lintegral_le_shearLowerColumn hn) (by norm_num) (by norm_num) hb
    have hN := lintegral_shearLowerDensity_near_le (u := u) hℓ' (by norm_num : (0 : ℝ) < 1 / 2 ^ 12)
      (by norm_num)
    have ha0 : 0 ≤ a := le_of_cellWalk ha
    have hb0 : 0 ≤ b := le_of_cellWalk hb
    push_cast at hL hR
    simp only [sub_zero] at hL hR
    have hsplit : ∫⁻ p in Ioc (0 : ℝ) 9, shearLowerDensity ℓ u p ≤
        (∫⁻ p in Ioc (0 : ℝ) (1 - 1 / 2 ^ 12), shearLowerDensity ℓ u p) +
        (∫⁻ p in Ioc (1 - 1 / 2 ^ 12 : ℝ) (1 + 1 / 2 ^ 12), shearLowerDensity ℓ u p) +
        ∫⁻ p in Ioc (1 + 1 / 2 ^ 12 : ℝ) 9, shearLowerDensity ℓ u p := by
      refine (lintegral_Ioc_le_add (b := 1 + 1 / 2 ^ 12) _).trans ?_
      gcongr
      exact lintegral_Ioc_le_add (b := 1 - 1 / 2 ^ 12) _
    have hnear : ENNReal.ofReal (2 * (1 / 2 ^ 12) * ((1 / 2 ^ 12) * (2 + 1 / 2 ^ 12) *
        ((1 / 2 ^ 12) ^ 2 + (2 + 1 / 2 ^ 12) ^ 2) / 2 /
          ((ℓ : ℝ) * (ℓ ^ 2 + 2) * Real.sqrt (ℓ * (ℓ ^ 2 + 2))))) ≤
        ENNReal.ofReal ((ceilScaled 64 (shearLowerNear ℓ) : ℝ) / 2 ^ 64) := by
      refine ENNReal.ofReal_le_ofReal (le_trans ?_ (le_ceilScaled_real 64 _))
      have hX : (0 : ℚ) < ℓ * (ℓ ^ 2 + 2) := by positivity
      have hs := sqrtLow_le_sqrt hX.le
      have hs0 : (0 : ℝ) < sqrtLow (ℓ * (ℓ ^ 2 + 2)) := by exact_mod_cast sqrtLow_pos hX
      unfold shearLowerNear
      push_cast at hs hs0 ⊢
      gcongr
    have hnear0 : (0 : ℝ) ≤ (ceilScaled 64 (shearLowerNear ℓ) : ℝ) / 2 ^ 64 := by
      have := sqrtLow_pos (by positivity : (0 : ℚ) < ℓ * (ℓ ^ 2 + 2))
      have h0 : (0 : ℚ) ≤ shearLowerNear ℓ := by unfold shearLowerNear; positivity
      exact (Rat.cast_nonneg.2 h0).trans (le_ceilScaled_real 64 _)
    calc 4 * ∫⁻ p in Ioc (0 : ℝ) 9, shearLowerDensity ℓ u p
        ≤ 4 * (ENNReal.ofReal ((a : ℝ) / 2 ^ 64) +
            ENNReal.ofReal ((ceilScaled 64 (shearLowerNear ℓ) : ℝ) / 2 ^ 64) +
            ENNReal.ofReal ((b : ℝ) / 2 ^ 64)) := by
          gcongr 4 * ?_
          refine hsplit.trans (add_le_add (add_le_add hL (hN.trans hnear)) hR)
      _ = ENNReal.ofReal ((4 * (a + b + ceilScaled 64 (shearLowerNear ℓ)) : ℤ) / 2 ^ 64) := by
          rw [← ENNReal.ofReal_add (by positivity) hnear0,
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          push_cast
          ring
  · simp at h

/-- **The lower cost from a slab value**: `S_low(10, A) ≤ N/2^64` for `ℓ ≤ A ≤ u`. -/
theorem shearLowerCost_le_shearLowerSlab {ℓ u : ℚ} {N : ℤ} (h : shearLowerSlab ℓ u = some N)
    {A : ℝ} (hℓA : (ℓ : ℝ) ≤ A) (hAu : A ≤ u) :
    shearLowerCost 10 A ≤ ENNReal.ofReal (N / 2 ^ 64) := by
  have hℓ : 0 < ℓ := by
    unfold shearLowerSlab at h
    split_ifs at h with hℓ
    · exact hℓ
  exact (shearLowerCost_le_region (by exact_mod_cast hℓ) hℓA hAu).trans
    (lintegral_shearLowerDensity_le h)

/-- `s_c ≤ 8` on `[0, 9]`. -/
theorem shearThreshold_le_eight {p : ℝ} (hp : 0 ≤ p) (hp9 : p ≤ 9) : shearThreshold p ≤ 8 := by
  refine shearThreshold_le_of_shearQuartic_nonpos (by norm_num) ?_
  simp only [shearQuartic]
  nlinarith [mul_le_mul hp9 hp9 hp (by norm_num : (0 : ℝ) ≤ 9), sq_nonneg p]

/-- **The lower cost from a slab value** with `u ≥ 8`: `S_low(10, A) ≤ N/2^64` for all `A ≥ ℓ`. -/
theorem shearLowerCost_le_shearLowerSlab_top {ℓ u : ℚ} {N : ℤ} (hu : 8 ≤ u)
    (h : shearLowerSlab ℓ u = some N) {A : ℝ} (hℓA : (ℓ : ℝ) ≤ A) :
    shearLowerCost 10 A ≤ ENNReal.ofReal (N / 2 ^ 64) := by
  have hℓ : 0 < ℓ := by
    unfold shearLowerSlab at h
    split_ifs at h with hℓ
    · exact hℓ
  refine (shearLowerCost_le_region_top (by exact_mod_cast hℓ) hℓA).trans
    ((le_of_eq ?_).trans (lintegral_shearLowerDensity_le h))
  congr 1
  refine setLIntegral_congr_fun measurableSet_Ioc fun p hp ↦ ?_
  simp only [shearLowerDensity]
  congr 2
  have hs := shearThreshold_le_eight hp.1.le hp.2
  have hu' : (8 : ℝ) ≤ u := by exact_mod_cast hu
  rw [min_eq_right ((min_le_right _ _).trans (hs.trans hu'))]

end IncompressibleFlow.SharpHolder
