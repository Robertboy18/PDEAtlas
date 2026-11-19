/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarHessian
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The kernel of the horizontal Hölder estimate of the strain

For the half-plane Biot–Savart law the strain `u_x` has the kernel `K₁(y) = y₁ y₂ / |y|⁴`
(Chen and Hou, Part I, (3.1)). Written in coordinates it is `strainDensity a b = a b / (a² + b²)²`.
After scaling the two points of a horizontal difference to `(± 1/2, 0)`, the difference
`u_x(1/2, ·) - u_x(-1/2, ·)` has the kernel

`Δ(s₁, s₂) = K₁(s₁ + 1/2, s₂) - K₁(s₁ - 1/2, s₂)`,

`strainDifference s₁ s₂` here (Part I, (3.9)). The results below are its algebra: the sign of
`Δ`, its threshold and its primitive. The transport map of the estimate pairs points with equal
values of the primitive `Φ`.

## Main definitions

* `strainDensity`: the kernel `K₁(a, b) = a b / (a² + b²)²`.
* `strainDifference`: the difference kernel `Δ(s₁, s₂)`.
* `strainQuartic`: the quartic `Δ₁ = s₂⁴ - 2 s₁² s₂² - 3 s₁⁴ + s₁²/2 + s₂²/2 + 1/16`, which
  carries the sign of `Δ`.
* `strainThreshold`: the threshold (3.10),
  `f(s₂) = ((1/2 - 2 s₂² + √(16 s₂⁴ + 4 s₂² + 1)) / 6)^{1/2}`.
* `strainPotential`: the primitive
  `Φ(t) = (s₂/2) (1 / ((t - 1/2)² + s₂²) - 1 / ((t + 1/2)² + s₂²))` of `Δ(·, s₂)`.

## Main results

* `strainDifference_eq`: `Δ = s₂ Δ₁ / (((s₁ + 1/2)² + s₂²)² ((s₁ - 1/2)² + s₂²)²)`.
* `strainQuartic_eq`: `Δ₁ = -3 (s₁² - f(s₂)²)(s₁² - u₋)` with `u₋ < 0`.
* `strainDifference_pos_iff`, `strainDifference_neg_iff`: for `s₂ > 0` and `s₁ ≥ 0` the kernel
  is positive for `s₁ < f(s₂)` and negative for `s₁ > f(s₂)` (3.11).
* `one_half_le_strainThreshold`, `monotoneOn_strainThreshold`: `f ≥ 1/2` and `f` increases in
  `s₂ ≥ 0` (Part II, Supplement, Lemma 5.3).
* `integral_strainDifference`: `∫_u^v Δ(·, s₂) = Φ(v) - Φ(u)`, with `Φ(0) = 0` and `Φ(t) → 0` as
  `t → ∞` (`strainPotential_zero`, `tendsto_strainPotential_atTop`).
* `strictMonoOn_strainPotential`, `strictAntiOn_strainPotential`: `Φ` is strictly increasing on
  `[0, f]` and strictly decreasing on `[f, ∞)`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, (3.1), p. 27, and Section 3.3,
  (3.9)-(3.11), p. 31.
  <https://arxiv.org/abs/2210.07191v4>
* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Supplementary material II,
  Section 5.3, Lemma 5.3, p. 8.
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace IncompressibleFlow.SharpHolder

/-! ### The kernel `K₁` in coordinates -/

/-- The strain kernel `K₁(a, b) = a b / (a² + b²)²` of Chen and Hou, Part I, (3.1), in
coordinates: the planar Hessian kernel `hessianKernel 0 1` at `(a, b)`. Its value at the origin is
`0`. -/
def strainDensity (a b : ℝ) : ℝ :=
  PotentialTheory.Planar.hessianKernel 0 1 !₂[a, b]

/-- `K₁(a, b) = a b / (a² + b²)²`. -/
theorem strainDensity_eq (a b : ℝ) : strainDensity a b = a * b / (a ^ 2 + b ^ 2) ^ 2 :=
  PotentialTheory.Planar.hessianKernel_zero_one_toLp a b

/-- `K₁` is odd in its first argument. -/
theorem strainDensity_neg_left (a b : ℝ) : strainDensity (-a) b = -strainDensity a b := by
  simp only [strainDensity_eq, neg_sq]
  ring

/-- `K₁` is odd in its second argument. -/
theorem strainDensity_neg_right (a b : ℝ) : strainDensity a (-b) = -strainDensity a b := by
  simp only [strainDensity_eq, neg_sq]
  ring

/-- `K₁` is symmetric under the exchange of its arguments. -/
theorem strainDensity_comm (a b : ℝ) : strainDensity a b = strainDensity b a := by
  simp only [strainDensity_eq]
  ring

/-- `|K₁(a, b)| ≤ 1 / (2 (a² + b²))`. -/
theorem abs_strainDensity_le (a b : ℝ) : |strainDensity a b| ≤ 1 / (2 * (a ^ 2 + b ^ 2)) := by
  rcases eq_or_lt_of_le (add_nonneg (sq_nonneg a) (sq_nonneg b)) with h | h
  · rw [← h]
    have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    simp [strainDensity_eq, ha, hb]
  · rw [strainDensity_eq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (a ^ 2 + b ^ 2) ^ 2),
      div_le_div_iff₀ (by positivity) (by positivity), abs_mul]
    have : 2 * (|a| * |b|) ≤ a ^ 2 + b ^ 2 := by
      nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
    nlinarith [mul_nonneg (abs_nonneg a) (abs_nonneg b)]

/-- The primitive `-(b/2) / (a² + b²)` of `K₁(·, b)`. -/
def strainPrimitive (b a : ℝ) : ℝ :=
  -(b / 2) / (a ^ 2 + b ^ 2)

/-- `-(b/2)/(a² + b²)` is a primitive of `K₁(·, b)` for `b ≠ 0`. -/
theorem hasDerivAt_strainPrimitive {b : ℝ} (hb : b ≠ 0) (a : ℝ) :
    HasDerivAt (strainPrimitive b) (strainDensity a b) a := by
  have hpos : a ^ 2 + b ^ 2 ≠ 0 := by positivity
  have hg : HasDerivAt (fun a ↦ a ^ 2 + b ^ 2) (2 * a) a := by
    simpa using (hasDerivAt_pow 2 a).add_const (b ^ 2)
  have h := (hasDerivAt_const a (-(b / 2))).div hg hpos
  have e : strainDensity a b =
      (0 * (a ^ 2 + b ^ 2) - -(b / 2) * (2 * a)) / (a ^ 2 + b ^ 2) ^ 2 := by
    simp only [strainDensity_eq]
    field_simp
    ring
  rw [e]
  exact h

/-- `K₁(·, b)` is continuous for `b ≠ 0`. -/
theorem continuous_strainDensity_left {b : ℝ} (hb : b ≠ 0) :
    Continuous fun a ↦ strainDensity a b := by
  simp only [strainDensity_eq]
  exact Continuous.div (by fun_prop) (by fun_prop) fun a ↦ by positivity

/-- For `b ≠ 0`, `K₁(·, b)` is integrable on the line. -/
theorem integrable_strainDensity_left {b : ℝ} (hb : b ≠ 0) :
    Integrable fun a ↦ strainDensity a b := by
  have hc : Integrable fun a : ℝ ↦ (1 + (a / b) ^ 2)⁻¹ := integrable_inv_one_add_sq.comp_div hb
  refine (hc.const_mul (1 / (2 * b ^ 2))).mono'
    (continuous_strainDensity_left hb).aestronglyMeasurable (Eventually.of_forall fun a ↦ ?_)
  rw [Real.norm_eq_abs]
  refine (abs_strainDensity_le a b).trans (le_of_eq ?_)
  have hb2 : b ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-! ### The difference kernel and its sign -/

/-- The kernel `Δ(s₁, s₂) = K₁(s₁ + 1/2, s₂) - K₁(s₁ - 1/2, s₂)` of the horizontal difference
`u_x(1/2, ·) - u_x(-1/2, ·)`, Chen and Hou, Part I, (3.9). -/
def strainDifference (s₁ s₂ : ℝ) : ℝ :=
  strainDensity (s₁ + 1 / 2) s₂ - strainDensity (s₁ - 1 / 2) s₂

/-- The quartic `Δ₁` of Chen and Hou, Part I, Section 3.3, which carries the sign of `Δ`. -/
def strainQuartic (s₁ s₂ : ℝ) : ℝ :=
  s₂ ^ 4 - 2 * s₁ ^ 2 * s₂ ^ 2 - 3 * s₁ ^ 4 + s₁ ^ 2 / 2 + s₂ ^ 2 / 2 + 1 / 16

/-- The sign threshold `f(s₂) = ((1/2 - 2 s₂² + √(16 s₂⁴ + 4 s₂² + 1)) / 6)^{1/2}` of Chen and
Hou, Part I, (3.10): for `s₂ ≠ 0`, the positive zero of `Δ(·, s₂)` (at `s₂ = 0` the kernel
vanishes identically). -/
def strainThreshold (s₂ : ℝ) : ℝ :=
  Real.sqrt ((1 / 2 - 2 * s₂ ^ 2 + Real.sqrt (16 * s₂ ^ 4 + 4 * s₂ ^ 2 + 1)) / 6)

/-- `Δ` is even in `s₁`. -/
theorem strainDifference_neg_left (s₁ s₂ : ℝ) :
    strainDifference (-s₁) s₂ = strainDifference s₁ s₂ := by
  simp only [strainDifference]
  rw [show -s₁ + 1 / 2 = -(s₁ - 1 / 2) by ring, show -s₁ - 1 / 2 = -(s₁ + 1 / 2) by ring,
    strainDensity_neg_left, strainDensity_neg_left]
  ring

/-- `Δ` is odd in `s₂`. -/
theorem strainDifference_neg_right (s₁ s₂ : ℝ) :
    strainDifference s₁ (-s₂) = -strainDifference s₁ s₂ := by
  simp only [strainDifference, strainDensity_neg_right]
  ring

/-- `Δ = s₂ Δ₁ / (((s₁ + 1/2)² + s₂²)² ((s₁ - 1/2)² + s₂²)²)`, Part I, Section 3.3. -/
theorem strainDifference_eq {s₁ s₂ : ℝ} (h : s₂ ≠ 0) :
    strainDifference s₁ s₂ = s₂ * strainQuartic s₁ s₂ /
      (((s₁ + 1 / 2) ^ 2 + s₂ ^ 2) ^ 2 * ((s₁ - 1 / 2) ^ 2 + s₂ ^ 2) ^ 2) := by
  have h₁ : (s₁ + 1 / 2) ^ 2 + s₂ ^ 2 ≠ 0 := by positivity
  have h₂ : (s₁ - 1 / 2) ^ 2 + s₂ ^ 2 ≠ 0 := by positivity
  simp only [strainDifference, strainDensity_eq, strainQuartic]
  field_simp
  ring

/-- `|1/2 - 2 s₂²| < (16 s₂⁴ + 4 s₂² + 1)^{1/2}`, so the radicand of `f(s₂)²` is positive. -/
private theorem sqrt_disc_gt (s₂ : ℝ) :
    |1 / 2 - 2 * s₂ ^ 2| < Real.sqrt (16 * s₂ ^ 4 + 4 * s₂ ^ 2 + 1) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith [sq_nonneg s₂, sq_nonneg (s₂ ^ 2)])

/-- The square of the threshold. -/
theorem strainThreshold_sq (s₂ : ℝ) :
    strainThreshold s₂ ^ 2 =
      (1 / 2 - 2 * s₂ ^ 2 + Real.sqrt (16 * s₂ ^ 4 + 4 * s₂ ^ 2 + 1)) / 6 := by
  rw [strainThreshold, Real.sq_sqrt]
  have := sqrt_disc_gt s₂
  have := neg_abs_le (1 / 2 - 2 * s₂ ^ 2)
  linarith

/-- The threshold is nonnegative. -/
theorem strainThreshold_nonneg (s₂ : ℝ) : 0 ≤ strainThreshold s₂ := Real.sqrt_nonneg _

/-- `Δ₁ = -3 (s₁² - f²) (s₁² - u₋)` with `u₋ = (1/2 - 2 s₂² - √(16 s₂⁴ + 4 s₂² + 1)) / 6 < 0`. -/
theorem strainQuartic_eq (s₁ s₂ : ℝ) :
    strainQuartic s₁ s₂ = -3 * (s₁ ^ 2 - strainThreshold s₂ ^ 2) *
      (s₁ ^ 2 - (1 / 2 - 2 * s₂ ^ 2 - Real.sqrt (16 * s₂ ^ 4 + 4 * s₂ ^ 2 + 1)) / 6) := by
  have hw := Real.sq_sqrt (show (0 : ℝ) ≤ 16 * s₂ ^ 4 + 4 * s₂ ^ 2 + 1 by positivity)
  rw [strainThreshold_sq, strainQuartic]
  linear_combination (-1 / 12 : ℝ) * hw

/-- `Δ₁ > 0` exactly below the threshold, for `s₁ ≥ 0`. -/
theorem strainQuartic_pos_iff {s₁ : ℝ} (hs₁ : 0 ≤ s₁) (s₂ : ℝ) :
    0 < strainQuartic s₁ s₂ ↔ s₁ < strainThreshold s₂ := by
  have hneg :
      0 < s₁ ^ 2 - (1 / 2 - 2 * s₂ ^ 2 - Real.sqrt (16 * s₂ ^ 4 + 4 * s₂ ^ 2 + 1)) / 6 := by
    have := sqrt_disc_gt s₂
    have := le_abs_self (1 / 2 - 2 * s₂ ^ 2)
    nlinarith [sq_nonneg s₁]
  rw [strainQuartic_eq]
  have hf := strainThreshold_nonneg s₂
  constructor
  · intro h
    by_contra hle
    push Not at hle
    have : 0 ≤ s₁ ^ 2 - strainThreshold s₂ ^ 2 := by nlinarith
    nlinarith
  · intro h
    have : s₁ ^ 2 - strainThreshold s₂ ^ 2 < 0 := by nlinarith
    nlinarith

/-- `Δ₁ < 0` exactly above the threshold, for `s₁ ≥ 0`. -/
theorem strainQuartic_neg_iff {s₁ : ℝ} (hs₁ : 0 ≤ s₁) (s₂ : ℝ) :
    strainQuartic s₁ s₂ < 0 ↔ strainThreshold s₂ < s₁ := by
  have hneg :
      0 < s₁ ^ 2 - (1 / 2 - 2 * s₂ ^ 2 - Real.sqrt (16 * s₂ ^ 4 + 4 * s₂ ^ 2 + 1)) / 6 := by
    have := sqrt_disc_gt s₂
    have := le_abs_self (1 / 2 - 2 * s₂ ^ 2)
    nlinarith [sq_nonneg s₁]
  rw [strainQuartic_eq]
  have hf := strainThreshold_nonneg s₂
  constructor
  · intro h
    by_contra hle
    push Not at hle
    have : s₁ ^ 2 - strainThreshold s₂ ^ 2 ≤ 0 := by nlinarith
    nlinarith
  · intro h
    have : 0 < s₁ ^ 2 - strainThreshold s₂ ^ 2 := by nlinarith
    nlinarith

/-- The threshold is a zero of `Δ₁`. -/
theorem strainQuartic_strainThreshold (s₂ : ℝ) : strainQuartic (strainThreshold s₂) s₂ = 0 := by
  rw [strainQuartic_eq]
  ring

/-- For `s₂ > 0` and `s₁ ≥ 0`, `Δ(s₁, s₂) > 0` exactly when `s₁ < f(s₂)`, Part I, (3.11). -/
theorem strainDifference_pos_iff {s₁ s₂ : ℝ} (hs₁ : 0 ≤ s₁) (hs₂ : 0 < s₂) :
    0 < strainDifference s₁ s₂ ↔ s₁ < strainThreshold s₂ := by
  rw [strainDifference_eq hs₂.ne', ← strainQuartic_pos_iff hs₁ s₂]
  have hd : 0 < ((s₁ + 1 / 2) ^ 2 + s₂ ^ 2) ^ 2 * ((s₁ - 1 / 2) ^ 2 + s₂ ^ 2) ^ 2 := by positivity
  rw [div_pos_iff_of_pos_right hd]
  exact ⟨fun h ↦ pos_of_mul_pos_right h hs₂.le, fun h ↦ mul_pos hs₂ h⟩

/-- For `s₂ > 0` and `s₁ ≥ 0`, `Δ(s₁, s₂) < 0` exactly when `s₁ > f(s₂)`, Part I, (3.11). -/
theorem strainDifference_neg_iff {s₁ s₂ : ℝ} (hs₁ : 0 ≤ s₁) (hs₂ : 0 < s₂) :
    strainDifference s₁ s₂ < 0 ↔ strainThreshold s₂ < s₁ := by
  rw [strainDifference_eq hs₂.ne', ← strainQuartic_neg_iff hs₁ s₂]
  have hd : 0 < ((s₁ + 1 / 2) ^ 2 + s₂ ^ 2) ^ 2 * ((s₁ - 1 / 2) ^ 2 + s₂ ^ 2) ^ 2 := by positivity
  rw [div_neg_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact absurd h (not_lt.2 hd.le)
    · exact neg_of_mul_neg_right h hs₂.le
  · intro h
    exact Or.inr ⟨mul_neg_of_pos_of_neg hs₂ h, hd⟩

/-- The threshold is at least `1/2`, Part II, Supplement, Lemma 5.3. -/
theorem one_half_le_strainThreshold (s₂ : ℝ) : 1 / 2 ≤ strainThreshold s₂ := by
  rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  refine Real.sqrt_le_sqrt ?_
  have : 1 + 2 * s₂ ^ 2 ≤ Real.sqrt (16 * s₂ ^ 4 + 4 * s₂ ^ 2 + 1) :=
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg s₂, sq_nonneg (s₂ ^ 2)])
  linarith

/-- The threshold is positive. -/
theorem strainThreshold_pos (s₂ : ℝ) : 0 < strainThreshold s₂ :=
  lt_of_lt_of_le (by norm_num) (one_half_le_strainThreshold s₂)

/-- The threshold increases in `s₂ ≥ 0`, Part II, Supplement, Lemma 5.3. -/
theorem monotoneOn_strainThreshold : MonotoneOn strainThreshold (Ici 0) := by
  intro u hu v hv huv
  have hu' : 0 ≤ u := hu
  refine Real.sqrt_le_sqrt (div_le_div_of_nonneg_right ?_ (by norm_num))
  set U := u ^ 2
  set V := v ^ 2
  have hUV : U ≤ V := by simp only [U, V]; nlinarith
  have hU : 0 ≤ U := sq_nonneg u
  have hu4 : u ^ 4 = U ^ 2 := by ring
  have hv4 : v ^ 4 = V ^ 2 := by ring
  rw [hu4, hv4]
  set a := Real.sqrt (16 * U ^ 2 + 4 * U + 1)
  set b := Real.sqrt (16 * V ^ 2 + 4 * V + 1)
  have ha := Real.sq_sqrt (show (0 : ℝ) ≤ 16 * U ^ 2 + 4 * U + 1 by positivity)
  have hb := Real.sq_sqrt (show (0 : ℝ) ≤ 16 * V ^ 2 + 4 * V + 1 by positivity)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hale : a ≤ 4 * U + 1 := Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
  have hble : b ≤ 4 * V + 1 := Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
  -- `(b - a)(b + a) = (V - U)(16 (U + V) + 4) ≥ 2 (V - U)(a + b)`
  have hprod : (b - a) * (b + a) = (V - U) * (16 * (U + V) + 4) := by nlinarith
  have hsum : 2 * (a + b) ≤ 16 * (U + V) + 4 := by nlinarith
  by_cases hab : a + b = 0
  · nlinarith
  · have hpos : 0 < a + b := lt_of_le_of_ne (by positivity) (Ne.symm hab)
    have : 2 * (V - U) ≤ b - a := by
      have h1 : 2 * (V - U) * (a + b) ≤ (b - a) * (b + a) := by
        rw [hprod]; nlinarith
      have h2 : (b - a) * (b + a) = (b - a) * (a + b) := by ring
      rw [h2] at h1
      exact le_of_mul_le_mul_right h1 hpos
    linarith

/-! ### The primitive -/

/-- The primitive `Φ(t) = (s₂/2) (1 / ((t - 1/2)² + s₂²) - 1 / ((t + 1/2)² + s₂²))` of
`Δ(·, s₂)`. The transport map of the horizontal estimate pairs points with equal `Φ`. -/
def strainPotential (s₂ t : ℝ) : ℝ :=
  strainPrimitive s₂ (t + 1 / 2) - strainPrimitive s₂ (t - 1 / 2)

/-- The primitive in closed form. -/
theorem strainPotential_eq (s₂ t : ℝ) :
    strainPotential s₂ t =
      s₂ / 2 * (1 / ((t - 1 / 2) ^ 2 + s₂ ^ 2) - 1 / ((t + 1 / 2) ^ 2 + s₂ ^ 2)) := by
  simp only [strainPotential, strainPrimitive]
  ring

/-- `Φ' = Δ(·, s₂)` for `s₂ ≠ 0`. -/
theorem hasDerivAt_strainPotential {s₂ : ℝ} (h : s₂ ≠ 0) (t : ℝ) :
    HasDerivAt (strainPotential s₂) (strainDifference t s₂) t := by
  exact ((hasDerivAt_strainPrimitive h (t + 1 / 2)).comp_add_const t (1 / 2)).sub
    ((hasDerivAt_strainPrimitive h (t - 1 / 2)).comp_sub_const t (1 / 2))

/-- `Φ` is continuous for `s₂ ≠ 0`. -/
theorem continuous_strainPotential {s₂ : ℝ} (h : s₂ ≠ 0) : Continuous (strainPotential s₂) :=
  continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_strainPotential h t).continuousAt

/-- `Φ(0) = 0`. -/
theorem strainPotential_zero (s₂ : ℝ) : strainPotential s₂ 0 = 0 := by
  simp only [strainPotential, strainPrimitive]
  ring

/-- `Φ(t) → 0` as `t → ∞`. -/
theorem tendsto_strainPotential_atTop (s₂ : ℝ) :
    Tendsto (strainPotential s₂) atTop (𝓝 0) := by
  have h : ∀ c : ℝ, Tendsto (fun t : ℝ ↦ strainPrimitive s₂ (t + c)) atTop (𝓝 0) := by
    intro c
    have hden : Tendsto (fun t : ℝ ↦ (t + c) ^ 2 + s₂ ^ 2) atTop atTop :=
      tendsto_atTop_add_const_right _ _
        ((tendsto_pow_atTop (by norm_num)).comp (tendsto_atTop_add_const_right _ c tendsto_id))
    have := hden.inv_tendsto_atTop.const_mul (-(s₂ / 2))
    simpa [strainPrimitive, div_eq_mul_inv] using this
  have := (h (1 / 2)).sub (h (-(1 / 2)))
  rw [sub_zero] at this
  refine this.congr' (Eventually.of_forall fun t ↦ ?_)
  simp only [strainPotential, sub_eq_add_neg]

/-- `Δ(·, s₂)` is continuous for `s₂ ≠ 0`. -/
theorem continuous_strainDifference_left {s₂ : ℝ} (h : s₂ ≠ 0) :
    Continuous fun s₁ ↦ strainDifference s₁ s₂ :=
  ((continuous_strainDensity_left h).comp (continuous_id.add continuous_const)).sub
    ((continuous_strainDensity_left h).comp (continuous_id.sub continuous_const))

/-- `Δ(·, s₂)` is integrable on the line for `s₂ ≠ 0`. -/
theorem integrable_strainDifference_left {s₂ : ℝ} (h : s₂ ≠ 0) :
    Integrable fun s₁ ↦ strainDifference s₁ s₂ :=
  ((integrable_strainDensity_left h).comp_add_right _).sub
    ((integrable_strainDensity_left h).comp_sub_right _)

/-- `∫_u^v Δ(·, s₂) = Φ(v) - Φ(u)`. -/
theorem integral_strainDifference {s₂ : ℝ} (h : s₂ ≠ 0) (u v : ℝ) :
    ∫ t in u..v, strainDifference t s₂ = strainPotential s₂ v - strainPotential s₂ u :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hasDerivAt_strainPotential h t)
    ((continuous_strainDifference_left h).intervalIntegrable _ _)

/-- The kernel has zero mass on the half-line: `∫_0^∞ Δ(·, s₂) = 0`. -/
theorem integral_Ioi_strainDifference {s₂ : ℝ} (h : s₂ ≠ 0) :
    ∫ t in Ioi 0, strainDifference t s₂ = 0 := by
  have := integral_Ioi_of_hasDerivAt_of_tendsto (a := 0)
    (continuous_strainPotential h).continuousWithinAt
    (fun t _ ↦ hasDerivAt_strainPotential h t)
    (integrable_strainDifference_left h).integrableOn (tendsto_strainPotential_atTop s₂)
  rw [this, strainPotential_zero, sub_zero]

/-- `Φ` is strictly increasing on `[0, f(s₂)]`. -/
theorem strictMonoOn_strainPotential {s₂ : ℝ} (h : 0 < s₂) :
    StrictMonoOn (strainPotential s₂) (Icc 0 (strainThreshold s₂)) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (continuous_strainPotential h.ne').continuousOn fun t ht ↦ ?_
  rw [interior_Icc] at ht
  rw [(hasDerivAt_strainPotential h.ne' t).deriv]
  exact (strainDifference_pos_iff ht.1.le h).2 ht.2

/-- `Φ` is strictly decreasing on `[f(s₂), ∞)`. -/
theorem strictAntiOn_strainPotential {s₂ : ℝ} (h : 0 < s₂) :
    StrictAntiOn (strainPotential s₂) (Ici (strainThreshold s₂)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ici _)
    (continuous_strainPotential h.ne').continuousOn fun t ht ↦ ?_
  rw [interior_Ici] at ht
  rw [(hasDerivAt_strainPotential h.ne' t).deriv]
  exact (strainDifference_neg_iff ((strainThreshold_nonneg s₂).trans ht.le) h).2 ht

end IncompressibleFlow.SharpHolder
