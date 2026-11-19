/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarRectangleIntegrals
public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.QuadrantSymmetrization
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# Constants of the sharp Hölder estimates: `|K₂|` across the diagonal and with a half power

Closed forms of Chen and Hou II, Supplementary material II, Sections 5.1.2 and 5.1.5, with
`K₂ = hessianKernel 0 0` and `f_s(t) = ∫₀ᵗ s² / (1 + s⁴) ds` (`halfPowerIntegral`). On a
rectangle of the closed first quadrant `∫_Q |K₂|` is one logarithm and six arctangents of the
corners; the sign of `K₂` changes on the diagonal, where the inner integral is split.

The integrals with a half power touch the pole; they are stated as iterated integrals, as in the
paper, and proved by the fundamental theorem of calculus with an integrable singularity
`y₂^{-1/2}` at the corner.

## Main definitions

* `halfPowerIntegral`: `f_s(t) = ∫₀ᵗ s² / (1 + s⁴) ds`.

## Main results

* `halfPowerIntegral_eq`: `f_s(t) = (log ((t² - √2 t + 1)/(t² + √2 t + 1)) + 2 arctan (√2 t + 1)
  + 2 arctan (√2 t - 1)) / (4√2)`; `halfPowerIntegral_one`: `f_s(1) = (π - 2 log (1 + √2))/(4√2)`.
* `tendsto_halfPowerIntegral_atTop`, `integral_Ioi_sq_div_one_add_pow_four`:
  `f_s(∞) = π / (2√2)`.
* `integral_div_sq_add_sq_mul_sqrt`: for `p > 0` and `0 ≤ a ≤ b`,
  `∫_a^b p √s / (p² + s²) ds = 2 √p (f_s(√(b/p)) - f_s(√(a/p)))`, (5.6).
* `integral_integral_abs_hessianKernel_zero_zero`, `integral_rectangle_abs_hessianKernel_zero_zero`:
  `∫_Q |K₂|` on every rectangle of the closed first quadrant avoiding the origin.
* `integral_square_abs_hessianKernel_zero_zero`:
  `F_diag(a, b) = ∫_{[a,b]²} |K₂| = (1/2) log (b/a) - (π/4 - arctan (a/b))`, (5.10).
* `integral_squareAnnulus_abs_hessianKernel_zero_one`,
  `integral_squareAnnulus_abs_hessianKernel_zero_zero`:
  `∫_{[-b,b]² \ [-a,a]²} |Kᵢ| = 2 log (b/a)`, (5.18).
* `integral_integral_abs_hessianKernel_zero_zero_mul_sqrt`: for `a, b > 0`,
  `∫₀^b (∫₀^a |K₂| dy₁) y₂^{1/2} dy₂` is `√b - √a f_s(√(b/a))` for `b ≤ a` and
  `√a (1 - 2 f_s(1) + f_s(√(b/a)))` for `a ≤ b` (the strip formulas after (5.9), whose
  absolute values are redundant), and `√m (1 - f_s(1))` on `[0, m]²`
  (`integral_integral_abs_hessianKernel_zero_zero_mul_sqrt_self`, (5.9)).
* `integral_integral_abs_hessianKernel_zero_zero_mul_sqrt_parabola`:
  `C_{K₂,low} = ∫₀¹ ∫₀^{y₁²} |K₂| y₂^{1/2} dy₂ dy₁ = (log 2 - 2 f_s(1)) / 2`,
  (5.11)-(5.12).

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Supplementary
  material II, Sections 5.1.2 and 5.1.5, (5.5)-(5.12) and (5.18).
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology PDE.Analysis
open scoped Interval

namespace PotentialTheory.Planar

/-! ### The function `f_s` -/

/-- `f_s(t) = ∫₀ᵗ s² / (1 + s⁴) ds` of Chen and Hou II, Supp. (5.5), the primitive behind
the integrals of the Biot–Savart kernels against a half power: by `s ↦ s²`,
`∫_0^x √s / (1 + s²) ds = 2 f_s(√x)` (`integral_div_sq_add_sq_mul_sqrt`). -/
def halfPowerIntegral (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, s ^ 2 / (1 + s ^ 4)

/-- The integrand `s ↦ s² / (1 + s⁴)` of `f_s` is continuous. -/
theorem continuous_sq_div_one_add_pow_four : Continuous fun s : ℝ ↦ s ^ 2 / (1 + s ^ 4) :=
  continuous_pow 2 |>.div (by fun_prop) fun s ↦ by positivity

/-- The derivative of `f_s` at `t` is `t² / (1 + t⁴)`. -/
theorem hasDerivAt_halfPowerIntegral (t : ℝ) :
    HasDerivAt halfPowerIntegral (t ^ 2 / (1 + t ^ 4)) t :=
  intervalIntegral.integral_hasDerivAt_right
    (continuous_sq_div_one_add_pow_four.intervalIntegrable 0 t)
    (continuous_sq_div_one_add_pow_four.stronglyMeasurableAtFilter _ _)
    continuous_sq_div_one_add_pow_four.continuousAt

/-- `f_s` is continuous. -/
theorem continuous_halfPowerIntegral : Continuous halfPowerIntegral :=
  continuous_iff_continuousAt.mpr fun t ↦ (hasDerivAt_halfPowerIntegral t).continuousAt

/-- `f_s(0) = 0`. -/
@[simp] theorem halfPowerIntegral_zero : halfPowerIntegral 0 = 0 := by
  simp [halfPowerIntegral]

/-- `f_s` is nondecreasing. -/
theorem monotone_halfPowerIntegral : Monotone halfPowerIntegral :=
  monotone_of_deriv_nonneg (fun t ↦ (hasDerivAt_halfPowerIntegral t).differentiableAt)
    fun t ↦ by rw [(hasDerivAt_halfPowerIntegral t).deriv]; positivity

/-- `(√2)² = 2`. -/
private theorem sqrt_two_sq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)

/-- `t² - √2 t + 1 > 0` for every real `t`. -/
private theorem quadratic_minus_pos (t : ℝ) : 0 < t ^ 2 - √2 * t + 1 := by
  nlinarith [sq_nonneg (t - √2 / 2), sqrt_two_sq]

/-- `t² + √2 t + 1 > 0` for every real `t`. -/
private theorem quadratic_plus_pos (t : ℝ) : 0 < t ^ 2 + √2 * t + 1 := by
  nlinarith [sq_nonneg (t + √2 / 2), sqrt_two_sq]

/-- The closed form of `f_s` with the logarithm split. -/
private def halfPowerClosed (t : ℝ) : ℝ :=
  (Real.log (t ^ 2 - √2 * t + 1) - Real.log (t ^ 2 + √2 * t + 1) +
    2 * Real.arctan (√2 * t + 1) + 2 * Real.arctan (√2 * t - 1)) / (4 * √2)

/-- The closed form of `f_s` has derivative `t² / (1 + t⁴)`, the integrand of `f_s`. -/
private theorem hasDerivAt_halfPowerClosed (t : ℝ) :
    HasDerivAt halfPowerClosed (t ^ 2 / (1 + t ^ 4)) t := by
  have hr := sqrt_two_sq
  have hr0 : (0 : ℝ) < √2 := by positivity
  have hA := quadratic_minus_pos t
  have hB := quadratic_plus_pos t
  have h1 : HasDerivAt (fun t ↦ t ^ 2 - √2 * t + 1) (2 * t - √2) t := by
    have := ((hasDerivAt_pow 2 t).sub ((hasDerivAt_id' t).const_mul √2)).add_const 1
    convert this using 1; simp
  have h2 : HasDerivAt (fun t ↦ t ^ 2 + √2 * t + 1) (2 * t + √2) t := by
    have := ((hasDerivAt_pow 2 t).add ((hasDerivAt_id' t).const_mul √2)).add_const 1
    convert this using 1; simp
  have ha1 := (Real.hasDerivAt_arctan (√2 * t + 1)).comp t
    (((hasDerivAt_id' t).const_mul √2).add_const 1)
  have ha2 := (Real.hasDerivAt_arctan (√2 * t - 1)).comp t
    (((hasDerivAt_id' t).const_mul √2).sub_const 1)
  have h := ((((h1.log hA.ne').sub (h2.log hB.ne')).add (ha1.const_mul 2)).add
    (ha2.const_mul 2)).div_const (4 * √2)
  refine h.congr_deriv ?_
  have e1 : 1 + (√2 * t + 1) ^ 2 = 2 * (t ^ 2 + √2 * t + 1) := by nlinarith [hr]
  have e2 : 1 + (√2 * t - 1) ^ 2 = 2 * (t ^ 2 - √2 * t + 1) := by nlinarith [hr]
  have e3 : (t ^ 2 - √2 * t + 1) * (t ^ 2 + √2 * t + 1) = 1 + t ^ 4 := by nlinarith [hr]
  rw [e1, e2]
  have hA' := hA.ne'
  have hB' := hB.ne'
  have step : (2 * t - √2) / (t ^ 2 - √2 * t + 1) - (2 * t + √2) / (t ^ 2 + √2 * t + 1) +
      2 * (1 / (2 * (t ^ 2 + √2 * t + 1)) * (√2 * 1)) +
      2 * (1 / (2 * (t ^ 2 - √2 * t + 1)) * (√2 * 1)) =
      2 * t / (t ^ 2 - √2 * t + 1) - 2 * t / (t ^ 2 + √2 * t + 1) := by
    field_simp
    ring
  have step2 : 2 * t / (t ^ 2 - √2 * t + 1) - 2 * t / (t ^ 2 + √2 * t + 1) =
      4 * √2 * t ^ 2 / (1 + t ^ 4) := by
    rw [div_sub_div _ _ hA' hB', e3]
    ring
  rw [step, step2]
  field_simp

/-- The closed form of `f_s` vanishes at `0`. -/
private theorem halfPowerClosed_zero : halfPowerClosed 0 = 0 := by
  simp [halfPowerClosed, Real.arctan_neg]

/-- `f_s` agrees with its closed form `halfPowerClosed` at every `t`. -/
private theorem halfPowerIntegral_eq_closed (t : ℝ) : halfPowerIntegral t = halfPowerClosed t := by
  rw [halfPowerIntegral, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ ↦ hasDerivAt_halfPowerClosed s)
    (continuous_sq_div_one_add_pow_four.intervalIntegrable 0 t), halfPowerClosed_zero, sub_zero]

/-- **The closed form of `f_s`**, Chen–Hou II, Supp. Section 5.1.2. -/
theorem halfPowerIntegral_eq (t : ℝ) :
    halfPowerIntegral t =
      (Real.log ((t ^ 2 - √2 * t + 1) / (t ^ 2 + √2 * t + 1)) + 2 * Real.arctan (√2 * t + 1) +
        2 * Real.arctan (√2 * t - 1)) / (4 * √2) := by
  rw [halfPowerIntegral_eq_closed, halfPowerClosed,
    Real.log_div (quadratic_minus_pos t).ne' (quadratic_plus_pos t).ne']

/-- **`f_s(1) = (π - 2 log (1 + √2)) / (4√2)`**. -/
theorem halfPowerIntegral_one :
    halfPowerIntegral 1 = (Real.pi - 2 * Real.log (1 + √2)) / (4 * √2) := by
  have hr := sqrt_two_sq
  have hr1 : (1 : ℝ) < √2 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hpos : 0 < √2 - 1 := by linarith
  have hinv : √2 - 1 = (√2 + 1)⁻¹ := eq_inv_of_mul_eq_one_left (by nlinarith [hr])
  have hatan : Real.arctan (√2 + 1) + Real.arctan (√2 - 1) = Real.pi / 2 := by
    rw [hinv, Real.arctan_inv_of_pos (by positivity)]; ring
  have hq : ((1 : ℝ) ^ 2 - √2 * 1 + 1) / (1 ^ 2 + √2 * 1 + 1) = ((1 + √2) ^ 2)⁻¹ := by
    rw [div_eq_iff (by positivity), eq_comm, inv_mul_eq_div, div_eq_iff (by positivity)]
    nlinarith [hr]
  rw [halfPowerIntegral_eq, hq, Real.log_inv, Real.log_pow, mul_one]
  congr 1
  push_cast
  linarith [hatan]

/-- `(t² - √2 t + 1) / (t² + √2 t + 1) → 1` as `t → ∞`. -/
private theorem tendsto_quadratic_ratio :
    Tendsto (fun t : ℝ ↦ (t ^ 2 - √2 * t + 1) / (t ^ 2 + √2 * t + 1)) atTop (𝓝 1) := by
  have hr0 : (0 : ℝ) < √2 := by positivity
  have hsmall : Tendsto (fun t : ℝ ↦ 2 * √2 * t / (t ^ 2 + √2 * t + 1)) atTop (𝓝 0) := by
    have hle : ∀ᶠ t : ℝ in atTop, 2 * √2 * t / (t ^ 2 + √2 * t + 1) ≤ 2 * √2 * t⁻¹ := by
      filter_upwards [eventually_gt_atTop 0] with t ht
      rw [div_le_iff₀ (quadratic_plus_pos t)]
      field_simp
      nlinarith [sq_nonneg t, mul_pos hr0 ht]
    have hge : ∀ᶠ t : ℝ in atTop, 0 ≤ 2 * √2 * t / (t ^ 2 + √2 * t + 1) := by
      filter_upwards [eventually_gt_atTop 0] with t ht
      exact div_nonneg (by positivity) (quadratic_plus_pos t).le
    have hlim : Tendsto (fun t : ℝ ↦ 2 * √2 * t⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.const_mul (2 * √2)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim hge hle
  have heq : ∀ t : ℝ, (t ^ 2 - √2 * t + 1) / (t ^ 2 + √2 * t + 1) =
      1 - 2 * √2 * t / (t ^ 2 + √2 * t + 1) := fun t ↦ by
    rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq (quadratic_plus_pos t).ne']
    ring
  simp_rw [heq]
  simpa using tendsto_const_nhds.sub hsmall

/-- `arctan (√2 t + s) → π / 2` as `t → ∞`. -/
private theorem tendsto_arctan_affine (s : ℝ) :
    Tendsto (fun t : ℝ ↦ Real.arctan (√2 * t + s)) atTop (𝓝 (Real.pi / 2)) := by
  have h : Tendsto (fun t : ℝ ↦ √2 * t + s) atTop atTop :=
    tendsto_atTop_add_const_right _ s (tendsto_id.const_mul_atTop (by positivity))
  exact (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h

/-- **`f_s(∞) = π / (2√2)`**. -/
theorem tendsto_halfPowerIntegral_atTop :
    Tendsto halfPowerIntegral atTop (𝓝 (Real.pi / (2 * √2))) := by
  have hlog := ((Real.continuousAt_log one_ne_zero).tendsto.comp tendsto_quadratic_ratio)
  rw [Real.log_one] at hlog
  have h := ((hlog.add ((tendsto_arctan_affine 1).const_mul 2)).add
    ((tendsto_arctan_affine (-1)).const_mul 2)).div_const (4 * √2)
  have hv : (0 + 2 * (Real.pi / 2) + 2 * (Real.pi / 2)) / (4 * √2) = Real.pi / (2 * √2) := by
    field_simp
    ring
  rw [hv] at h
  refine h.congr fun t ↦ ?_
  rw [halfPowerIntegral_eq]
  simp only [Function.comp_apply, sub_eq_add_neg]

/-- **`∫₀^∞ s² / (1 + s⁴) ds = π / (2√2)`**, the improper form of `f_s(∞)`. -/
theorem integral_Ioi_sq_div_one_add_pow_four :
    ∫ s in Ioi (0 : ℝ), s ^ 2 / (1 + s ^ 4) = Real.pi / (2 * √2) := by
  have hcont := continuous_halfPowerIntegral.continuousWithinAt (s := Ici 0) (x := 0)
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt halfPowerIntegral (x ^ 2 / (1 + x ^ 4)) x :=
    fun x _ ↦ hasDerivAt_halfPowerIntegral x
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hd
    (integrableOn_Ioi_deriv_of_nonneg hcont hd (fun x _ ↦ by positivity)
      tendsto_halfPowerIntegral_atTop) tendsto_halfPowerIntegral_atTop,
    halfPowerIntegral_zero, sub_zero]

/-! ### Integrals with a half power -/

/-- The primitive `2 √p f_s(√(s/p))` of `p √s / (p² + s²)` for `s > 0`. -/
private theorem hasDerivAt_halfPowerPrimitive {p s : ℝ} (hp : 0 < p) (hs : 0 < s) :
    HasDerivAt (fun s ↦ 2 * √p * halfPowerIntegral (√(s / p))) (p / (p ^ 2 + s ^ 2) * √s) s := by
  have hsp : 0 < s / p := div_pos hs hp
  have h1 : HasDerivAt (fun s ↦ √(s / p)) (1 / (2 * √(s / p)) * (1 / p)) s := by
    have := (Real.hasDerivAt_sqrt hsp.ne').comp s ((hasDerivAt_id' s).div_const p)
    simpa [Function.comp_def, one_div] using this
  have h := ((hasDerivAt_halfPowerIntegral (√(s / p))).comp s h1).const_mul (2 * √p)
  refine h.congr_deriv ?_
  obtain ⟨u, hu, rfl⟩ : ∃ u, 0 < u ∧ s = u ^ 2 :=
    ⟨√s, Real.sqrt_pos.mpr hs, (Real.sq_sqrt hs.le).symm⟩
  obtain ⟨w, hw, rfl⟩ : ∃ w, 0 < w ∧ p = w ^ 2 :=
    ⟨√p, Real.sqrt_pos.mpr hp, (Real.sq_sqrt hp.le).symm⟩
  rw [show u ^ 2 / w ^ 2 = (u / w) ^ 2 by ring, Real.sqrt_sq (div_pos hu hw).le,
    Real.sqrt_sq hw.le, Real.sqrt_sq hu.le]
  field_simp

/-- **The half-power substitution**, Chen–Hou II, Supp. (5.6): for `p > 0` and
`0 ≤ a ≤ b`, `∫_a^b p / (p² + s²) √s ds = 2 √p (f_s(√(b/p)) - f_s(√(a/p)))`. -/
theorem integral_div_sq_add_sq_mul_sqrt {p a b : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ s in a..b, p / (p ^ 2 + s ^ 2) * √s =
      2 * √p * (halfPowerIntegral (√(b / p)) - halfPowerIntegral (√(a / p))) := by
  rw [mul_sub]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab ?_ (fun s hs ↦
    hasDerivAt_halfPowerPrimitive hp (ha.trans_lt hs.1)) ?_
  · exact (continuous_const.mul (continuous_halfPowerIntegral.comp
      ((continuous_id.div_const p).sqrt))).continuousOn
  · refine (ContinuousOn.mul ?_ Real.continuous_sqrt.continuousOn).intervalIntegrable
    exact continuousOn_const.div (by fun_prop) fun s _ ↦ by positivity

/-! ### `|K₂|` on rectangles of the first quadrant -/

/-- `Φ(u, v) = v / (2 (u² + v²))`, the primitive of `K₂(u, ·)`. -/
private def edgeValue (u v : ℝ) : ℝ := v / (2 * (u ^ 2 + v ^ 2))

/-- `K₂(u, v) ≥ 0` below the diagonal, for `0 ≤ v ≤ u`. -/
theorem hessianKernel_zero_zero_toLp_nonneg {u v : ℝ} (hv : 0 ≤ v) (hvu : v ≤ u) :
    0 ≤ hessianKernel 0 0 !₂[u, v] := by
  rw [hessianKernel_zero_zero_toLp]
  exact div_nonneg (by nlinarith) (by positivity)

/-- `K₂(u, v) ≤ 0` above the diagonal, for `0 ≤ u ≤ v`. -/
theorem hessianKernel_zero_zero_toLp_nonpos {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    hessianKernel 0 0 !₂[u, v] ≤ 0 := by
  rw [hessianKernel_zero_zero_toLp]
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)

/-- `v ↦ K₂(u, v)` is continuous on every set `s` on which `u² + v² ≠ 0`. -/
private theorem continuous_kernelTwo_right {u : ℝ} {s : Set ℝ} (h : ∀ v ∈ s, u ^ 2 + v ^ 2 ≠ 0) :
    ContinuousOn (fun v ↦ hessianKernel 0 0 !₂[u, v]) s := by
  simp only [hessianKernel_zero_zero_toLp]
  exact (continuousOn_const.sub (continuous_pow 2).continuousOn).div (by fun_prop)
    fun v hv ↦ mul_ne_zero two_ne_zero (pow_ne_zero 2 (h v hv))

/-- The inner integral of `|K₂|` across the diagonal: for `u ≥ 0` and `0 ≤ c ≤ d`, with
`z = min d (max c u)`, `∫_c^d |K₂(u, v)| dv = 2Φ(u, z) - Φ(u, c) - Φ(u, d)`. -/
private theorem integral_abs_kernelTwo_right {u c d : ℝ} (hu : 0 ≤ u) (hc : 0 ≤ c) (hcd : c ≤ d)
    (h : ∀ v ∈ Icc c d, u ^ 2 + v ^ 2 ≠ 0) :
    ∫ v in c..d, |hessianKernel 0 0 !₂[u, v]| =
      2 * edgeValue u (min d (max c u)) - edgeValue u c - edgeValue u d := by
  have hsub : ∀ {x y : ℝ}, c ≤ x → x ≤ y → y ≤ d → ∀ v ∈ uIcc x y, u ^ 2 + v ^ 2 ≠ 0 := by
    intro x y hx hxy hy v hv
    rw [uIcc_of_le hxy] at hv; exact h v ⟨hx.trans hv.1, hv.2.trans hy⟩
  rcases le_total u c with huc | hcu
  · rw [max_eq_left huc, min_eq_right hcd]
    rw [intervalIntegral.integral_congr (g := fun v ↦ -hessianKernel 0 0 !₂[u, v]) fun v hv ↦ by
      rw [uIcc_of_le hcd] at hv
      exact abs_of_nonpos (hessianKernel_zero_zero_toLp_nonpos hu (huc.trans hv.1)),
      intervalIntegral.integral_neg,
      integral_hessianKernel_zero_zero_right (hsub le_rfl hcd le_rfl)]
    simp only [edgeValue]
    ring
  rcases le_total u d with hud | hdu
  · rw [max_eq_right hcu, min_eq_right hud]
    have hint : ∀ {x y : ℝ}, c ≤ x → x ≤ y → y ≤ d →
        IntervalIntegrable (fun v ↦ |hessianKernel 0 0 !₂[u, v]|) volume x y := fun hx hxy hy ↦
      ((continuous_kernelTwo_right (hsub hx hxy hy)).abs).intervalIntegrable
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint le_rfl hcu hud)
      (hint hcu hud le_rfl)]
    rw [intervalIntegral.integral_congr (g := fun v ↦ hessianKernel 0 0 !₂[u, v]) fun v hv ↦ by
      rw [uIcc_of_le hcu] at hv
      exact abs_of_nonneg (hessianKernel_zero_zero_toLp_nonneg (hc.trans hv.1) hv.2),
      intervalIntegral.integral_congr (a := u) (b := d)
        (g := fun v ↦ -hessianKernel 0 0 !₂[u, v]) fun v hv ↦ by
      rw [uIcc_of_le hud] at hv
      exact abs_of_nonpos (hessianKernel_zero_zero_toLp_nonpos hu hv.1),
      intervalIntegral.integral_neg, integral_hessianKernel_zero_zero_right (hsub le_rfl hcu hud),
      integral_hessianKernel_zero_zero_right (hsub hcu hud le_rfl)]
    simp only [edgeValue]
    ring
  · rw [max_eq_right hcu, min_eq_left hdu]
    rw [intervalIntegral.integral_congr (g := fun v ↦ hessianKernel 0 0 !₂[u, v]) fun v hv ↦ by
      rw [uIcc_of_le hcd] at hv
      exact abs_of_nonneg (hessianKernel_zero_zero_toLp_nonneg (hc.trans hv.1) (hv.2.trans hdu)),
      integral_hessianKernel_zero_zero_right (hsub le_rfl hcd le_rfl)]
    simp only [edgeValue]
    ring

/-- `u ↦ Φ(u, f u)` is continuous on `s` when `f` is continuous on `s` and `u² + f(u)² ≠ 0` there.
-/
private theorem continuousOn_edgeValue {s : Set ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f s)
    (h : ∀ u ∈ s, u ^ 2 + f u ^ 2 ≠ 0) : ContinuousOn (fun u ↦ edgeValue u (f u)) s :=
  hf.div ((continuousOn_const.mul ((continuous_pow 2).continuousOn.add (hf.pow 2))))
    fun u hu ↦ mul_ne_zero two_ne_zero (h u hu)

/-- `∫_a^b Φ(u, c) du = (arctan (b/c) - arctan (a/c)) / 2`. -/
private theorem integral_edgeValue {a b c : ℝ} (h : ∀ u ∈ uIcc a b, u ^ 2 + c ^ 2 ≠ 0) :
    ∫ u in a..b, edgeValue u c = (Real.arctan (b / c) - Real.arctan (a / c)) / 2 := by
  unfold edgeValue
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hasDerivAt_arctan_div_left u c)
    ((continuousOn_edgeValue continuousOn_const h).intervalIntegrable)]
  ring

/-- **`|K₂|` over a rectangle of the first quadrant.** For `0 ≤ a ≤ b`, `0 ≤ c ≤ d` and
`(a, c) ≠ 0`, with `p = max a (min c b)` and `q = max a (min d b)` the clamps of `c` and `d` to
`[a, b]`, the integral of `|K₂|` over `[a, b] × [c, d]` is
`(1/2) log (q/p) + arctan (p/c) - (arctan (a/c) + arctan (b/c))/2 + (arctan (a/d) + arctan (b/d))/2
- arctan (q/d)`, with `arctan (u/0) = 0`. The sign of `K₂` changes on the diagonal; the inner
integral is split there. -/
theorem integral_integral_abs_hessianKernel_zero_zero {a b c d : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hc : 0 ≤ c) (hcd : c ≤ d) (h0 : 0 < a ∨ 0 < c) :
    ∫ x in a..b, ∫ y in c..d, |hessianKernel 0 0 !₂[x, y]| =
      Real.log (max a (min d b) / max a (min c b)) / 2 + Real.arctan (max a (min c b) / c) -
        (Real.arctan (a / c) + Real.arctan (b / c)) / 2 +
        (Real.arctan (a / d) + Real.arctan (b / d)) / 2 - Real.arctan (max a (min d b) / d) := by
  set p := max a (min c b) with hp
  set q := max a (min d b) with hq
  have hne : ∀ u v : ℝ, a ≤ u → c ≤ v → u ^ 2 + v ^ 2 ≠ 0 := fun u v hu hv ↦ by
    rcases h0 with h | h
    · have : 0 < u := h.trans_le hu; positivity
    · have : 0 < v := h.trans_le hv; positivity
  have hneI (v : ℝ) (hv : c ≤ v) : ∀ u ∈ uIcc a b, u ^ 2 + v ^ 2 ≠ 0 := fun u hu ↦
    hne u v (by rw [uIcc_of_le hab] at hu; exact hu.1) hv
  have hap : a ≤ p := le_max_left _ _
  have hpq : p ≤ q := max_le_max le_rfl (min_le_min_right b hcd)
  have hqb : q ≤ b := max_le hab (min_le_right _ _)
  set Z : ℝ → ℝ := fun u ↦ min d (max c u) with hZ
  have hZc : ∀ u, c ≤ Z u := fun u ↦ le_min hcd (le_max_left c u)
  rw [intervalIntegral.integral_congr (g := fun u ↦ 2 * edgeValue u (Z u) - edgeValue u c -
      edgeValue u d) fun u hu ↦ by
    rw [uIcc_of_le hab] at hu
    exact integral_abs_kernelTwo_right (ha.trans hu.1) hc hcd fun v hv ↦ hne u v hu.1 hv.1]
  have cZ : ContinuousOn (fun u ↦ edgeValue u (Z u)) (uIcc a b) :=
    continuousOn_edgeValue (by fun_prop) fun u hu ↦ by
      rw [uIcc_of_le hab] at hu; exact hne u (Z u) hu.1 (hZc u)
  have cc : ContinuousOn (fun u ↦ edgeValue u c) (uIcc a b) :=
    continuousOn_edgeValue continuousOn_const (hneI c le_rfl)
  have cd : ContinuousOn (fun u ↦ edgeValue u d) (uIcc a b) :=
    continuousOn_edgeValue continuousOn_const (hneI d hcd)
  have c2Z : ContinuousOn (fun u ↦ 2 * edgeValue u (Z u)) (uIcc a b) := continuousOn_const.mul cZ
  have i2Zc : IntervalIntegrable (fun u ↦ 2 * edgeValue u (Z u) - edgeValue u c) volume a b :=
    (c2Z.sub cc).intervalIntegrable
  rw [intervalIntegral.integral_sub i2Zc cd.intervalIntegrable,
    intervalIntegral.integral_sub c2Z.intervalIntegrable cc.intervalIntegrable,
    integral_edgeValue (hneI c le_rfl), integral_edgeValue (hneI d hcd)]
  have hsub : ∀ {x y : ℝ}, a ≤ x → x ≤ y → y ≤ b →
      IntervalIntegrable (fun u ↦ 2 * edgeValue u (Z u)) volume x y := by
    intro x y hx hxy hy
    have hsub : uIcc x y ⊆ uIcc a b := by
      rw [uIcc_of_le hab, uIcc_of_le hxy]; exact Icc_subset_Icc hx hy
    exact (c2Z.mono hsub).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals (hsub le_rfl hap (hpq.trans hqb))
      (hsub hap (hpq.trans hqb) le_rfl),
    ← intervalIntegral.integral_add_adjacent_intervals (hsub hap hpq hqb)
      (hsub (hap.trans hpq) hqb le_rfl)]
  -- the piece `[a, p]`, below `c`
  have e1 : ∫ u in a..p, 2 * edgeValue u (Z u) = Real.arctan (p / c) - Real.arctan (a / c) := by
    rw [intervalIntegral.integral_congr_ae (g := fun u ↦ 2 * edgeValue u c)
      (Eventually.of_forall fun u hu ↦ ?_)]
    · rw [intervalIntegral.integral_const_mul, integral_edgeValue fun u hu ↦ by
        rw [uIcc_of_le hap] at hu; exact hne u c hu.1 le_rfl]
      ring
    · rw [uIoc_of_le hap] at hu
      have hpm : p = min c b :=
        max_eq_right ((lt_max_iff.1 (hu.1.trans_le hu.2)).resolve_left (lt_irrefl a)).le
      have huc : u ≤ c := hu.2.trans (hpm ▸ min_le_left c b)
      simp only [hZ, max_eq_left huc, min_eq_right hcd]
  -- the piece `[q, b]`, above `d`
  have e3 : ∫ u in q..b, 2 * edgeValue u (Z u) = Real.arctan (b / d) - Real.arctan (q / d) := by
    rw [intervalIntegral.integral_congr_ae (g := fun u ↦ 2 * edgeValue u d)
      (Eventually.of_forall fun u hu ↦ ?_)]
    · rw [intervalIntegral.integral_const_mul, integral_edgeValue fun u hu ↦ by
        rw [uIcc_of_le hqb] at hu; exact hne u d ((hap.trans hpq).trans hu.1) hcd]
      ring
    · rw [uIoc_of_le hqb] at hu
      have hdu : d < u :=
        (min_lt_iff.1 ((le_max_right a _).trans_lt hu.1)).resolve_right (not_lt.2 hu.2)
      simp only [hZ, max_eq_right (hcd.trans hdu.le), min_eq_left hdu.le]
  -- the piece `[p, q]`, across the diagonal
  have e2 : ∫ u in p..q, 2 * edgeValue u (Z u) = Real.log (q / p) / 2 := by
    rcases eq_or_lt_of_le hpq with hpq' | hpq'
    · rw [hpq', intervalIntegral.integral_same]
      rcases eq_or_ne q 0 with h' | h'
      · simp [h']
      · simp [div_self h']
    have hp0 : 0 < p := by
      rcases h0 with h | h
      · exact h.trans_le hap
      · exact lt_max_iff.2 (Or.inr (lt_min h (by linarith)))
    rw [intervalIntegral.integral_congr_ae (g := fun u ↦ 1 / (2 * u))
      (Eventually.of_forall fun u hu ↦ ?_)]
    · have hlog : ∀ u ∈ uIcc p q, HasDerivAt (fun u ↦ Real.log u / 2) (1 / (2 * u)) u := by
        intro u hu
        rw [uIcc_of_le hpq] at hu
        have hu0 : u ≠ 0 := (hp0.trans_le hu.1).ne'
        convert (Real.hasDerivAt_log hu0).div_const 2 using 1
        field_simp
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hlog
        (ContinuousOn.intervalIntegrable fun u hu ↦ by
          rw [uIcc_of_le hpq] at hu
          exact (continuousAt_const.div (continuousAt_const.mul continuousAt_id)
            (mul_ne_zero two_ne_zero (hp0.trans_le hu.1).ne')).continuousWithinAt),
        Real.log_div (hp0.trans_le hpq).ne' hp0.ne']
      ring
    · rw [uIoc_of_le hpq] at hu
      have hcu : c ≤ u := by
        by_contra! h'
        rcases min_lt_iff.1 ((le_max_right a _).trans_lt hu.1) with h'' | h'' <;> linarith [hu.2]
      have hqm : q = min d b := max_eq_right
        ((lt_max_iff.1 ((hap.trans_lt hu.1).trans_le hu.2)).resolve_left (lt_irrefl a)).le
      have hud : u ≤ d := hu.2.trans (hqm ▸ min_le_left d b)
      have hu0 : u ≠ 0 := (hp0.trans hu.1).ne'
      simp only [hZ, max_eq_right hcu, min_eq_right hud, edgeValue]
      field_simp
      ring
  rw [e1, e2, e3]
  ring

/-- **`|K₂|` over a rectangle of the first quadrant**, as an integral over the plane. -/
theorem integral_rectangle_abs_hessianKernel_zero_zero {a b c d : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hc : 0 ≤ c) (hcd : c ≤ d) (h0 : 0 < a ∨ 0 < c) :
    ∫ y in coordinateRectangle a b c d, |hessianKernel 0 0 y| =
      Real.log (max a (min d b) / max a (min c b)) / 2 + Real.arctan (max a (min c b) / c) -
        (Real.arctan (a / c) + Real.arctan (b / c)) / 2 +
        (Real.arctan (a / d) + Real.arctan (b / d)) / 2 - Real.arctan (max a (min d b) / d) := by
  have h0' : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0 := by tauto
  rw [setIntegral_coordinateRectangle hab hcd (continuousOn_hessianKernel 0 0 h0').abs]
  exact integral_integral_abs_hessianKernel_zero_zero ha hab hc hcd h0

/-- **`F_diag`**, Chen–Hou II, Supp. (5.10): for `0 < a ≤ b`,
`∫_{[a, b]²} |K₂| = (1/2) log (b/a) - (π/4 - arctan (a/b))`. -/
theorem integral_square_abs_hessianKernel_zero_zero {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ y in coordinateRectangle a b a b, |hessianKernel 0 0 y| =
      Real.log (b / a) / 2 - (Real.pi / 4 - Real.arctan (a / b)) := by
  have hb : 0 < b := ha.trans_le hab
  rw [integral_rectangle_abs_hessianKernel_zero_zero ha.le hab ha.le hab (Or.inl ha),
    min_eq_left hab, max_self, min_self, max_eq_right hab, div_self ha.ne', div_self hb.ne',
    Real.arctan_one, show b / a = (a / b)⁻¹ by rw [inv_div],
    Real.arctan_inv_of_pos (div_pos ha hb)]
  ring

/-- The square annulus `[-b, b]² \ [-a, a]²`. -/
private def squareAnnulus (a b : ℝ) : Set (ℝ^2) :=
  coordinateRectangle (-b) b (-b) b \ coordinateRectangle (-a) a (-a) a

/-- Every point of the square annulus `[-b, b]² \ [-a, a]²` has norm at least `a`. -/
private theorem le_norm_of_mem_squareAnnulus {a b : ℝ} {y : ℝ^2} (hy : y ∈ squareAnnulus a b) :
    a ≤ ‖y‖ := by
  by_contra hlt
  push Not at hlt
  refine hy.2 ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
    linarith [abs_le.mp (EuclideanSpace.abs_apply_le_norm y 0), abs_le.mp
        (EuclideanSpace.abs_apply_le_norm y 1)]

/-- The square annulus is invariant under each coordinate reflection `Rₖ`. -/
private theorem mem_squareAnnulus_reflect {a b : ℝ} (k : Fin 2) (y : ℝ^2) :
    PDE.Common.coordinateReflection k y ∈ squareAnnulus a b ↔ y ∈ squareAnnulus a b := by
  have key : ∀ (r : ℝ) (i : Fin 2), (PDE.Common.coordinateReflection k y i ∈ Icc (-r) r ↔
      y i ∈ Icc (-r) r) := by
    intro r i
    by_cases hik : i = k
    · subst hik
      rw [PDE.Common.coordinateReflection_apply_same]
      constructor <;> intro h <;> exact ⟨by linarith [h.2], by linarith [h.1]⟩
    · rw [PDE.Common.coordinateReflection_apply_of_ne k i hik]
  simp only [squareAnnulus, Set.mem_sdiff, mem_coordinateRectangle, key]

/-- The integral of an even kernel over the square annulus is four times the integral over the
two rectangles of the first quadrant. -/
private theorem integral_squareAnnulus {f : ℝ^2 → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hf : Measurable f) (hbound : ∀ y ∈ squareAnnulus a b, |f y| ≤ 1 / (2 * a ^ 2))
    (h₀ : ∀ y, f (PDE.Common.coordinateReflection 0 y) = f y)
    (h₁ : ∀ y, f (PDE.Common.coordinateReflection 1 y) = f y) :
    ∫ y in squareAnnulus a b, f y =
      4 * ((∫ p in (0 : ℝ)..b, ∫ q in a..b, f !₂[p, q]) +
        ∫ p in a..b, ∫ q in (0 : ℝ)..a, f !₂[p, q]) := by
  have hS : MeasurableSet (squareAnnulus a b) :=
    (measurableSet_coordinateRectangle _ _ _ _).diff (measurableSet_coordinateRectangle _ _ _ _)
  have hSb : squareAnnulus a b ⊆ Metric.closedBall 0 (2 * b) := by
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    obtain ⟨⟨h0, h1⟩, -⟩ := hy
    have : ‖y‖ ^ 2 ≤ (2 * b) ^ 2 := by
      rw [EuclideanSpace.norm_sq_fin_two]; nlinarith [h0.1, h0.2, h1.1, h1.2]
    nlinarith [norm_nonneg y]
  have hint : IntegrableOn f (squareAnnulus a b) := by
    refine Measure.integrableOn_of_bounded (M := 1 / (2 * a ^ 2))
      ((measure_mono hSb).trans_lt measure_closedBall_lt_top).ne hf.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hS] with y hy
    rw [Real.norm_eq_abs]; exact hbound y hy
  have hrefl (i : Fin 2) (hi : ∀ y, f (PDE.Common.coordinateReflection i y) = f y) (y : ℝ^2) :
      (squareAnnulus a b).indicator f (PDE.Common.coordinateReflection i y) =
        (squareAnnulus a b).indicator f y := by
    by_cases hy : y ∈ squareAnnulus a b
    · rw [indicator_of_mem ((mem_squareAnnulus_reflect i y).mpr hy), indicator_of_mem hy, hi]
    · rw [indicator_of_notMem (mt (mem_squareAnnulus_reflect i y).mp hy), indicator_of_notMem hy]
  rw [← integral_indicator hS, GreenFunction.integral_eq_four_mul_setIntegral_quadrant
      ((integrable_indicator_iff hS).mpr hint) (hrefl 0 h₀) (hrefl 1 h₁), setIntegral_indicator hS]
  set A := {y : ℝ^2 | y 0 ∈ Ioc 0 b ∧ y 1 ∈ Ioc a b}
  set B := {y : ℝ^2 | y 0 ∈ Ioc a b ∧ y 1 ∈ Ioc 0 a}
  have hAB : GreenFunction.quadrant ∩ squareAnnulus a b = A ∪ B := by
    ext y
    simp only [GreenFunction.quadrant, squareAnnulus, mem_inter_iff, Set.mem_sdiff,
      mem_coordinateRectangle, mem_union, mem_Icc, mem_Ioc, A, B, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨h0, h1⟩, ⟨⟨-, hb0⟩, -, hb1⟩, hn⟩
      by_cases h : a < y 1
      · exact Or.inl ⟨⟨h0, hb0⟩, h, hb1⟩
      · push Not at h
        refine Or.inr ⟨⟨?_, hb0⟩, h1, h⟩
        by_contra h'
        push Not at h'
        exact hn ⟨⟨by linarith, h'⟩, by linarith, h⟩
    · rintro (⟨⟨h0, hb0⟩, h1, hb1⟩ | ⟨⟨h0, hb0⟩, h1, hb1⟩)
      · refine ⟨⟨h0, by linarith⟩, ⟨⟨by linarith, hb0⟩, by linarith, hb1⟩, ?_⟩
        rintro ⟨-, -, h⟩; linarith
      · refine ⟨⟨by linarith, h1⟩, ⟨⟨by linarith, hb0⟩, by linarith, by linarith⟩, ?_⟩
        rintro ⟨⟨-, h⟩, -⟩; linarith
  have hsub : A ∪ B ⊆ squareAnnulus a b := hAB ▸ inter_subset_right
  have hAm : MeasurableSet A := (measurableSet_Ioc.preimage (by fun_prop)).inter
    (measurableSet_Ioc.preimage (by fun_prop))
  have hBm : MeasurableSet B := (measurableSet_Ioc.preimage (by fun_prop)).inter
    (measurableSet_Ioc.preimage (by fun_prop))
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro y ⟨-, h1, -⟩ ⟨-, -, h2⟩
    linarith
  rw [hAB, setIntegral_union hdisj hBm (hint.mono_set (subset_union_left.trans hsub))
      (hint.mono_set (subset_union_right.trans hsub)),
    setIntegral_coordinateProduct (hint.mono_set (subset_union_left.trans hsub)),
    setIntegral_coordinateProduct (hint.mono_set (subset_union_right.trans hsub)),
    intervalIntegral.integral_of_le (ha.le.trans hab), intervalIntegral.integral_of_le hab]
  congr 2
  · refine setIntegral_congr_fun measurableSet_Ioc fun p _ ↦ ?_
    rw [intervalIntegral.integral_of_le hab]
  · refine setIntegral_congr_fun measurableSet_Ioc fun p _ ↦ ?_
    rw [intervalIntegral.integral_of_le ha.le]

/-- On the square annulus `[-b, b]² \ [-a, a]²` with `a > 0`, `|kᵢⱼ| ≤ 1 / (2 a²)`. -/
private theorem abs_hessianKernel_le_of_mem_squareAnnulus (i j : Fin 2) {a b : ℝ} (ha : 0 < a)
    {y : ℝ^2} (hy : y ∈ squareAnnulus a b) : |(|hessianKernel i j y|)| ≤ 1 / (2 * a ^ 2) := by
  rw [abs_abs]
  refine (abs_hessianKernel_le i j y).trans ?_
  have := le_norm_of_mem_squareAnnulus hy
  gcongr

/-- **`∫_{[-b, b]² \ [-a, a]²} |K₁| = 2 log (b/a)`**, Chen–Hou II, Supp. (5.18). -/
theorem integral_squareAnnulus_abs_hessianKernel_zero_one {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ y in coordinateRectangle (-b) b (-b) b \ coordinateRectangle (-a) a (-a) a,
      |hessianKernel 0 1 y| = 2 * Real.log (b / a) := by
  have hb : 0 < b := ha.trans_le hab
  have h := integral_squareAnnulus (f := fun y ↦ |hessianKernel 0 1 y|) ha hab
    (continuous_abs.measurable.comp (measurable_hessianKernel 0 1))
    (fun y hy ↦ abs_hessianKernel_le_of_mem_squareAnnulus 0 1 ha hy)
    (fun y ↦ by simp only [hessianKernel_zero_one_coordinateReflection, abs_neg])
    (fun y ↦ by simp only [hessianKernel_zero_one_coordinateReflection, abs_neg])
  rw [show coordinateRectangle (-b) b (-b) b \ coordinateRectangle (-a) a (-a) a =
    squareAnnulus a b from rfl, h]
  have hpos : ∀ {s t c d : ℝ}, 0 ≤ s → s ≤ t → 0 ≤ c → c ≤ d →
      ∫ p in s..t, ∫ q in c..d, |hessianKernel 0 1 !₂[p, q]| =
        ∫ p in s..t, ∫ q in c..d, hessianKernel 0 1 !₂[p, q] := by
    intro s t c d hs hst hc hcd
    refine intervalIntegral.integral_congr fun p hp ↦ intervalIntegral.integral_congr fun q hq ↦ ?_
    rw [uIcc_of_le hst] at hp; rw [uIcc_of_le hcd] at hq
    rw [hessianKernel_zero_one_toLp]
    exact abs_of_nonneg (div_nonneg (mul_nonneg (hs.trans hp.1) (hc.trans hq.1)) (by positivity))
  rw [hpos le_rfl hb.le ha.le hab, hpos ha.le hab le_rfl ha.le,
    integral_integral_hessianKernel_zero_one hb.le hab (Or.inr (Or.inr (Or.inl ha))),
    integral_integral_hessianKernel_zero_one hab ha.le (Or.inl ha)]
  simp only [cornerSum]
  have l2 : ∀ x : ℝ, 0 < x → Real.log (x ^ 2 + x ^ 2) = Real.log 2 + 2 * Real.log x := by
    intro x hx
    rw [show x ^ 2 + x ^ 2 = 2 * x ^ 2 by ring, Real.log_mul (by norm_num) (by positivity),
      Real.log_pow]
    push_cast; ring
  have l1 : ∀ x : ℝ, Real.log ((0 : ℝ) ^ 2 + x ^ 2) = 2 * Real.log x := by
    intro x; rw [zero_pow two_ne_zero, zero_add, Real.log_pow]; push_cast; ring
  have l1' : ∀ x : ℝ, Real.log (x ^ 2 + (0 : ℝ) ^ 2) = 2 * Real.log x := by
    intro x; rw [zero_pow two_ne_zero, add_zero, Real.log_pow]; push_cast; ring
  rw [l2 b hb, l2 a ha, l1 b, l1 a, l1' b, l1' a, add_comm (b ^ 2) (a ^ 2),
    Real.log_div hb.ne' ha.ne']
  ring

/-- **`∫_{[-b, b]² \ [-a, a]²} |K₂| = 2 log (b/a)`**, Chen–Hou II, Supp. (5.18). -/
theorem integral_squareAnnulus_abs_hessianKernel_zero_zero {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ y in coordinateRectangle (-b) b (-b) b \ coordinateRectangle (-a) a (-a) a,
      |hessianKernel 0 0 y| = 2 * Real.log (b / a) := by
  have hb : 0 < b := ha.trans_le hab
  have h := integral_squareAnnulus (f := fun y ↦ |hessianKernel 0 0 y|) ha hab
    (continuous_abs.measurable.comp (measurable_hessianKernel 0 0))
    (fun y hy ↦ abs_hessianKernel_le_of_mem_squareAnnulus 0 0 ha hy)
    (fun y ↦ by simp only [hessianKernel_zero_zero_coordinateReflection])
    (fun y ↦ by simp only [hessianKernel_zero_zero_coordinateReflection])
  rw [show coordinateRectangle (-b) b (-b) b \ coordinateRectangle (-a) a (-a) a =
    squareAnnulus a b from rfl, h,
    integral_integral_abs_hessianKernel_zero_zero le_rfl hb.le ha.le hab (Or.inr ha),
    integral_integral_abs_hessianKernel_zero_zero ha.le hab le_rfl ha.le (Or.inl ha)]
  simp only [min_eq_left hab, max_eq_right ha.le, min_self, max_eq_right hb.le, min_eq_left hb.le,
    max_eq_left ha.le, max_self, div_self ha.ne', div_self hb.ne', zero_div, div_zero,
    Real.arctan_zero, Real.arctan_one, Real.log_one]
  ring

/-! ### `|K₂|` against `y₂^{1/2}` near the corner -/

/-- `|K₂(u, v)| = |K₂(v, u)|`, since swapping the coordinates changes the sign of `K₂`. -/
private theorem abs_kernelTwo_swap (u v : ℝ) :
    |hessianKernel 0 0 !₂[u, v]| = |hessianKernel 0 0 !₂[v, u]| := by
  rw [hessianKernel_zero_zero_toLp, hessianKernel_zero_zero_toLp, ← abs_neg]
  congr 1
  rw [add_comm (v ^ 2)]
  ring

/-- The inner integral `∫₀^a |K₂(y₁, y₂)| dy₁ = 2Φ(y₂, min a y₂) - Φ(y₂, a)` for `y₂ > 0`. -/
private theorem integral_abs_kernelTwo_left {a y : ℝ} (ha : 0 < a) (hy : 0 < y) :
    ∫ x in (0 : ℝ)..a, |hessianKernel 0 0 !₂[x, y]| =
      2 * edgeValue y (min a y) - edgeValue y a := by
  simp_rw [abs_kernelTwo_swap _ y]
  rw [integral_abs_kernelTwo_right hy.le le_rfl ha.le fun v _ ↦ by positivity,
    max_eq_right hy.le]
  simp [edgeValue]

/-- The primitive `√a f_s(√(s/a))` of `a √s / (2 (a² + s²))`. -/
private theorem hasDerivAt_halfPowerPrimitive_half {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    HasDerivAt (fun s ↦ √a * halfPowerIntegral (√(s / a))) (edgeValue s a * √s) s := by
  have h := (hasDerivAt_halfPowerPrimitive ha hs).div_const 2
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun s ↦ ?_)
  · simp only [edgeValue]; field_simp; ring
  · simp only; ring

/-- `s ↦ √a f_s(√(s / a))` is continuous. -/
private theorem continuous_halfPowerPrimitive (a : ℝ) :
    Continuous fun s ↦ √a * halfPowerIntegral (√(s / a)) :=
  continuous_const.mul (continuous_halfPowerIntegral.comp (continuous_id.div_const a).sqrt)

/-- For `0 < y ≤ a`, `(∫₀^a |K₂(x, y)| dx) √y = 1 / (2√y) - Φ(y, a) √y`. -/
private theorem corner_integrand_eq {a y : ℝ} (ha : 0 < a) (hy : 0 < y) (hya : y ≤ a) :
    (∫ x in (0 : ℝ)..a, |hessianKernel 0 0 !₂[x, y]|) * √y =
      1 / (2 * √y) - edgeValue y a * √y := by
  rw [integral_abs_kernelTwo_left ha hy, min_eq_right hya]
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 < t ∧ y = t ^ 2 :=
    ⟨√y, Real.sqrt_pos.mpr hy, (Real.sq_sqrt hy.le).symm⟩
  simp only [edgeValue]
  rw [Real.sqrt_sq ht.le]
  field_simp
  ring

/-- `y ↦ √y - √a f_s(√(y / a))` is continuous on `[0, b]` and has derivative `1 / (2√y) - Φ(y, a)
√y` on `(0, b)`. -/
private theorem corner_primitive {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun y ↦ √y - √a * halfPowerIntegral (√(y / a))) (Icc 0 b) ∧
      ∀ y ∈ Ioo (0 : ℝ) b, HasDerivAt (fun y ↦ √y - √a * halfPowerIntegral (√(y / a)))
        (1 / (2 * √y) - edgeValue y a * √y) y :=
  ⟨(Real.continuous_sqrt.sub (continuous_halfPowerPrimitive a)).continuousOn, fun y hy ↦
    (Real.hasDerivAt_sqrt hy.1.ne' |>.congr_deriv (by ring)).sub
      (hasDerivAt_halfPowerPrimitive_half ha hy.1)⟩

/-- For `0 < a` and `b ≤ a`, `y ↦ 1 / (2√y) - Φ(y, a) √y` is integrable on `(0, b]`, despite the
singularity `y^{-1/2}` at `0`. -/
private theorem integrableOn_corner {a b : ℝ} (ha : 0 < a) (hba : b ≤ a) :
    IntegrableOn (fun y ↦ 1 / (2 * √y) - edgeValue y a * √y) (Ioc 0 b) :=
  intervalIntegral.integrableOn_deriv_of_nonneg (corner_primitive ha).1 (corner_primitive ha).2
    fun y hy ↦ by
      rw [← corner_integrand_eq ha hy.1 (hy.2.le.trans hba)]
      exact mul_nonneg (intervalIntegral.integral_nonneg ha.le fun x _ ↦ abs_nonneg _)
        (Real.sqrt_nonneg y)

/-- For `0 < b ≤ a`, every `y ∈ (0, b]` has `(∫₀^a |K₂(x, y)| dx) √y = 1 / (2√y) - Φ(y, a) √y`. -/
private theorem corner_ae {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    ∀ᵐ y ∂volume, y ∈ Ι (0 : ℝ) b →
      (∫ x in (0 : ℝ)..a, |hessianKernel 0 0 !₂[x, y]|) * √y =
        1 / (2 * √y) - edgeValue y a * √y :=
  Eventually.of_forall fun y hy ↦ by
    rw [uIoc_of_le hb.le] at hy
    exact corner_integrand_eq ha hy.1 (hy.2.trans hba)

/-- For `0 < b ≤ a`, `y ↦ (∫₀^a |K₂(x, y)| dx) √y` is integrable on `[0, b]`. -/
private theorem intervalIntegrable_corner {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    IntervalIntegrable (fun y ↦ (∫ x in (0 : ℝ)..a, |hessianKernel 0 0 !₂[x, y]|) * √y)
      volume 0 b := by
  have h := (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mpr (integrableOn_corner ha hba)
  refine h.congr fun y hy ↦ ?_
  rw [uIoc_of_le hb.le] at hy
  exact (corner_integrand_eq ha hy.1 (hy.2.trans hba)).symm

/-- For `0 < b ≤ a`, `∫₀^b (∫₀^a |K₂(x, y)| dx) √y dy = √b - √a f_s(√(b / a))`. -/
private theorem integral_corner_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    ∫ y in (0 : ℝ)..b, (∫ x in (0 : ℝ)..a, |hessianKernel 0 0 !₂[x, y]|) * √y =
      √b - √a * halfPowerIntegral (√(b / a)) := by
  rw [intervalIntegral.integral_congr_ae (corner_ae ha hb hba),
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb.le (corner_primitive ha).1
      (corner_primitive ha).2
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mpr (integrableOn_corner ha hba))]
  simp

/-- **`|K₂|` against `y₂^{1/2}` on a corner rectangle**, Chen–Hou II, Supp. Section 5.1.2: for
`a, b > 0`, `F(a, b) = ∫₀^b (∫₀^a |K₂(y)| dy₁) y₂^{1/2} dy₂` is `√b - √a f_s(√(b/a))` when
`b ≤ a` and `√a (1 - 2 f_s(1) + f_s(√(b/a)))` when `a ≤ b` (the strip formulas after
(5.9), whose absolute values are redundant). -/
theorem integral_integral_abs_hessianKernel_zero_zero_mul_sqrt {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) :
    ∫ y in (0 : ℝ)..b, (∫ x in (0 : ℝ)..a, |hessianKernel 0 0 !₂[x, y]|) * √y =
      if b ≤ a then √b - √a * halfPowerIntegral (√(b / a))
      else √a * (1 - 2 * halfPowerIntegral 1 + halfPowerIntegral (√(b / a))) := by
  split_ifs with hba
  · exact integral_corner_le ha hb hba
  push Not at hba
  have hcont : ContinuousOn (fun y ↦ edgeValue y a * √y) (uIcc a b) :=
    (continuousOn_edgeValue continuousOn_const fun y _ ↦ by positivity).mul
      Real.continuous_sqrt.continuousOn
  have hupper : ∀ y ∈ uIcc a b,
      (∫ x in (0 : ℝ)..a, |hessianKernel 0 0 !₂[x, y]|) * √y = edgeValue y a * √y := by
    intro y hy
    rw [uIcc_of_le hba.le] at hy
    rw [integral_abs_kernelTwo_left ha (ha.trans_le hy.1), min_eq_left hy.1]
    ring
  rw [← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_corner ha ha le_rfl)
      ((hcont.intervalIntegrable).congr ?_),
    integral_corner_le ha ha le_rfl, intervalIntegral.integral_congr hupper]
  · have e : ∀ y : ℝ, edgeValue y a * √y = (a / (a ^ 2 + y ^ 2) * √y) / 2 := fun y ↦ by
      have : 0 < a ^ 2 + y ^ 2 := by positivity
      simp only [edgeValue]; field_simp; ring
    simp_rw [e]
    rw [intervalIntegral.integral_div, integral_div_sq_add_sq_mul_sqrt ha ha.le hba.le,
      div_self ha.ne', Real.sqrt_one]
    ring
  · intro y hy
    rw [uIoc_of_le hba.le] at hy
    exact (hupper y (by rw [uIcc_of_le hba.le]; exact ⟨hy.1.le, hy.2⟩)).symm

/-- **`∫_{[0, m]²} |K₂| y₂^{1/2} = √m (1 - f_s(1))`**, Chen–Hou II, Supp. (5.9). -/
theorem integral_integral_abs_hessianKernel_zero_zero_mul_sqrt_self {m : ℝ} (hm : 0 < m) :
    ∫ y in (0 : ℝ)..m, (∫ x in (0 : ℝ)..m, |hessianKernel 0 0 !₂[x, y]|) * √y =
      √m * (1 - halfPowerIntegral 1) := by
  rw [integral_integral_abs_hessianKernel_zero_zero_mul_sqrt hm hm]
  simp only [le_refl, ↓reduceIte, div_self hm.ne', Real.sqrt_one]
  ring

/-- The inner integral of `C_{K₂,low}`: for `0 < x ≤ 1`,
`∫₀^{x²} |K₂(x, y)| √y dy = x / (2 (1 + x²)) - f_s(√x) / (2√x)`. -/
private theorem integral_parabola_inner {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    ∫ y in (0 : ℝ)..x ^ 2, |hessianKernel 0 0 !₂[x, y]| * √y =
      x / (2 * (1 + x ^ 2)) - halfPowerIntegral (√x) / (2 * √x) := by
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have hxx : x ^ 2 ≤ x := by nlinarith
  have hsx := Real.sqrt_pos.mpr hx
  set H : ℝ → ℝ := fun y ↦ y * √y / (2 * (x ^ 2 + y ^ 2)) -
    1 / (4 * x) * (2 * √x * halfPowerIntegral (√(y / x)))
  have hHc : ContinuousOn H (Icc 0 (x ^ 2)) := by
    refine (ContinuousOn.div (by fun_prop) (by fun_prop) fun y _ ↦ by positivity).sub ?_
    exact (continuous_const.mul (continuous_const.mul (continuous_halfPowerIntegral.comp
      (continuous_id.div_const x).sqrt))).continuousOn
  have hHd : ∀ y ∈ Ioo (0 : ℝ) (x ^ 2), HasDerivAt H
      (hessianKernel 0 0 !₂[x, y] * √y) y := by
    intro y hy
    have hy0 := hy.1
    have h1 : HasDerivAt (fun y ↦ y * √y) (√y + y * (1 / (2 * √y))) y :=
      ((hasDerivAt_id' y).mul (Real.hasDerivAt_sqrt hy0.ne')).congr_deriv (by ring)
    have h2 : HasDerivAt (fun y ↦ 2 * (x ^ 2 + y ^ 2)) (2 * (2 * y)) y := by
      simpa using ((hasDerivAt_pow 2 y).const_add (x ^ 2)).const_mul 2
    have h3 := (h1.div h2 (by positivity)).sub
      ((hasDerivAt_halfPowerPrimitive hx hy0).const_mul (1 / (4 * x)))
    refine h3.congr_deriv ?_
    rw [hessianKernel_zero_zero_toLp]
    obtain ⟨t, ht, rfl⟩ : ∃ t, 0 < t ∧ y = t ^ 2 :=
      ⟨√y, Real.sqrt_pos.mpr hy0, (Real.sq_sqrt hy0.le).symm⟩
    rw [Real.sqrt_sq ht.le]
    field_simp
    ring
  have hKi : IntervalIntegrable (fun y ↦ hessianKernel 0 0 !₂[x, y] * √y) volume 0 (x ^ 2) := by
    refine ContinuousOn.intervalIntegrable ?_
    simp only [hessianKernel_zero_zero_toLp]
    exact ((continuousOn_const.sub (continuous_pow 2).continuousOn).div (by fun_prop)
      fun y _ ↦ by positivity).mul Real.continuous_sqrt.continuousOn
  rw [intervalIntegral.integral_congr (g := fun y ↦ hessianKernel 0 0 !₂[x, y] * √y)
      fun y hy ↦ by
        rw [uIcc_of_le hx2] at hy
        rw [abs_of_nonneg (hessianKernel_zero_zero_toLp_nonneg hy.1 (hy.2.trans hxx))],
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx2 hHc hHd hKi]
  simp only [H, Real.sqrt_sq hx.le, zero_div, Real.sqrt_zero, halfPowerIntegral_zero, mul_zero,
    sub_zero, show x ^ 2 / x = x by field_simp]
  field_simp
  linear_combination (-4 * (1 + x ^ 2) * halfPowerIntegral √x) * Real.mul_self_sqrt hx.le

/-- **`C_{K₂,low} = (log 2 - 2 f_s(1)) / 2`**, Chen–Hou II, Supp. (5.11)-(5.12):
`∫₀¹ ∫₀^{y₁²} |K₂(y)| y₂^{1/2} dy₂ dy₁ = (log 2 - 2 f_s(1)) / 2 = 0.102825...`. -/
theorem integral_integral_abs_hessianKernel_zero_zero_mul_sqrt_parabola :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..x ^ 2, |hessianKernel 0 0 !₂[x, y]| * √y =
      (Real.log 2 - 2 * halfPowerIntegral 1) / 2 := by
  set A : ℝ → ℝ := fun x ↦ Real.log (1 + x ^ 2) / 2 - √x * halfPowerIntegral (√x)
  set g : ℝ → ℝ := fun x ↦ x / (2 * (1 + x ^ 2)) - halfPowerIntegral (√x) / (2 * √x)
  have hAc : ContinuousOn A (Icc 0 1) := by
    refine ((ContinuousOn.log (by fun_prop) fun x _ ↦ by positivity).div_const 2).sub ?_
    exact (Real.continuous_sqrt.mul (continuous_halfPowerIntegral.comp
      Real.continuous_sqrt)).continuousOn
  have hAd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt A (g x) x := by
    intro x hx
    have hx0 := hx.1
    have hs := Real.hasDerivAt_sqrt hx0.ne'
    have h1 : HasDerivAt (fun x ↦ 1 + x ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).const_add 1
    have h := ((h1.log (by positivity)).div_const 2).sub
      (hs.mul ((hasDerivAt_halfPowerIntegral (√x)).comp x hs))
    refine h.congr_deriv ?_
    obtain ⟨t, ht, rfl⟩ : ∃ t, 0 < t ∧ x = t ^ 2 :=
      ⟨√x, Real.sqrt_pos.mpr hx0, (Real.sq_sqrt hx0.le).symm⟩
    simp only [g, Function.comp_apply]
    rw [Real.sqrt_sq ht.le]
    field_simp
    ring
  have hg : ∀ x ∈ Ioo (0 : ℝ) 1,
      ∫ y in (0 : ℝ)..x ^ 2, |hessianKernel 0 0 !₂[x, y]| * √y = g x := fun x hx ↦
    integral_parabola_inner hx.1 hx.2.le
  have hg0 : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ g x := fun x hx ↦ by
    rw [← hg x hx]
    exact intervalIntegral.integral_nonneg (sq_nonneg x) fun y _ ↦
      mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg y)
  have hgi : IntervalIntegrable g volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      (intervalIntegral.integrableOn_deriv_of_nonneg hAc hAd hg0)
  rw [intervalIntegral.integral_congr_ae (g := g) (Eventually.of_forall fun x hx ↦ by
      rw [uIoc_of_le zero_le_one] at hx
      exact integral_parabola_inner hx.1 hx.2),
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hAc hAd hgi]
  simp only [A, Real.sqrt_one, one_pow, Real.sqrt_zero, halfPowerIntegral_zero, mul_zero,
    zero_pow two_ne_zero, add_zero, Real.log_one, zero_div, sub_zero, one_mul]
  norm_num
  ring

end PotentialTheory.Planar
