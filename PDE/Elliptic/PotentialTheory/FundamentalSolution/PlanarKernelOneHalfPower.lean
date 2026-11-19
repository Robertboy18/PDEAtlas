/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarKernelConstants

/-!
# The kernel `K₁` against a half power

Closed forms of Chen and Hou II, Supplementary material II, (5.13), (5.14) and Section 6.1.1,
for `K₁ = hessianKernel 0 1 = y₁ y₂ / |y|⁴` (without the factor `1/π`) and the
function

`f_h(a) = ∫₀ᵃ s^{3/2} / (1 + s²) ds` (`threeHalvesPowerIntegral`).

The three iterated integrals of `K₁` against `√u` or `√v`, on the square `[0, δ]²` and on strips
of it, are behind the singular-region bounds of `u_x` (Supp. 6.1.1). With `δ = 1` and `α = t`
they are the integrals `I₁`, `I₂` of Supp. 6.1.1, and `∫_{[0,1]²} K₁ y₁^{1/2} = 1 - f_h(1)/2`.

The integrals with a half power touch the pole; they are iterated integrals, as in the paper.

## Main definitions

* `threeHalvesPowerIntegral`: `f_h(a) = ∫₀ᵃ s^{3/2} / (1 + s²) ds`.

## Main results

* `threeHalvesPowerIntegral_eq`: `f_h(a) = 2 √a - π/√2 + 2 f_s(1/√a)` for `a > 0`, with
  `f_s = halfPowerIntegral`.
* `integral_inv_one_add_pow_four`: `∫₀ˣ dt/(1 + t⁴) = π/(2√2) - f_s(1/x)` for `x > 0`.
* `integral_mul_sqrt_div_sq_add_sq`: `∫₀ᵃ s^{3/2} / (p² + s²) ds = √p f_h(a/p)`, (5.14).
* `integral_hessianKernel_zero_one_right`: `∫_c^d K₁(u, v) dv = u/(2(u² + c²)) - u/(2(u² + d²))`.
* `integral_integral_hessianKernel_zero_one_mul_sqrt`: for `0 < t ≤ δ`,
  `∫₀^δ (∫_t^δ K₁ dv) √u du = (√t f_h(δ/t) - √δ f_h(1)) / 2`.
* `integral_integral_hessianKernel_zero_one_mul_sqrt_self`:
  `∫₀^δ (∫₀^δ K₁ dv) √u du = √δ (2 - f_h(1)) / 2`.
* `integral_integral_hessianKernel_zero_one_mul_sqrt_left`: for `t ≥ 0` and `δ > 0`,
  `∫₀^t (∫₀^δ K₁ du) √v dv = (2√t - √δ f_h(t/δ)) / 2`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Supplementary
  material II, Section 5.1.2, (5.13)-(5.14), and Section 6.1.1.
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Interval

namespace PotentialTheory.Planar

/-! ### The function `f_h` -/

/-- For `p ≠ 0` the integrand `s ↦ s √s / (p² + s²)` is continuous. -/
theorem continuous_mul_sqrt_div_sq_add_sq {p : ℝ} (hp : p ≠ 0) :
    Continuous fun s : ℝ ↦ s * √s / (p ^ 2 + s ^ 2) :=
  (continuous_id.mul Real.continuous_sqrt).div (by fun_prop) fun s ↦ by positivity

/-- `f_h(a) = ∫₀ᵃ s^{3/2} / (1 + s²) ds` of Chen and Hou II, Supp. (5.13), written with
`s^{3/2} = s √s`. -/
def threeHalvesPowerIntegral (a : ℝ) : ℝ := ∫ s in (0 : ℝ)..a, s * √s / (1 + s ^ 2)

/-- The integrand `s ↦ s √s / (1 + s²)` of `f_h` is continuous. -/
private theorem continuous_threeHalvesIntegrand : Continuous fun s : ℝ ↦ s * √s / (1 + s ^ 2) := by
  simpa using continuous_mul_sqrt_div_sq_add_sq (p := 1) one_ne_zero

/-- The derivative of `f_h` at `a` is `a √a / (1 + a²)`. -/
theorem hasDerivAt_threeHalvesPowerIntegral (a : ℝ) :
    HasDerivAt threeHalvesPowerIntegral (a * √a / (1 + a ^ 2)) a :=
  intervalIntegral.integral_hasDerivAt_right
    (continuous_threeHalvesIntegrand.intervalIntegrable 0 a)
    (continuous_threeHalvesIntegrand.stronglyMeasurableAtFilter _ _)
    continuous_threeHalvesIntegrand.continuousAt

/-- The function `f_h` is continuous. -/
theorem continuous_threeHalvesPowerIntegral : Continuous threeHalvesPowerIntegral :=
  continuous_iff_continuousAt.mpr fun a ↦ (hasDerivAt_threeHalvesPowerIntegral a).continuousAt

/-- `f_h(0) = 0`. -/
@[simp] theorem threeHalvesPowerIntegral_zero : threeHalvesPowerIntegral 0 = 0 := by
  simp [threeHalvesPowerIntegral]

/-- `f_h` is nondecreasing on `[0, ∞)`. -/
theorem monotoneOn_threeHalvesPowerIntegral : MonotoneOn threeHalvesPowerIntegral (Ici 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
    continuous_threeHalvesPowerIntegral.continuousOn
    (fun a _ ↦ (hasDerivAt_threeHalvesPowerIntegral a).differentiableAt.differentiableWithinAt)
    fun a ha ↦ ?_
  rw [interior_Ici] at ha
  rw [(hasDerivAt_threeHalvesPowerIntegral a).deriv]
  have : 0 < a := ha
  positivity

/-- `f_h(a) ≥ 0` for `a ≥ 0`. -/
theorem threeHalvesPowerIntegral_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ threeHalvesPowerIntegral a := by
  simpa using monotoneOn_threeHalvesPowerIntegral (mem_Ici.2 le_rfl) (mem_Ici.2 ha) ha

/-- The function `t ↦ 1 / (1 + t⁴)` is continuous. -/
private theorem continuous_inv_one_add_pow_four : Continuous fun t : ℝ ↦ 1 / (1 + t ^ 4) :=
  continuous_const.div (by fun_prop) fun t ↦ by positivity

/-- `∫₀ˣ dt / (1 + t⁴) = π / (2√2) - f_s(1/x)` for `x > 0`: the substitution `t ↦ 1/t` turns the
integral into the tail `∫_{1/x}^∞ s² / (1 + s⁴) ds` of `f_s(∞) = π / (2√2)`. -/
theorem integral_inv_one_add_pow_four {x : ℝ} (hx : 0 < x) :
    ∫ t in (0 : ℝ)..x, 1 / (1 + t ^ 4) = Real.pi / (2 * √2) - halfPowerIntegral (1 / x) := by
  set R : ℝ → ℝ := fun t ↦ Real.pi / (2 * √2) - halfPowerIntegral (1 / t) with hR
  have hderiv : ∀ t, 0 < t → HasDerivAt R (1 / (1 + t ^ 4)) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ ↦ 1 / t) (-(1 / t ^ 2)) t := by
      simpa [one_div] using hasDerivAt_inv ht.ne'
    have h := ((hasDerivAt_halfPowerIntegral (1 / t)).comp t h1).const_sub (Real.pi / (2 * √2))
    refine h.congr_deriv ?_
    field_simp
    ring
  have hcontR : ContinuousOn R (Ioi 0) := fun t ht ↦ (hderiv t ht).continuousAt.continuousWithinAt
  -- the two sides agree on every `[ε, x]`; let `ε → 0⁺`
  have hInt : Continuous fun y : ℝ ↦ ∫ t in (0 : ℝ)..y, 1 / (1 + t ^ 4) :=
    intervalIntegral.continuous_primitive
      (fun a b ↦ continuous_inv_one_add_pow_four.intervalIntegrable a b) 0
  have hR0 : Tendsto R (𝓝[>] 0) (𝓝 0) := by
    have hinv : Tendsto (fun t : ℝ ↦ 1 / t) (𝓝[>] 0) atTop := by
      simpa [one_div] using tendsto_inv_nhdsGT_zero
    have := (tendsto_halfPowerIntegral_atTop.comp hinv).const_sub (Real.pi / (2 * √2))
    simpa [hR, sub_self] using this
  have hlim : Tendsto (fun ε : ℝ ↦ (∫ t in (0 : ℝ)..ε, 1 / (1 + t ^ 4)) + (R x - R ε))
      (𝓝[>] 0) (𝓝 (0 + (R x - 0))) := by
    refine Tendsto.add ?_ (tendsto_const_nhds.sub hR0)
    have := (hInt.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (∫ t in (0 : ℝ)..ε, 1 / (1 + t ^ 4)) + (R x - R ε) =
      ∫ t in (0 : ℝ)..x, 1 / (1 + t ^ 4) := by
    filter_upwards [Ioo_mem_nhdsGT hx] with ε hε
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (continuous_inv_one_add_pow_four.intervalIntegrable 0 ε)
      (continuous_inv_one_add_pow_four.intervalIntegrable ε x)]
    congr 1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht ↦ hderiv t ?_)
      (continuous_inv_one_add_pow_four.intervalIntegrable ε x)]
    rw [uIcc_of_le hε.2.le] at ht
    exact hε.1.trans_le ht.1
  have := tendsto_nhds_unique (hlim.congr' heq) tendsto_const_nhds
  rw [← this]
  simp [hR]

/-- The primitive `2√s - 2 ∫₀^{√s} dt/(1 + t⁴)` of `s^{3/2} / (1 + s²)` on `s > 0`. -/
private theorem hasDerivAt_threeHalvesPrimitive {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun s ↦ 2 * √s - 2 * ∫ t in (0 : ℝ)..√s, 1 / (1 + t ^ 4))
      (s * √s / (1 + s ^ 2)) s := by
  have hsq : HasDerivAt (fun s ↦ √s) (1 / (2 * √s)) s := by
    simpa using Real.hasDerivAt_sqrt hs.ne'
  have hI : HasDerivAt (fun y ↦ ∫ t in (0 : ℝ)..y, 1 / (1 + t ^ 4)) (1 / (1 + √s ^ 4)) √s :=
    intervalIntegral.integral_hasDerivAt_right
      (continuous_inv_one_add_pow_four.intervalIntegrable 0 _)
      (continuous_inv_one_add_pow_four.stronglyMeasurableAtFilter _ _)
      continuous_inv_one_add_pow_four.continuousAt
  have h := (hsq.const_mul 2).sub ((hI.comp s hsq).const_mul 2)
  refine h.congr_deriv ?_
  obtain ⟨r, hr, rfl⟩ : ∃ r, 0 < r ∧ s = r ^ 2 :=
    ⟨√s, Real.sqrt_pos.mpr hs, (Real.sq_sqrt hs.le).symm⟩
  rw [Real.sqrt_sq hr.le]
  field_simp
  ring

/-- `f_h(a) = 2√a - 2 ∫₀^{√a} dt / (1 + t⁴)` for `a ≥ 0`, by `s = t²`. -/
private theorem threeHalvesPowerIntegral_eq_sub {a : ℝ} (ha : 0 ≤ a) :
    threeHalvesPowerIntegral a = 2 * √a - 2 * ∫ t in (0 : ℝ)..√a, 1 / (1 + t ^ 4) := by
  have hcont : ContinuousOn (fun s ↦ 2 * √s - 2 * ∫ t in (0 : ℝ)..√s, 1 / (1 + t ^ 4))
      (Icc 0 a) := by
    have hI : Continuous fun y : ℝ ↦ ∫ t in (0 : ℝ)..y, 1 / (1 + t ^ 4) :=
      intervalIntegral.continuous_primitive
      (fun a b ↦ continuous_inv_one_add_pow_four.intervalIntegrable a b) 0
    exact ((continuous_const.mul Real.continuous_sqrt).sub
      (continuous_const.mul (hI.comp Real.continuous_sqrt))).continuousOn
  rw [threeHalvesPowerIntegral, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha hcont
    (fun s hs ↦ hasDerivAt_threeHalvesPrimitive hs.1)
    (continuous_threeHalvesIntegrand.intervalIntegrable 0 a)]
  simp

/-- **`f_h` through `f_s`**: for `a > 0`, `f_h(a) = 2 √a - π/√2 + 2 f_s(1/√a)`. -/
theorem threeHalvesPowerIntegral_eq {a : ℝ} (ha : 0 < a) :
    threeHalvesPowerIntegral a = 2 * √a - Real.pi / √2 + 2 * halfPowerIntegral (1 / √a) := by
  rw [threeHalvesPowerIntegral_eq_sub ha.le, integral_inv_one_add_pow_four (Real.sqrt_pos.2 ha)]
  have : (√2 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- **`f_h(1) = 2 - π/√2 + 2 f_s(1)`**. -/
theorem threeHalvesPowerIntegral_one :
    threeHalvesPowerIntegral 1 = 2 - Real.pi / √2 + 2 * halfPowerIntegral 1 := by
  simpa using threeHalvesPowerIntegral_eq one_pos

/-- **The substitution of Supp. (5.14)**: for `p > 0`,
`∫₀ᵃ s^{3/2} / (p² + s²) ds = √p f_h(a/p)`. -/
theorem integral_mul_sqrt_div_sq_add_sq {p a : ℝ} (hp : 0 < p) :
    ∫ s in (0 : ℝ)..a, s * √s / (p ^ 2 + s ^ 2) = √p * threeHalvesPowerIntegral (a / p) := by
  have h := intervalIntegral.smul_integral_comp_mul_left
    (fun s : ℝ ↦ s * √s / (p ^ 2 + s ^ 2)) p (a := 0) (b := a / p)
  rw [mul_zero, mul_div_cancel₀ _ hp.ne'] at h
  rw [← h, threeHalvesPowerIntegral, smul_eq_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  have hsp : √p ^ 2 = p := Real.sq_sqrt hp.le
  have hsp0 : 0 < √p := Real.sqrt_pos.2 hp
  congr 1
  ext s
  rcases le_or_gt s 0 with hs | hs
  · rw [Real.sqrt_eq_zero'.2 hs, Real.sqrt_eq_zero'.2 (mul_nonpos_of_nonneg_of_nonpos hp.le hs)]
    simp
  rw [Real.sqrt_mul hp.le]
  rw [← hsp]
  field_simp

/-! ### Inner integrals of `K₁` -/

/-- `∫_c^d K₁(u, v) dv = u / (2 (u² + c²)) - u / (2 (u² + d²))` when the segment avoids the
pole. -/
theorem integral_hessianKernel_zero_one_right {u c d : ℝ}
    (h : ∀ v ∈ uIcc c d, u ^ 2 + v ^ 2 ≠ 0) :
    ∫ v in c..d, hessianKernel 0 1 !₂[u, v] =
      u / (2 * (u ^ 2 + c ^ 2)) - u / (2 * (u ^ 2 + d ^ 2)) := by
  have hd : ∀ v ∈ uIcc c d, HasDerivAt (fun v ↦ -(u / (2 * (u ^ 2 + v ^ 2))))
      (hessianKernel 0 1 !₂[u, v]) v := by
    intro v hv
    have hne := h v hv
    have h1 : HasDerivAt (fun v ↦ 2 * (u ^ 2 + v ^ 2)) (2 * (2 * v)) v := by
      have := ((hasDerivAt_pow 2 v).const_add (u ^ 2)).const_mul 2
      simpa using this
    have h2 := (h1.inv (mul_ne_zero two_ne_zero hne)).const_mul u
    have h3 := h2.neg
    rw [hessianKernel_zero_one_toLp]
    convert h3 using 1
    · ext v; simp [div_eq_mul_inv]
    · field_simp
  have hcont : ContinuousOn (fun v ↦ hessianKernel 0 1 !₂[u, v]) (uIcc c d) := by
    simp only [hessianKernel_zero_one_toLp]
    exact continuousOn_const.mul continuousOn_id |>.div (by fun_prop)
      fun v hv ↦ pow_ne_zero 2 (h v hv)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable]
  ring

/-- `∫_a^b K₁(u, v) du = v / (2 (a² + v²)) - v / (2 (b² + v²))`. On the line `v = 0` both sides
vanish. -/
theorem integral_hessianKernel_zero_one_left {v a b : ℝ} :
    ∫ u in a..b, hessianKernel 0 1 !₂[u, v] =
      v / (2 * (a ^ 2 + v ^ 2)) - v / (2 * (b ^ 2 + v ^ 2)) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [hessianKernel_zero_one_toLp]
  have hsym : ∀ u, hessianKernel 0 1 !₂[u, v] = hessianKernel 0 1 !₂[v, u] := fun u ↦ by
    simp only [hessianKernel_zero_one_toLp]; ring
  simp_rw [hsym]
  rw [integral_hessianKernel_zero_one_right fun u _ ↦ by positivity]
  ring

/-- The inner integral over `[0, δ]`: `∫₀^δ K₁(u, v) dv = 1/(2u) - u/(2(u² + δ²))`,
with the value `0` at `u = 0` on both sides. -/
theorem integral_hessianKernel_zero_one_right_zero {u δ : ℝ} (hδ : 0 < δ) :
    ∫ v in (0 : ℝ)..δ, hessianKernel 0 1 !₂[u, v] = 1 / (2 * u) - u / (2 * (u ^ 2 + δ ^ 2)) := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp [hessianKernel_zero_one_toLp]
  rw [integral_hessianKernel_zero_one_right fun v _ ↦ by positivity]
  field_simp
  ring

/-! ### Iterated integrals with a half power -/

/-- `∫₀^δ 1/(2√u) du = √δ`. -/
theorem integral_inv_two_sqrt {δ : ℝ} (hδ : 0 ≤ δ) :
    ∫ u in (0 : ℝ)..δ, 1 / (2 * √u) = √δ := by
  have hd : ∀ u ∈ Ioo 0 δ, HasDerivAt (fun u ↦ √u) (1 / (2 * √u)) u := fun u hu ↦ by
    simpa using Real.hasDerivAt_sqrt hu.1.ne'
  have hint : IntervalIntegrable (fun u ↦ 1 / (2 * √u)) volume 0 δ := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hδ]
    exact intervalIntegral.integrableOn_deriv_of_nonneg Real.continuous_sqrt.continuousOn hd
      fun u _ ↦ by positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hδ Real.continuous_sqrt.continuousOn
    hd hint]
  simp

/-- `u ↦ 1/(2√u)` is integrable on `[0, δ]`. -/
theorem intervalIntegrable_inv_two_sqrt {δ : ℝ} (hδ : 0 ≤ δ) :
    IntervalIntegrable (fun u ↦ 1 / (2 * √u)) volume 0 δ := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hδ]
  exact intervalIntegral.integrableOn_deriv_of_nonneg Real.continuous_sqrt.continuousOn
    (fun u hu ↦ by simpa using Real.hasDerivAt_sqrt hu.1.ne') fun u _ ↦ by positivity

/-- For `0 < t ≤ δ`, the inner integral over the strip in closed form:
`(∫_t^δ K₁(u, v) dv) √u = (u √u / (t² + u²) - u √u / (δ² + u²)) / 2`. -/
private theorem integral_strip_mul_sqrt_eq {δ t : ℝ} (ht : 0 < t) (htδ : t ≤ δ) (u : ℝ) :
    (∫ v in t..δ, hessianKernel 0 1 !₂[u, v]) * √u =
      (u * √u / (t ^ 2 + u ^ 2) - u * √u / (δ ^ 2 + u ^ 2)) / 2 := by
  have hδ : 0 < δ := ht.trans_le htδ
  rw [integral_hessianKernel_zero_one_right fun v hv ↦ by
    rw [uIcc_of_le htδ] at hv
    have : 0 < v := ht.trans_le hv.1
    positivity]
  have h1 : 0 < u ^ 2 + t ^ 2 := by positivity
  have h2 : 0 < u ^ 2 + δ ^ 2 := by positivity
  field_simp
  ring

/-- For `δ > 0`, the inner integral over the square in closed form:
`(∫₀^δ K₁(u, v) dv) √u = 1/(2√u) - u √u / (2(δ² + u²))`. -/
private theorem integral_square_mul_sqrt_eq {δ : ℝ} (hδ : 0 < δ) (u : ℝ) :
    (∫ v in (0 : ℝ)..δ, hessianKernel 0 1 !₂[u, v]) * √u =
      1 / (2 * √u) - (u * √u / (δ ^ 2 + u ^ 2)) / 2 := by
  rw [integral_hessianKernel_zero_one_right_zero hδ]
  rcases le_or_gt u 0 with hu | hu
  · rw [Real.sqrt_eq_zero'.2 hu]; simp
  obtain ⟨r, hr, rfl⟩ : ∃ r, 0 < r ∧ u = r ^ 2 :=
    ⟨√u, Real.sqrt_pos.mpr hu, (Real.sq_sqrt hu.le).symm⟩
  rw [Real.sqrt_sq hr.le]
  field_simp
  ring

/-- For `δ > 0`, the inner integral in the first variable in closed form:
`(∫₀^δ K₁(u, v) du) √v = 1/(2√v) - v √v / (2(δ² + v²))`. -/
private theorem integral_left_mul_sqrt_eq {δ : ℝ} (hδ : 0 < δ) (v : ℝ) :
    (∫ u in (0 : ℝ)..δ, hessianKernel 0 1 !₂[u, v]) * √v =
      1 / (2 * √v) - (v * √v / (δ ^ 2 + v ^ 2)) / 2 := by
  have hsym : (∫ u in (0 : ℝ)..δ, hessianKernel 0 1 !₂[u, v]) =
      ∫ u in (0 : ℝ)..δ, hessianKernel 0 1 !₂[v, u] := by
    congr 1; ext u; simp only [hessianKernel_zero_one_toLp]; ring
  rw [hsym]
  exact integral_square_mul_sqrt_eq hδ v

/-- The integrand of `integral_integral_hessianKernel_zero_one_mul_sqrt` is integrable on
`[0, a]`, for `a ≥ 0` and `0 ≤ c ≤ d`. -/
theorem intervalIntegrable_integral_hessianKernel_zero_one_mul_sqrt {a c d : ℝ} (ha : 0 ≤ a)
    (hc : 0 ≤ c) (hcd : c ≤ d) :
    IntervalIntegrable (fun u ↦ (∫ v in c..d, hessianKernel 0 1 !₂[u, v]) * √u) volume 0 a := by
  rcases hc.eq_or_lt with rfl | hc
  · rcases hcd.eq_or_lt with rfl | hd
    · simp
    simp_rw [integral_square_mul_sqrt_eq hd]
    exact (intervalIntegrable_inv_two_sqrt ha).sub
      (((continuous_mul_sqrt_div_sq_add_sq hd.ne').intervalIntegrable 0 a).div_const 2)
  · have hd : 0 < d := hc.trans_le hcd
    simp_rw [integral_strip_mul_sqrt_eq hc hcd]
    exact (((continuous_mul_sqrt_div_sq_add_sq hc.ne').intervalIntegrable 0 a).sub
      ((continuous_mul_sqrt_div_sq_add_sq hd.ne').intervalIntegrable 0 a)).div_const 2

/-- The integrand of `integral_integral_hessianKernel_zero_one_mul_sqrt_left` is integrable on
`[0, t]`, for `t ≥ 0` and `δ > 0`. -/
theorem intervalIntegrable_integral_hessianKernel_zero_one_mul_sqrt_left {δ t : ℝ} (hδ : 0 < δ)
    (ht : 0 ≤ t) :
    IntervalIntegrable (fun v ↦ (∫ u in (0 : ℝ)..δ, hessianKernel 0 1 !₂[u, v]) * √v)
      volume 0 t := by
  simp_rw [integral_left_mul_sqrt_eq hδ]
  exact (intervalIntegrable_inv_two_sqrt ht).sub
    (((continuous_mul_sqrt_div_sq_add_sq hδ.ne').intervalIntegrable 0 t).div_const 2)

/-- **The first integral of Supp. 6.1 on a strip**: for `0 < t ≤ δ`,
`∫₀^δ (∫_t^δ K₁(u, v) dv) √u du = (√t f_h(δ/t) - √δ f_h(1)) / 2`. -/
theorem integral_integral_hessianKernel_zero_one_mul_sqrt {δ t : ℝ} (ht : 0 < t) (htδ : t ≤ δ) :
    ∫ u in (0 : ℝ)..δ, (∫ v in t..δ, hessianKernel 0 1 !₂[u, v]) * √u =
      (√t * threeHalvesPowerIntegral (δ / t) - √δ * threeHalvesPowerIntegral 1) / 2 := by
  have hδ : 0 < δ := ht.trans_le htδ
  simp_rw [integral_strip_mul_sqrt_eq ht htδ]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
      ((continuous_mul_sqrt_div_sq_add_sq ht.ne').intervalIntegrable 0 δ)
      ((continuous_mul_sqrt_div_sq_add_sq hδ.ne').intervalIntegrable 0 δ),
    integral_mul_sqrt_div_sq_add_sq ht, integral_mul_sqrt_div_sq_add_sq hδ, div_self hδ.ne']

/-- **The first integral of Supp. 6.1 on the square**:
`∫₀^δ (∫₀^δ K₁(u, v) dv) √u du = √δ (2 - f_h(1)) / 2`; for `δ = 1`, `1 - f_h(1)/2`. -/
theorem integral_integral_hessianKernel_zero_one_mul_sqrt_self {δ : ℝ} (hδ : 0 < δ) :
    ∫ u in (0 : ℝ)..δ, (∫ v in (0 : ℝ)..δ, hessianKernel 0 1 !₂[u, v]) * √u =
      √δ * (2 - threeHalvesPowerIntegral 1) / 2 := by
  simp_rw [integral_square_mul_sqrt_eq hδ]
  rw [intervalIntegral.integral_sub (intervalIntegrable_inv_two_sqrt hδ.le)
      (((continuous_mul_sqrt_div_sq_add_sq hδ.ne').intervalIntegrable 0 δ).div_const 2),
    integral_inv_two_sqrt hδ.le, intervalIntegral.integral_div,
    integral_mul_sqrt_div_sq_add_sq hδ, div_self hδ.ne']
  ring

/-- **The second integral of Supp. 6.1**: for `t ≥ 0` and `δ > 0`,
`∫₀^t (∫₀^δ K₁(u, v) du) √v dv = (2√t - √δ f_h(t/δ)) / 2`. -/
theorem integral_integral_hessianKernel_zero_one_mul_sqrt_left {δ t : ℝ} (hδ : 0 < δ)
    (ht : 0 ≤ t) :
    ∫ v in (0 : ℝ)..t, (∫ u in (0 : ℝ)..δ, hessianKernel 0 1 !₂[u, v]) * √v =
      (2 * √t - √δ * threeHalvesPowerIntegral (t / δ)) / 2 := by
  simp_rw [integral_left_mul_sqrt_eq hδ]
  rw [intervalIntegral.integral_sub (intervalIntegrable_inv_two_sqrt ht)
      (((continuous_mul_sqrt_div_sq_add_sq hδ.ne').intervalIntegrable 0 t).div_const 2),
    integral_inv_two_sqrt ht, intervalIntegral.integral_div, integral_mul_sqrt_div_sq_add_sq hδ]
  ring

end PotentialTheory.Planar
