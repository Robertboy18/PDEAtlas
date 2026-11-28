/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import PDE.Analysis.Calculus.AbsolutelyContinuous.Rpow

/-!
# Bliss's inequality: the sharp Sobolev inequality for radial functions

Let `a > 0`, `p = 2 + 2/a` and `R ≥ 0`, and let `φ` be a Lipschitz function on the line with
`φ ≥ 0` on `[0, R]` and `φ(R) = 0`. Then

`a (a + 1) (4κ)^{1/(a+1)} (∫₀^R r^{2a+1} φ^p dr)^{a/(a+1)} ≤ ∫₀^R r^{2a+1} φ'² dr`,

with `κ = ∫₀¹ s √(1 - s^{2/a}) ds`. For `a = (n - 2) / 2` the weight is `r^{n-1}` and
`p = 2n / (n - 2)`, so for a radial function `u(x) = φ(|x|)` on `ℝⁿ` the two sides are, up to
powers of the area of the unit sphere, `‖u‖_p²` and `‖∇u‖₂²`. This is the one-dimensional
problem behind the sharp Sobolev inequality. Bliss found the best constant in 1930. Only the
inequality is proved here: that the constant is the best one is not, the extremal functions
are not characterized, and the version with `∫ |φ'|^q` for `q ≠ 2` is not treated.

## Main results

* `blissKappa a`: the number `κ`, nonnegative for every `a` and positive for `a > 0`. Its value
  `√π Γ(a + 1) / (4 Γ(a + 3/2))` is `blissKappa_eq`.
* `bliss_step`: the inequality on one interval `[α, β]`, `0 ≤ α`, where `φ ≥ 0` and
  `r^a φ(r) ≤ M`, for both signs.
* `bliss_inequality`: Bliss's inequality above.

## How it works

Put `W(r) = r^a φ(r)`. It vanishes at `r = 0` and where `φ` does, and

`r^{2a+1} φ'² = r W'² + a² W² / r - a (W²)'`.

Let `M` be the maximum of `W` and `h(s) = a s √(1 - (s/M)^{2/a})` for `0 ≤ s ≤ M`
(`blissProfile`), so that `h(W)² = a² W² - a² M^{-2/a} W^p`. The inequality
`r W'² + h(W)² / r ≥ 2 |W'| h(W)` then gives

`r^{2a+1} φ'² ≥ ± 2 h(W) W' - a (W²)' + a² M^{-2/a} r^{2a+1} φ^p`,

with either sign. The first two terms on the right are the derivative of `± 2 Ψ(W) - a W²`,
where `Ψ' = h` (`blissPrimitive`). Integrate with the sign `+` from `0` to a point where
`W = M`, and with the sign `-` from there to `R`:

`∫ r^{2a+1} φ'² ≥ 4 Ψ(M) + a² M^{-2/a} ∫ r^{2a+1} φ^p`,  `Ψ(M) = a M² κ`.

The inequality between the weighted arithmetic and geometric means removes `M` and leaves
`a (a + 1) (4κ)^{1/(a+1)} (∫ r^{2a+1} φ^p)^{a/(a+1)}`. The profile `h` is the one of
`φ(r) = (1 + r²)^{-a}`, for which every step is an equality on the half line. That function
does not vanish at a finite `R`, and the case of equality is not proved. Bliss used the
calculus of variations. Here the square is completed along the profile of the extremal
function, and Mathlib's fundamental theorem of calculus for absolutely continuous functions
(`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`) integrates the result.

## References

* G. A. Bliss, "An integral inequality", *J. London Math. Soc.* 5 (1930), 40-46: the
  inequality and its extremal functions.
* G. Talenti, "Best constant in Sobolev inequality", *Ann. Mat. Pura Appl.* 110 (1976), 353-372:
  the reduction of the Sobolev inequality to this one. <https://doi.org/10.1007/BF02418013>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped NNReal Topology

namespace SobolevSpace.Inequalities

variable {a M : ℝ}

/-! ## The profile `h` and its primitive -/

/-- The number `κ(a) = ∫₀¹ s √(1 - s^{2/a}) ds` in the constant of Bliss's inequality. -/
def blissKappa (a : ℝ) : ℝ := ∫ s in (0 : ℝ)..1, s * √(1 - s ^ (2 / a))

/-- The number `κ(a)` is nonnegative for every real `a`: the integrand is. -/
theorem blissKappa_nonneg (a : ℝ) : 0 ≤ blissKappa a :=
  intervalIntegral.integral_nonneg zero_le_one fun _ hs ↦ mul_nonneg hs.1 (Real.sqrt_nonneg _)

/-- For `a > 0` the number `κ(a)` is positive: the integrand is positive on `(0, 1)`. -/
theorem blissKappa_pos (ha : 0 < a) : 0 < blissKappa a := by
  have hc : Continuous fun s : ℝ ↦ s * √(1 - s ^ (2 / a)) :=
    continuous_id.mul (Real.continuous_sqrt.comp
      (continuous_const.sub (Real.continuous_rpow_const (by positivity))))
  refine intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable 0 1)
    (fun s hs ↦ ?_) zero_lt_one
  have h1 : s ^ (2 / a) < 1 := Real.rpow_lt_one hs.1.le hs.2 (by positivity)
  exact mul_pos hs.1 (Real.sqrt_pos.mpr (sub_pos.mpr h1))

/-- The profile `h(s) = a s √(1 - (s/M)^{2/a})`: the slope `r W'` of an extremal function as a
function of its value `W = s`, when the maximum of `W` is `M`. -/
def blissProfile (a M s : ℝ) : ℝ := a * s * √(1 - (s / M) ^ (2 / a))

/-- The profile is continuous on the line, for `a > 0`. -/
theorem continuous_blissProfile (ha : 0 < a) (M : ℝ) : Continuous (blissProfile a M) :=
  (continuous_const.mul continuous_id).mul (Real.continuous_sqrt.comp
    (continuous_const.sub ((continuous_id.div_const M).rpow_const fun _ ↦ Or.inr (by positivity))))

/-- On `[0, M]` the square of the profile is `a² s² - a² M^{-2/a} s^{2 + 2/a}`. -/
theorem blissProfile_sq (ha : 0 < a) (hM : 0 < M) {s : ℝ} (hs : 0 ≤ s) (hsM : s ≤ M) :
    blissProfile a M s ^ 2 = a ^ 2 * s ^ 2 - a ^ 2 / M ^ (2 / a) * s ^ (2 + 2 / a) := by
  have h1 : (s / M) ^ (2 / a) ≤ 1 :=
    Real.rpow_le_one (div_nonneg hs hM.le) ((div_le_one hM).mpr hsM) (by positivity)
  have h2 : s ^ (2 + 2 / a) = s ^ 2 * s ^ (2 / a) := by
    rw [Real.rpow_add' hs (by positivity), Real.rpow_two]
  have hM' : M ^ (2 / a) ≠ 0 := (Real.rpow_pos_of_pos hM _).ne'
  rw [blissProfile, mul_pow, Real.sq_sqrt (sub_nonneg.mpr h1), Real.div_rpow hs hM.le, h2]
  field_simp

/-- On `[0, M]` the profile is at most `a M`. -/
theorem abs_blissProfile_le (ha : 0 < a) (hM : 0 < M) {s : ℝ} (hs : 0 ≤ s) (hsM : s ≤ M) :
    |blissProfile a M s| ≤ a * M := by
  have h1 : √(1 - (s / M) ^ (2 / a)) ≤ 1 := by
    have h := Real.sqrt_le_sqrt
      (sub_le_self 1 (Real.rpow_nonneg (div_nonneg hs hM.le) (2 / a)))
    rwa [Real.sqrt_one] at h
  rw [blissProfile, abs_mul, abs_mul, abs_of_pos ha, abs_of_nonneg hs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc a * s * √(1 - (s / M) ^ (2 / a)) ≤ a * M * 1 := by gcongr
    _ = a * M := mul_one _

/-- The primitive `Ψ(s) = ∫₀^s h` of the profile. -/
def blissPrimitive (a M s : ℝ) : ℝ := ∫ σ in (0 : ℝ)..s, blissProfile a M σ

/-- The derivative of the primitive `Ψ` is the profile `h`, at every point. -/
theorem hasDerivAt_blissPrimitive (ha : 0 < a) (M s : ℝ) :
    HasDerivAt (blissPrimitive a M) (blissProfile a M s) s :=
  intervalIntegral.integral_hasDerivAt_right
    ((continuous_blissProfile ha M).intervalIntegrable _ _)
    ((continuous_blissProfile ha M).stronglyMeasurableAtFilter _ _)
    (continuous_blissProfile ha M).continuousAt

/-- The primitive vanishes at `0`. -/
@[simp]
theorem blissPrimitive_zero : blissPrimitive a M 0 = 0 := intervalIntegral.integral_same

/-- The value of the primitive at the maximum: `Ψ(M) = a M² κ`. -/
theorem blissPrimitive_self (hM : 0 < M) : blissPrimitive a M M = a * M ^ 2 * blissKappa a := by
  have h := intervalIntegral.integral_comp_div (a := 0) (b := M)
    (fun s ↦ a * M * (s * √(1 - s ^ (2 / a)))) hM.ne'
  have e : ∀ x, a * M * (x / M * √(1 - (x / M) ^ (2 / a))) = blissProfile a M x := fun x ↦ by
    rw [blissProfile]
    field_simp
  simp only [e, zero_div, div_self hM.ne', smul_eq_mul] at h
  rw [blissPrimitive, h, intervalIntegral.integral_const_mul, blissKappa]
  ring

/-! ## The inequality on an interval -/

/-- For a continuous `φ` and exponents `b, q ≥ 0` the function `r ↦ r^b φ(r)^q` is continuous
on the line. With `b = 2a + 1` and `q = 2 + 2/a` it is the integrand of the left side of
Bliss's inequality. -/
theorem continuous_rpow_mul_rpow {b q : ℝ} (hb : 0 ≤ b) (hq : 0 ≤ q) {φ : ℝ → ℝ}
    (hφ : Continuous φ) : Continuous fun r : ℝ ↦ r ^ b * φ r ^ q :=
  (Real.continuous_rpow_const hb).mul (hφ.rpow_const fun _ ↦ Or.inr hq)

/-- For a Lipschitz `φ` and `b ≥ 0` the function `r ↦ r^b φ'(r)²` is integrable on every
bounded interval: `φ'` is measurable and bounded by the Lipschitz constant. -/
theorem intervalIntegrable_rpow_mul_deriv_sq {L : ℝ≥0} {φ : ℝ → ℝ} (hφ : LipschitzWith L φ)
    {b : ℝ} (hb : 0 ≤ b) (α β : ℝ) :
    IntervalIntegrable (fun r : ℝ ↦ r ^ b * deriv φ r ^ 2) volume α β := by
  have hd2 : IntervalIntegrable (fun r : ℝ ↦ deriv φ r ^ 2) volume α β := by
    refine (intervalIntegrable_const (c := (L : ℝ) ^ 2)).mono_fun'
      ((measurable_deriv φ).pow_const 2).aestronglyMeasurable (Eventually.of_forall fun r ↦ ?_)
    change ‖deriv φ r ^ 2‖ ≤ (L : ℝ) ^ 2
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using norm_deriv_le_of_lipschitz hφ) 2
  exact hd2.continuousOn_mul (Real.continuous_rpow_const hb).continuousOn

/-- **Bliss's inequality on one interval.** Let `φ` be Lipschitz, `0 ≤ α ≤ β`, and `φ ≥ 0`,
`W(r) = r^a φ(r) ≤ M` on `[α, β]`. With `Ψ' = h` and either sign `σ = ±1`,

`[2σ Ψ(W) - a W²]_α^β + a² M^{-2/a} ∫_α^β r^{2a+1} φ^p ≤ ∫_α^β r^{2a+1} φ'²`, `p = 2 + 2/a`.

The left side is the integral of a function that is pointwise at most `r^{2a+1} φ'²`: the
difference is `(r W' - σ h(W))² / r`. -/
theorem bliss_step (ha : 0 < a) (hM : 0 < M) {L : ℝ≥0} {φ : ℝ → ℝ} (hφ : LipschitzWith L φ)
    {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (h0 : ∀ r ∈ Icc α β, 0 ≤ φ r)
    (hWM : ∀ r ∈ Icc α β, r ^ a * φ r ≤ M) {σ : ℝ} (hσ : σ ^ 2 = 1) :
    (2 * σ * blissPrimitive a M (β ^ a * φ β) - a * (β ^ a * φ β) ^ 2) -
        (2 * σ * blissPrimitive a M (α ^ a * φ α) - a * (α ^ a * φ α) ^ 2) +
      a ^ 2 / M ^ (2 / a) * ∫ r in α..β, r ^ (2 * a + 1) * φ r ^ (2 + 2 / a) ≤
    ∫ r in α..β, r ^ (2 * a + 1) * deriv φ r ^ 2 := by
  set W : ℝ → ℝ := fun r ↦ r ^ a * φ r with hW
  set Ψσ : ℝ → ℝ := fun s ↦ 2 * σ * blissPrimitive a M s - a * s ^ 2 with hΨσ
  have hσabs : |σ| = 1 :=
    (pow_eq_one_iff_of_nonneg (abs_nonneg σ) two_ne_zero).mp (by rw [sq_abs]; exact hσ)
  -- `W` is absolutely continuous on `[α, β]`, with values in `[0, M]`
  have hWac : AbsolutelyContinuousOnInterval W α β :=
    ((Real.absolutelyContinuousOnInterval_rpow ha β).mono
      (uIcc_subset_uIcc (mem_uIcc_of_le hα hαβ) right_mem_uIcc)).mul
      hφ.lipschitzOnWith.absolutelyContinuousOnInterval
  have hWmem : MapsTo W (uIcc α β) (Icc 0 M) := fun r hr ↦ by
    rw [uIcc_of_le hαβ] at hr
    exact ⟨mul_nonneg (Real.rpow_nonneg (hα.trans hr.1) _) (h0 r hr), hWM r hr⟩
  -- `s ↦ 2σ Ψ(s) - a s²` has the derivative `2σ h(s) - 2 a s`, bounded on `[0, M]`
  have hΨd (s : ℝ) : HasDerivAt Ψσ (2 * σ * blissProfile a M s - a * (2 * s)) s := by
    have h2 : HasDerivAt (fun s : ℝ ↦ a * s ^ 2) (a * (2 * s)) s := by
      simpa using (hasDerivAt_pow 2 s).const_mul a
    exact ((hasDerivAt_blissPrimitive ha M s).const_mul (2 * σ)).sub h2
  have hbound : ∀ s ∈ Icc 0 M, ‖2 * σ * blissProfile a M s - a * (2 * s)‖ ≤ 4 * a * M := by
    intro s hs
    have h1 := abs_blissProfile_le ha hM hs.1 hs.2
    rw [Real.norm_eq_abs]
    calc |2 * σ * blissProfile a M s - a * (2 * s)|
        = |2 * σ * blissProfile a M s + -(a * (2 * s))| := by rw [sub_eq_add_neg]
      _ ≤ |2 * σ * blissProfile a M s| + |-(a * (2 * s))| := abs_add_le _ _
      _ = 2 * |blissProfile a M s| + a * (2 * s) := by
          rw [abs_neg, abs_mul, abs_mul, hσabs, abs_two, mul_one,
            abs_of_nonneg (mul_nonneg ha.le (mul_nonneg zero_le_two hs.1))]
      _ ≤ 2 * (a * M) + a * (2 * M) := by
          gcongr
          exact hs.2
      _ = 4 * a * M := by ring
  have hΨlip : LipschitzOnWith (Real.toNNReal (4 * a * M)) Ψσ (Icc 0 M) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
    rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, dist_eq_norm]
    exact (convex_Icc 0 M).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s _ ↦ (hΨd s).hasDerivWithinAt) hbound hy hx
  have hFac : AbsolutelyContinuousOnInterval (Ψσ ∘ W) α β :=
    hΨlip.comp_absolutelyContinuousOnInterval hWmem hWac
  -- integrability of the three terms
  have hf := continuous_rpow_mul_rpow (b := 2 * a + 1) (q := 2 + 2 / a) (by positivity)
    (by positivity) hφ.continuous
  have hg := intervalIntegrable_rpow_mul_deriv_sq hφ (b := 2 * a + 1) (by positivity) α β
  have hint1 : IntervalIntegrable (fun r ↦ deriv (Ψσ ∘ W) r +
      a ^ 2 / M ^ (2 / a) * (r ^ (2 * a + 1) * φ r ^ (2 + 2 / a))) volume α β :=
    hFac.intervalIntegrable_deriv.add ((hf.intervalIntegrable _ _).const_mul _)
  -- the pointwise inequality, almost everywhere
  have hae : ∀ᵐ r ∂volume.restrict (Icc α β), deriv (Ψσ ∘ W) r +
      a ^ 2 / M ^ (2 / a) * (r ^ (2 * a + 1) * φ r ^ (2 + 2 / a)) ≤
        r ^ (2 * a + 1) * deriv φ r ^ 2 := by
    filter_upwards [ae_restrict_of_ae hφ.ae_differentiableAt_real,
      ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ))]
      with r hd hr hr0
    have hrpos : 0 < r := lt_of_le_of_ne (hα.trans hr.1) hr0.symm
    have hWd : HasDerivAt W (a * r ^ (a - 1) * φ r + r ^ a * deriv φ r) r :=
      (Real.hasDerivAt_rpow_const (Or.inl hrpos.ne')).mul hd.hasDerivAt
    have hFd := (hΨd (W r)).comp r hWd
    rw [hFd.deriv, Real.rpow_sub_one hrpos.ne']
    have hX : 0 < r ^ a := Real.rpow_pos_of_pos hrpos a
    have hW0 : 0 ≤ r ^ a * φ r := mul_nonneg hX.le (h0 r hr)
    have hsq := blissProfile_sq ha hM hW0 (hWM r hr)
    have hpow : r ^ (2 * a + 1) = r * (r ^ a) ^ 2 := by
      rw [show 2 * a + 1 = a + a + 1 by ring, Real.rpow_add hrpos, Real.rpow_add hrpos,
        Real.rpow_one]
      ring
    have hWp : (r ^ a * φ r) ^ (2 + 2 / a) = r * (r * (r ^ a) ^ 2 * φ r ^ (2 + 2 / a)) := by
      rw [Real.mul_rpow hX.le (h0 r hr), ← Real.rpow_mul hrpos.le,
        show a * (2 + 2 / a) = a + a + 1 + 1 by field_simp; ring, Real.rpow_add hrpos,
        Real.rpow_add hrpos, Real.rpow_add hrpos, Real.rpow_one]
      ring
    rw [hpow]
    simp only [hW] at hsq ⊢
    -- names for the quantities: `X = r^a`, `D = φ'(r)`, `H = h(W)`, `P = φ^p`, `c = a²/M^{2/a}`
    generalize r ^ a = X at hX hsq hWp ⊢
    generalize deriv φ r = D
    generalize blissProfile a M (X * φ r) = H at hsq ⊢
    generalize φ r ^ (2 + 2 / a) = P at hWp ⊢
    generalize a ^ 2 / M ^ (2 / a) = c at hsq ⊢
    rw [hWp] at hsq
    have hD : r * X * D = r * (a * (X / r) * φ r + X * D) - a * X * φ r := by
      field_simp
      ring
    have key : r * (r * X ^ 2 * D ^ 2) - r * ((2 * σ * H - a * (2 * (X * φ r))) *
        (a * (X / r) * φ r + X * D) + c * (r * X ^ 2 * P)) =
        (r * (a * (X / r) * φ r + X * D) - σ * H) ^ 2 := by
      linear_combination (r * X * D + (r * (a * (X / r) * φ r + X * D) - a * X * φ r)) * hD +
        -hsq - H ^ 2 * hσ
    have hnn := sq_nonneg (r * (a * (X / r) * φ r + X * D) - σ * H)
    exact le_of_mul_le_mul_left (by linarith) hrpos
  -- integrate
  have hmono := intervalIntegral.integral_mono_ae_restrict hαβ hint1 hg hae
  rw [intervalIntegral.integral_add hFac.intervalIntegrable_deriv
    ((hf.intervalIntegrable _ _).const_mul _), intervalIntegral.integral_const_mul,
    hFac.integral_deriv_eq_sub] at hmono
  exact hmono

/-! ## The inequality -/

/-- **Bliss's inequality.** Let `a > 0`, `p = 2 + 2/a`, and let `φ` be a Lipschitz function on
the line with `φ ≥ 0` on `[0, R]` and `φ R = 0`. Then

`a (a + 1) (4κ)^{1/(a+1)} (∫₀^R r^{2a+1} φ^p dr)^{a/(a+1)} ≤ ∫₀^R r^{2a+1} φ'² dr`,

with `κ = blissKappa a`. For `a = (n - 2) / 2` this is the sharp Sobolev inequality for the
radial function `φ(|x|)` on `ℝⁿ`: the weight is `r^{n-1}`, `p = 2n / (n - 2)` and
`a / (a + 1) = 2 / p`. The proof applies `bliss_step` with the sign `+` up to a maximum point of
`W(r) = r^a φ(r)` and with the sign `-` after it, and removes the maximum `M` with the weighted
inequality between the arithmetic and the geometric mean. -/
theorem bliss_inequality (ha : 0 < a) {L : ℝ≥0} {R : ℝ} (hR0 : 0 ≤ R) {φ : ℝ → ℝ}
    (hφ : LipschitzWith L φ) (h0 : ∀ r ∈ Icc 0 R, 0 ≤ φ r) (hR : φ R = 0) :
    a * (a + 1) * (4 * blissKappa a) ^ (1 / (a + 1)) *
        (∫ r in (0 : ℝ)..R, r ^ (2 * a + 1) * φ r ^ (2 + 2 / a)) ^ (a / (a + 1)) ≤
      ∫ r in (0 : ℝ)..R, r ^ (2 * a + 1) * deriv φ r ^ 2 := by
  set N : ℝ := ∫ r in (0 : ℝ)..R, r ^ (2 * a + 1) * φ r ^ (2 + 2 / a) with hN
  set I : ℝ := ∫ r in (0 : ℝ)..R, r ^ (2 * a + 1) * deriv φ r ^ 2 with hI
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg hR0 fun r hr ↦
    mul_nonneg (Real.rpow_nonneg hr.1 _) (sq_nonneg _)
  have hN0 : 0 ≤ N := intervalIntegral.integral_nonneg hR0 fun r hr ↦
    mul_nonneg (Real.rpow_nonneg hr.1 _) (Real.rpow_nonneg (h0 r hr) _)
  have hWc : Continuous fun r : ℝ ↦ r ^ a * φ r :=
    (Real.continuous_rpow_const ha.le).mul hφ.continuous
  -- a maximum point `r₀` of `W(r) = r^a φ(r)` on `[0, R]`
  obtain ⟨r₀, hr₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hR0) hWc.continuousOn
  have hmax' : ∀ r ∈ Icc 0 R, r ^ a * φ r ≤ r₀ ^ a * φ r₀ := fun r hr ↦ isMaxOn_iff.mp hmax r hr
  have hM0 : 0 ≤ r₀ ^ a * φ r₀ := mul_nonneg (Real.rpow_nonneg hr₀.1 _) (h0 r₀ hr₀)
  rcases hM0.eq_or_lt with hMz | hMpos
  · -- `W` vanishes on `[0, R]`, so the left side is zero
    have hz : ∀ r ∈ uIcc 0 R, r ^ (2 * a + 1) * φ r ^ (2 + 2 / a) = 0 := by
      intro r hr
      rw [uIcc_of_le hR0] at hr
      have hWr : r ^ a * φ r = 0 := le_antisymm ((hmax' r hr).trans_eq hMz.symm)
        (mul_nonneg (Real.rpow_nonneg hr.1 _) (h0 r hr))
      rcases mul_eq_zero.mp hWr with h | h
      · have hr0 : r = 0 := by
          by_contra hne
          exact (Real.rpow_pos_of_pos (lt_of_le_of_ne hr.1 (Ne.symm hne)) a).ne' h
        rw [hr0, Real.zero_rpow (by positivity), zero_mul]
      · rw [h, Real.zero_rpow (by positivity), mul_zero]
    have hNz : N = 0 := by
      rw [hN, intervalIntegral.integral_congr hz, intervalIntegral.integral_zero]
    rw [hNz, Real.zero_rpow (by positivity), mul_zero]
    exact hI0
  · set M : ℝ := r₀ ^ a * φ r₀ with hM
    have hc := continuous_rpow_mul_rpow (b := 2 * a + 1) (q := 2 + 2 / a) (by positivity)
      (by positivity) hφ.continuous
    have hg := intervalIntegrable_rpow_mul_deriv_sq hφ (b := 2 * a + 1) (by positivity)
    -- the sign `+` on `[0, r₀]` and the sign `-` on `[r₀, R]`
    have s1 := bliss_step ha hMpos hφ (α := 0) (β := r₀) le_rfl hr₀.1
      (fun r hr ↦ h0 r ⟨hr.1, hr.2.trans hr₀.2⟩)
      (fun r hr ↦ hmax' r ⟨hr.1, hr.2.trans hr₀.2⟩) (σ := 1) (by norm_num)
    have s2 := bliss_step ha hMpos hφ (α := r₀) (β := R) hr₀.1 hr₀.2
      (fun r hr ↦ h0 r ⟨hr₀.1.trans hr.1, hr.2⟩)
      (fun r hr ↦ hmax' r ⟨hr₀.1.trans hr.1, hr.2⟩) (σ := -1) (by norm_num)
    simp only [← hM, Real.zero_rpow ha.ne', zero_mul, hR, mul_zero, blissPrimitive_zero,
      blissPrimitive_self hMpos] at s1 s2
    have hsum_f := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (μ := volume) 0 r₀) (hc.intervalIntegrable r₀ R)
    have hsum_g := intervalIntegral.integral_add_adjacent_intervals (hg 0 r₀) (hg r₀ R)
    have key : 4 * (a * M ^ 2 * blissKappa a) + a ^ 2 / M ^ (2 / a) * N ≤ I := by
      rw [hN, hI, ← hsum_f, ← hsum_g]
      linarith
    -- the weighted inequality of means removes `M`
    have hκ := blissKappa_nonneg a
    have hA : 0 < a * (a + 1) := by positivity
    have hMa : 0 < M ^ (2 / a) := Real.rpow_pos_of_pos hMpos _
    have hm : 0 < M ^ (2 / (a + 1)) := Real.rpow_pos_of_pos hMpos _
    have hAM := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 / (a + 1)) (w₂ := a / (a + 1))
      (p₁ := a * (a + 1) * (4 * blissKappa a) * M ^ 2) (p₂ := a * (a + 1) * N / M ^ (2 / a))
      (by positivity) (by positivity) (by positivity) (by positivity) (by field_simp; ring)
    have e1 : (a * (a + 1) * (4 * blissKappa a) * M ^ 2) ^ (1 / (a + 1)) =
        (a * (a + 1)) ^ (1 / (a + 1)) * (4 * blissKappa a) ^ (1 / (a + 1)) *
          M ^ (2 / (a + 1)) := by
      rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hA.le (by positivity),
        ← Real.rpow_natCast M 2, ← Real.rpow_mul hMpos.le,
        show ((2 : ℕ) : ℝ) * (1 / (a + 1)) = 2 / (a + 1) by push_cast; ring]
    have e2 : (a * (a + 1) * N / M ^ (2 / a)) ^ (a / (a + 1)) =
        (a * (a + 1)) ^ (a / (a + 1)) * N ^ (a / (a + 1)) / M ^ (2 / (a + 1)) := by
      rw [Real.div_rpow (by positivity) hMa.le, Real.mul_rpow hA.le hN0,
        ← Real.rpow_mul hMpos.le, show 2 / a * (a / (a + 1)) = 2 / (a + 1) by field_simp]
    have e3 : (a * (a + 1)) ^ (1 / (a + 1)) * (a * (a + 1)) ^ (a / (a + 1)) = a * (a + 1) := by
      rw [← Real.rpow_add hA, show 1 / (a + 1) + a / (a + 1) = 1 by field_simp; ring,
        Real.rpow_one]
    have e4 : 1 / (a + 1) * (a * (a + 1) * (4 * blissKappa a) * M ^ 2) +
        a / (a + 1) * (a * (a + 1) * N / M ^ (2 / a)) =
        4 * (a * M ^ 2 * blissKappa a) + a ^ 2 / M ^ (2 / a) * N := by
      field_simp
    have e5 : (a * (a + 1)) ^ (1 / (a + 1)) * (4 * blissKappa a) ^ (1 / (a + 1)) *
        M ^ (2 / (a + 1)) *
          ((a * (a + 1)) ^ (a / (a + 1)) * N ^ (a / (a + 1)) / M ^ (2 / (a + 1))) =
        (a * (a + 1)) ^ (1 / (a + 1)) * (a * (a + 1)) ^ (a / (a + 1)) *
          (4 * blissKappa a) ^ (1 / (a + 1)) * N ^ (a / (a + 1)) := by
      field_simp
    rw [e1, e2, e5, e3, e4] at hAM
    exact hAM.trans key

end SobolevSpace.Inequalities
