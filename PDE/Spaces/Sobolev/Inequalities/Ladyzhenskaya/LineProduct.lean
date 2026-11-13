/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Line bounds and the three-slice estimate

For a continuously differentiable compactly supported `φ : ℝ → ℝ`, the fundamental theorem of
calculus applied from both ends of the line gives `2 |φ(t)| ≤ ∫ |φ'|`; applied to `φ²` it gives
`φ(t)² ≤ ∫ |φ φ'|`. On every coordinate line, the square of a function is therefore bounded by
the integral of `|u ∂ᵢu|` along that line.

On a product `X × Y × Z` of s-finite measure spaces, these three line bounds alone imply
`(∫ g⁴)² ≤ (∫ g²) (∫ d₀²) (∫ d₁²) (∫ d₂²)`. This is Ladyzhenskaya's argument. On each slice
`{a} × Y × Z` the line bounds in the second and third directions bound `∫ g⁴` by the product of
the slice integrals of `g d₁` and `g d₂`. The line bound in the first direction bounds every
slice integral of `g²` by `∫ g d₀`, and Cauchy-Schwarz on the slices, in the first variable and
on the whole product closes the estimate. All integrals are lower Lebesgue integrals, so no
integrability hypothesis is needed.

## Main results

* `two_mul_enorm_le_lintegral_enorm_deriv`, `enorm_sq_le_lintegral_enorm_mul_enorm_deriv`: the
  line bounds.
* `lintegral_mul_sq_le`: Cauchy-Schwarz for lower Lebesgue integrals.
* `lintegral_pow_four_sq_le_of_lineBounds`: the three-slice estimate.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace SobolevSpace.Inequalities

/-- A compactly supported `C¹` function on the line is bounded by half the total variation:
`2 |f(x)| ≤ ∫ |f'|`, from the fundamental theorem of calculus on `(-∞, x]` and on `(x, ∞)`. -/
theorem two_mul_enorm_le_lintegral_enorm_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (x : ℝ) :
    2 * ‖f x‖ₑ ≤ ∫⁻ y, ‖deriv f y‖ₑ := by
  have hleft := hfc.enorm_le_lintegral_Ici_deriv hf x
  have hright : ‖f x‖ₑ ≤ ∫⁻ y in Ioi x, ‖deriv f y‖ₑ := by
    have hderiv : ∀ y ∈ Ioi x, HasDerivAt f (deriv f y) y := fun y _ ↦
      (hf.differentiable one_ne_zero y).hasDerivAt
    have hint : IntegrableOn (deriv f) (Ioi x) :=
      ((hf.continuous_deriv le_rfl).integrable_of_hasCompactSupport hfc.deriv).integrableOn
    have htend : Tendsto f atTop (𝓝 0) := by
      have h0 := hfc
      rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at h0
      exact (h0.filter_mono atTop_le_cocompact).tendsto
    have h := integral_Ioi_of_hasDerivAt_of_tendsto hf.continuous.continuousWithinAt hderiv
      hint htend
    calc ‖f x‖ₑ = ‖∫ y in Ioi x, deriv f y‖ₑ := by rw [h, zero_sub, enorm_neg]
      _ ≤ ∫⁻ y in Ioi x, ‖deriv f y‖ₑ := enorm_integral_le_lintegral_enorm _
  calc 2 * ‖f x‖ₑ = ‖f x‖ₑ + ‖f x‖ₑ := two_mul _
    _ ≤ (∫⁻ y in Iic x, ‖deriv f y‖ₑ) + ∫⁻ y in Ioi x, ‖deriv f y‖ₑ := add_le_add hleft hright
    _ = ∫⁻ y, ‖deriv f y‖ₑ := by rw [← compl_Iic, lintegral_add_compl _ measurableSet_Iic]

/-- The line bound for the square: `φ(x)² ≤ ∫ |φ φ'|` for a compactly supported `C¹`
function `φ` on the line. -/
theorem enorm_sq_le_lintegral_enorm_mul_enorm_deriv {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (x : ℝ) :
    ‖φ x‖ₑ ^ 2 ≤ ∫⁻ y, ‖φ y‖ₑ * ‖deriv φ y‖ₑ := by
  have hsq : ContDiff ℝ 1 (fun y ↦ φ y * φ y) := hφ.mul hφ
  have hsqc : HasCompactSupport (fun y ↦ φ y * φ y) := hφc.mul_left
  have hd (y : ℝ) : deriv (fun y ↦ φ y * φ y) y = 2 * (φ y * deriv φ y) := by
    have h := (hφ.differentiable one_ne_zero y).hasDerivAt
    have h2 : HasDerivAt (fun y ↦ φ y * φ y) (deriv φ y * φ y + φ y * deriv φ y) y :=
      h.mul h
    rw [h2.deriv]
    ring
  have h := two_mul_enorm_le_lintegral_enorm_deriv hsq hsqc x
  simp_rw [hd] at h
  have hint : ∫⁻ y, ‖2 * (φ y * deriv φ y)‖ₑ = 2 * ∫⁻ y, ‖φ y‖ₑ * ‖deriv φ y‖ₑ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
    refine lintegral_congr fun y ↦ ?_
    rw [enorm_mul, enorm_mul]
    congr 1
    rw [Real.enorm_eq_ofReal_abs]
    norm_num
  rw [hint, enorm_mul, ← sq] at h
  exact (ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top).mp h

/-- Cauchy-Schwarz for lower Lebesgue integrals: `(∫ f g)² ≤ (∫ f²) (∫ g²)`. -/
theorem lintegral_mul_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, f a * g a ∂μ) ^ 2 ≤ (∫⁻ a, f a ^ 2 ∂μ) * ∫⁻ a, g a ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  simp only [Pi.mul_apply, ENNReal.rpow_two] at h
  have hsq (t : ℝ≥0∞) : (t ^ (1 / 2 : ℝ)) ^ 2 = t := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  calc (∫⁻ a, f a * g a ∂μ) ^ 2
      ≤ ((∫⁻ a, f a ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ a, g a ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
    _ = (∫⁻ a, f a ^ 2 ∂μ) * ∫⁻ a, g a ^ 2 ∂μ := by rw [mul_pow, hsq, hsq]

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} {ρ : Measure Z} [SFinite μ] [SFinite ν] [SFinite ρ]

/-- The three-slice estimate. On `X × Y × Z`, let `g² ≤ ∫ g dᵢ` along every line in the `i`th
factor. Then `(∫ g⁴)² ≤ (∫ g²) (∫ d₀²) (∫ d₁²) (∫ d₂²)`. With `g = |u|` and `dᵢ = |∂ᵢu|` this
is Ladyzhenskaya's inequality `‖u‖₄⁴ ≤ ‖u‖₂ ‖∂₀u‖₂ ‖∂₁u‖₂ ‖∂₂u‖₂` in three dimensions. -/
theorem lintegral_pow_four_sq_le_of_lineBounds {g d₀ d₁ d₂ : X × Y × Z → ℝ≥0∞}
    (hg : Measurable g) (hd₀ : Measurable d₀) (hd₁ : Measurable d₁) (hd₂ : Measurable d₂)
    (h₀ : ∀ a q, g (a, q) ^ 2 ≤ ∫⁻ a', g (a', q) * d₀ (a', q) ∂μ)
    (h₁ : ∀ a b c, g (a, b, c) ^ 2 ≤ ∫⁻ b', g (a, b', c) * d₁ (a, b', c) ∂ν)
    (h₂ : ∀ a b c, g (a, b, c) ^ 2 ≤ ∫⁻ c', g (a, b, c') * d₂ (a, b, c') ∂ρ) :
    (∫⁻ p, g p ^ 4 ∂μ.prod (ν.prod ρ)) ^ 2 ≤
      (∫⁻ p, g p ^ 2 ∂μ.prod (ν.prod ρ)) * (∫⁻ p, d₀ p ^ 2 ∂μ.prod (ν.prod ρ)) *
        (∫⁻ p, d₁ p ^ 2 ∂μ.prod (ν.prod ρ)) * ∫⁻ p, d₂ p ^ 2 ∂μ.prod (ν.prod ρ) := by
  -- Slice quantities in the first variable.
  let S : X → ℝ≥0∞ := fun a ↦ ∫⁻ q, g (a, q) ^ 2 ∂ν.prod ρ
  let A₁ : X → ℝ≥0∞ := fun a ↦ ∫⁻ q, g (a, q) * d₁ (a, q) ∂ν.prod ρ
  let A₂ : X → ℝ≥0∞ := fun a ↦ ∫⁻ q, g (a, q) * d₂ (a, q) ∂ν.prod ρ
  let D₁ : X → ℝ≥0∞ := fun a ↦ ∫⁻ q, d₁ (a, q) ^ 2 ∂ν.prod ρ
  let D₂ : X → ℝ≥0∞ := fun a ↦ ∫⁻ q, d₂ (a, q) ^ 2 ∂ν.prod ρ
  let T : ℝ≥0∞ := ∫⁻ p, g p * d₀ p ∂μ.prod (ν.prod ρ)
  have hA₁m : Measurable A₁ := (hg.mul hd₁).lintegral_prod_right'
  have hA₂m : Measurable A₂ := (hg.mul hd₂).lintegral_prod_right'
  have hD₁m : Measurable D₁ := (hd₁.pow_const 2).lintegral_prod_right'
  have hD₂m : Measurable D₂ := (hd₂.pow_const 2).lintegral_prod_right'
  -- On each slice, the fourth power is controlled by the product of two slice integrals.
  have hslice (a : X) : ∫⁻ q, g (a, q) ^ 4 ∂ν.prod ρ ≤ A₁ a * A₂ a := by
    let K₁ : Z → ℝ≥0∞ := fun c ↦ ∫⁻ b', g (a, b', c) * d₁ (a, b', c) ∂ν
    let K₂ : Y → ℝ≥0∞ := fun b ↦ ∫⁻ c', g (a, b, c') * d₂ (a, b, c') ∂ρ
    have hF₁ : Measurable fun q : Y × Z ↦ g (a, q) * d₁ (a, q) :=
      (hg.mul hd₁).comp measurable_prodMk_left
    have hF₂ : Measurable fun q : Y × Z ↦ g (a, q) * d₂ (a, q) :=
      (hg.mul hd₂).comp measurable_prodMk_left
    have hK₁ : Measurable K₁ := hF₁.lintegral_prod_left'
    have hK₂ : Measurable K₂ := hF₂.lintegral_prod_right'
    have hswap : ∫⁻ c, K₁ c ∂ρ = A₁ a := by
      rw [lintegral_lintegral_swap (μ := ρ) (ν := ν)
        (f := fun c b' ↦ g (a, b', c) * d₁ (a, b', c)) (hF₁.comp measurable_swap).aemeasurable]
      exact (lintegral_prod _ hF₁.aemeasurable).symm
    calc ∫⁻ q, g (a, q) ^ 4 ∂ν.prod ρ = ∫⁻ b, ∫⁻ c, g (a, b, c) ^ 4 ∂ρ ∂ν :=
          lintegral_prod _ ((hg.comp measurable_prodMk_left).pow_const 4).aemeasurable
      _ ≤ ∫⁻ b, ∫⁻ c, K₂ b * K₁ c ∂ρ ∂ν := by
          refine lintegral_mono fun b ↦ lintegral_mono fun c ↦ ?_
          calc g (a, b, c) ^ 4 = g (a, b, c) ^ 2 * g (a, b, c) ^ 2 := by ring
            _ ≤ K₂ b * K₁ c := mul_le_mul' (h₂ a b c) (h₁ a b c)
      _ = ∫⁻ b, K₂ b * ∫⁻ c, K₁ c ∂ρ ∂ν :=
          lintegral_congr fun b ↦ lintegral_const_mul _ hK₁
      _ = (∫⁻ b, K₂ b ∂ν) * ∫⁻ c, K₁ c ∂ρ := lintegral_mul_const _ hK₂
      _ = A₂ a * A₁ a := by rw [hswap, ← lintegral_prod _ hF₂.aemeasurable]
      _ = A₁ a * A₂ a := mul_comm _ _
  -- Cauchy-Schwarz on each slice.
  have hA₁ (a : X) : A₁ a ^ 2 ≤ S a * D₁ a :=
    lintegral_mul_sq_le (hg.comp measurable_prodMk_left).aemeasurable
      (hd₁.comp measurable_prodMk_left).aemeasurable
  have hA₂ (a : X) : A₂ a ^ 2 ≤ S a * D₂ a :=
    lintegral_mul_sq_le (hg.comp measurable_prodMk_left).aemeasurable
      (hd₂.comp measurable_prodMk_left).aemeasurable
  -- The line bound in the first direction bounds every slice mass.
  have hS (a : X) : S a ≤ T := by
    calc S a ≤ ∫⁻ q, ∫⁻ a', g (a', q) * d₀ (a', q) ∂μ ∂ν.prod ρ :=
          lintegral_mono fun q ↦ h₀ a q
      _ = ∫⁻ a', ∫⁻ q, g (a', q) * d₀ (a', q) ∂ν.prod ρ ∂μ :=
          lintegral_lintegral_swap (μ := ν.prod ρ) (ν := μ)
            (f := fun q a' ↦ g (a', q) * d₀ (a', q))
            ((hg.mul hd₀).comp measurable_swap).aemeasurable
      _ = T := (lintegral_prod _ (hg.mul hd₀).aemeasurable).symm
  have hT : T ^ 2 ≤ (∫⁻ p, g p ^ 2 ∂μ.prod (ν.prod ρ)) * ∫⁻ p, d₀ p ^ 2 ∂μ.prod (ν.prod ρ) :=
    lintegral_mul_sq_le hg.aemeasurable hd₀.aemeasurable
  have hD₁ : ∫⁻ p, d₁ p ^ 2 ∂μ.prod (ν.prod ρ) = ∫⁻ a, D₁ a ∂μ :=
    lintegral_prod _ (hd₁.pow_const 2).aemeasurable
  have hD₂ : ∫⁻ p, d₂ p ^ 2 ∂μ.prod (ν.prod ρ) = ∫⁻ a, D₂ a ∂μ :=
    lintegral_prod _ (hd₂.pow_const 2).aemeasurable
  calc (∫⁻ p, g p ^ 4 ∂μ.prod (ν.prod ρ)) ^ 2
      = (∫⁻ a, ∫⁻ q, g (a, q) ^ 4 ∂ν.prod ρ ∂μ) ^ 2 := by
        rw [lintegral_prod _ (hg.pow_const 4).aemeasurable]
    _ ≤ (∫⁻ a, A₁ a * A₂ a ∂μ) ^ 2 := by
        gcongr with a
        exact hslice a
    _ ≤ (∫⁻ a, A₁ a ^ 2 ∂μ) * ∫⁻ a, A₂ a ^ 2 ∂μ :=
        lintegral_mul_sq_le hA₁m.aemeasurable hA₂m.aemeasurable
    _ ≤ (∫⁻ a, T * D₁ a ∂μ) * ∫⁻ a, T * D₂ a ∂μ := by
        gcongr with a a
        · exact (hA₁ a).trans (mul_le_mul_left (hS a) _)
        · exact (hA₂ a).trans (mul_le_mul_left (hS a) _)
    _ = T ^ 2 * (∫⁻ a, D₁ a ∂μ) * ∫⁻ a, D₂ a ∂μ := by
        rw [lintegral_const_mul _ hD₁m, lintegral_const_mul _ hD₂m]
        ring
    _ ≤ _ := by
        rw [← hD₁, ← hD₂]
        gcongr

end SobolevSpace.Inequalities
