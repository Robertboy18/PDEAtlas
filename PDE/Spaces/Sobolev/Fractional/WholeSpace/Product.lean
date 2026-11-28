/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Integration.Convolution.Young
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Lebesgue

/-!
# Products in Sobolev spaces of real order

For `σ ≥ 0` and `s > n/2`, the product of two functions in `L²(ℝⁿ)` satisfies the tame estimate
`E_σ(fg) ≤ 2 · 4^σ c (E_σ(f) E_s(g) + E_s(f) E_σ(g))`, with `c = wienerConst n s`, and for
`σ > n/2` the space `H^σ(ℝⁿ)` is an algebra: `E_σ(fg) ≤ 4^{σ+1} c E_σ(f) E_σ(g)`. A quadratic
term such as `u · ∇u` is estimated this way, and since the orders are real, a bootstrap can gain a
fraction of a derivative at each step. Nothing is assumed finite. The product
`h = f g` is an `L²` function given with the statement; `exists_ae_eq_mul` provides it when one
factor has finite energy of an order above `n/2`. At integer orders `k > n/2` the graph norms
have the algebra property too (`SobolevSpace.GraphSpace.multiplication`), proved with
derivatives. Not covered here: the product with a function that has bounded derivatives but lies
in no `H^s`, and the tame estimate with `‖f‖_∞` in place of `‖f̂‖₁`, which needs a paraproduct.

## Main results

* `coe_besselWeight_le_add`: `(1 + |ξ|²)^σ ≤ 4^σ ((1 + |ξ - η|²)^σ + (1 + |η|²)^σ)` for `σ ≥ 0`.
* `lintegral_besselWeight_mul_convolution_sq_le`: the weighted Young inequality, for `σ ≥ 0` and
  all measurable `F, G ≥ 0`.
* `besselEnergy_mul_le_of_integrable`: the tame estimate with the `L¹` norms of the transforms,
  `E_σ(fg) ≤ 2 · 4^σ (E_σ(f) ‖ĝ‖₁² + ‖f̂‖₁² E_σ(g))`.
* `besselEnergy_mul_le`, `besselEnergy_mul_le_mul`: the tame estimate and the algebra property.
* `exists_ae_eq_mul`: the product of a function of finite energy of order `s > n/2` with a
  function in `L²` is in `L²`.

## How it works

The transform of a product is the convolution of the transforms, so
`|(fg)^(ξ)| ≤ ∫ |f̂(ξ - η)| |ĝ(η)| dη` (`enorm_fourier_le_lintegral_of_ae_eq_mul`). The inequality
for the weight of a sum moves the square root of the weight onto one of the two factors, and
Young's inequality `‖F ⋆ G‖₂ ≤ ‖F‖₂ ‖G‖₁` bounds each of the two convolutions. This is the tame
estimate with `‖f̂‖₁²` and `‖ĝ‖₁²`, and by the Cauchy–Schwarz inequality both are at most `c E_s`
(`sq_lintegral_enorm_fourier_le`). A function in `H^s`, `s > n/2`, is bounded, so its product with
a function in `L²` is in `L²`.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley, 1999,
  for Young's inequality for convolutions and the Fourier transform of a convolution.
  <https://www.wiley.com/en-us/Real+Analysis%3A+Modern+Techniques+and+Their+Applications%2C+2nd+Edition-p-9780471317166>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter FourierTransform
open PDE.Analysis PDE.Analysis.Fourier
open scoped ENNReal NNReal

namespace SobolevSpace.Fractional

variable {n : ℕ}

/-! ## The weight of a sum -/

/-- **The weight of a sum**: `(1 + |ξ|²)^σ ≤ 4^σ ((1 + |ξ - η|²)^σ + (1 + |η|²)^σ)` for
`σ ≥ 0`. -/
theorem coe_besselWeight_le_add {σ : ℝ} (hσ : 0 ≤ σ) (ξ η : ℝ^n) :
    (besselWeight n σ ξ : ℝ≥0∞) ≤ ENNReal.ofReal (4 ^ σ) *
      ((besselWeight n σ (ξ - η) : ℝ≥0∞) + besselWeight n σ η) := by
  have ha : (0 : ℝ) < 1 + ‖ξ - η‖ ^ 2 := by positivity
  have hb : (0 : ℝ) < 1 + ‖η‖ ^ 2 := by positivity
  have hle : 1 + ‖ξ‖ ^ 2 ≤ 4 * max (1 + ‖ξ - η‖ ^ 2) (1 + ‖η‖ ^ 2) := by
    have h1 : ‖ξ‖ ≤ ‖ξ - η‖ + ‖η‖ := by simpa using norm_add_le (ξ - η) η
    have h2 : ‖ξ‖ ^ 2 ≤ (‖ξ - η‖ + ‖η‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 := le_max_left (1 + ‖ξ - η‖ ^ 2) (1 + ‖η‖ ^ 2)
    have h4 := le_max_right (1 + ‖ξ - η‖ ^ 2) (1 + ‖η‖ ^ 2)
    nlinarith [sq_nonneg (‖ξ - η‖ - ‖η‖)]
  have hpow : (1 + ‖ξ‖ ^ 2) ^ σ ≤
      4 ^ σ * ((1 + ‖ξ - η‖ ^ 2) ^ σ + (1 + ‖η‖ ^ 2) ^ σ) := by
    refine (Real.rpow_le_rpow (by positivity) hle hσ).trans ?_
    rw [Real.mul_rpow (by norm_num) (le_max_of_le_left ha.le)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rcases le_total (1 + ‖ξ - η‖ ^ 2) (1 + ‖η‖ ^ 2) with h | h
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left (Real.rpow_nonneg ha.le _)
    · rw [max_eq_left h]
      exact le_add_of_nonneg_right (Real.rpow_nonneg hb.le _)
  rw [coe_besselWeight, coe_besselWeight, coe_besselWeight,
    ← ENNReal.ofReal_add (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg hb.le _),
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hpow

/-- The weight of order `σ` is the square of the weight of order `σ / 2`. -/
theorem coe_besselWeight_half_sq (σ : ℝ) (ξ : ℝ^n) :
    (besselWeight n (σ / 2) ξ : ℝ≥0∞) ^ 2 = besselWeight n σ ξ := by
  rw [sq, ← ENNReal.coe_mul, ← besselWeight_add, add_halves]

/-! ## The weighted convolution inequality -/

/-- Young's inequality `‖F ⋆ G‖₂ ≤ ‖F‖₂ ‖G‖₁` on `ℝⁿ`, squared. -/
private theorem lintegral_convolution_sq_le_left {F G : ℝ^n → ℝ≥0∞} (hF : Measurable F)
    (hG : Measurable G) :
    ∫⁻ ξ, (∫⁻ η, F (ξ - η) * G η) ^ 2 ≤ (∫⁻ ξ, F ξ ^ 2) * (∫⁻ ξ, G ξ) ^ 2 := by
  have h := ENNReal.lintegral_convolution_rpow_le (volume : Measure (ℝ^n)) (p := 2) (q := 1)
    (r := 2) two_pos one_pos le_rfl one_le_two (by norm_num) hF hG
  simpa only [ENNReal.rpow_two, ENNReal.rpow_one, div_self (two_ne_zero' ℝ), div_one] using h

/-- Young's inequality `‖F ⋆ G‖₂ ≤ ‖F‖₁ ‖G‖₂` on `ℝⁿ`, squared. -/
private theorem lintegral_convolution_sq_le_right {F G : ℝ^n → ℝ≥0∞} (hF : Measurable F)
    (hG : Measurable G) :
    ∫⁻ ξ, (∫⁻ η, F (ξ - η) * G η) ^ 2 ≤ (∫⁻ ξ, F ξ) ^ 2 * ∫⁻ ξ, G ξ ^ 2 := by
  have h := ENNReal.lintegral_convolution_rpow_le (volume : Measure (ℝ^n)) (p := 1) (q := 2)
    (r := 2) one_pos two_pos one_le_two le_rfl (by norm_num) hF hG
  simpa only [ENNReal.rpow_two, ENNReal.rpow_one, div_self (two_ne_zero' ℝ), div_one] using h

/-- **The weighted Young inequality.** For `σ ≥ 0` and measurable `F, G ≥ 0` on `ℝⁿ`,

`∫ (1 + |ξ|²)^σ (F ⋆ G)² ≤ 2 · 4^σ ((∫ (1 + |ξ|²)^σ F²) (∫ G)² + (∫ F)² ∫ (1 + |ξ|²)^σ G²)`.

The inequality for the weight of a sum puts its square root on one of the two factors, and Young's
inequality bounds each of the two convolutions. -/
theorem lintegral_besselWeight_mul_convolution_sq_le {σ : ℝ} (hσ : 0 ≤ σ) {F G : ℝ^n → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable G) :
    ∫⁻ ξ, (besselWeight n σ ξ : ℝ≥0∞) * (∫⁻ η, F (ξ - η) * G η) ^ 2 ≤
      2 * ENNReal.ofReal (4 ^ σ) *
        ((∫⁻ ξ, (besselWeight n σ ξ : ℝ≥0∞) * F ξ ^ 2) * (∫⁻ ξ, G ξ) ^ 2 +
          (∫⁻ ξ, F ξ) ^ 2 * ∫⁻ ξ, (besselWeight n σ ξ : ℝ≥0∞) * G ξ ^ 2) := by
  -- the square root of the weight
  set v : ℝ^n → ℝ≥0∞ := fun ξ ↦ (besselWeight n (σ / 2) ξ : ℝ≥0∞) with hv
  have hvm : Measurable v := measurable_coe_nnreal_ennreal.comp (measurable_besselWeight _)
  have hvF : Measurable fun ξ ↦ v ξ * F ξ := hvm.mul hF
  have hvG : Measurable fun ξ ↦ v ξ * G ξ := hvm.mul hG
  have hk2 : ENNReal.ofReal (4 ^ (σ / 2)) ^ 2 = ENNReal.ofReal (4 ^ σ) := by
    rw [← ENNReal.ofReal_pow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 2
    push_cast
    ring
  -- the root of the weight moves onto one of the two factors
  have hpt (ξ : ℝ^n) : v ξ * ∫⁻ η, F (ξ - η) * G η ≤ ENNReal.ofReal (4 ^ (σ / 2)) *
      ((∫⁻ η, (v (ξ - η) * F (ξ - η)) * G η) + ∫⁻ η, F (ξ - η) * (v η * G η)) := by
    have hFs : Measurable fun η ↦ F (ξ - η) := hF.comp (measurable_const.sub measurable_id)
    have hvFs : Measurable fun η ↦ v (ξ - η) * F (ξ - η) :=
      hvF.comp (measurable_const.sub measurable_id)
    have hm₁ : Measurable fun η ↦ (v (ξ - η) * F (ξ - η)) * G η := hvFs.mul hG
    have hm₂ : Measurable fun η ↦ F (ξ - η) * (v η * G η) := hFs.mul hvG
    have hm : Measurable fun η ↦ (v (ξ - η) * F (ξ - η)) * G η + F (ξ - η) * (v η * G η) :=
      hm₁.add hm₂
    calc v ξ * ∫⁻ η, F (ξ - η) * G η = ∫⁻ η, v ξ * (F (ξ - η) * G η) :=
          (lintegral_const_mul _ (hFs.mul hG)).symm
      _ ≤ ∫⁻ η, ENNReal.ofReal (4 ^ (σ / 2)) *
            ((v (ξ - η) * F (ξ - η)) * G η + F (ξ - η) * (v η * G η)) := by
          refine lintegral_mono fun η ↦ ?_
          calc v ξ * (F (ξ - η) * G η)
              ≤ ENNReal.ofReal (4 ^ (σ / 2)) * (v (ξ - η) + v η) * (F (ξ - η) * G η) :=
                mul_le_mul' (coe_besselWeight_le_add (by positivity) ξ η) le_rfl
            _ = _ := by ring
      _ = _ := by rw [lintegral_const_mul _ hm, lintegral_add_left hm₁]
  -- the pointwise bound, squared
  have hsq (ξ : ℝ^n) : (besselWeight n σ ξ : ℝ≥0∞) * (∫⁻ η, F (ξ - η) * G η) ^ 2 ≤
      2 * ENNReal.ofReal (4 ^ σ) * ((∫⁻ η, (v (ξ - η) * F (ξ - η)) * G η) ^ 2 +
        (∫⁻ η, F (ξ - η) * (v η * G η)) ^ 2) := by
    rw [← coe_besselWeight_half_sq, ← mul_pow]
    refine (pow_le_pow_left₀ zero_le (hpt ξ) 2).trans ?_
    rw [mul_pow, hk2, mul_comm 2, mul_assoc]
    -- `(a + b)² ≤ 2 (a² + b²)` in `[0, ∞]`: the mean inequality for the exponent `2`
    have add_sq (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
      have h := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 2) one_le_two
      rwa [ENNReal.rpow_two, ENNReal.rpow_two, ENNReal.rpow_two,
        show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] at h
    exact mul_le_mul' le_rfl (add_sq _ _)
  have hkernel₁ : Measurable fun z : ℝ^n × ℝ^n ↦ (v (z.1 - z.2) * F (z.1 - z.2)) * G z.2 :=
    (hvF.comp (measurable_fst.sub measurable_snd)).mul (hG.comp measurable_snd)
  have hkernel₂ : Measurable fun z : ℝ^n × ℝ^n ↦ F (z.1 - z.2) * (v z.2 * G z.2) :=
    (hF.comp (measurable_fst.sub measurable_snd)).mul (hvG.comp measurable_snd)
  have hA : Measurable fun ξ ↦ (∫⁻ η, (v (ξ - η) * F (ξ - η)) * G η) ^ 2 :=
    hkernel₁.lintegral_prod_right.pow_const 2
  have hB : Measurable fun ξ ↦ (∫⁻ η, F (ξ - η) * (v η * G η)) ^ 2 :=
    hkernel₂.lintegral_prod_right.pow_const 2
  have hAB : Measurable fun ξ ↦ (∫⁻ η, (v (ξ - η) * F (ξ - η)) * G η) ^ 2 +
      (∫⁻ η, F (ξ - η) * (v η * G η)) ^ 2 := hA.add hB
  have hw (H : ℝ^n → ℝ≥0∞) :
      ∫⁻ ξ, (v ξ * H ξ) ^ 2 = ∫⁻ ξ, (besselWeight n σ ξ : ℝ≥0∞) * H ξ ^ 2 :=
    lintegral_congr fun ξ ↦ by rw [mul_pow, coe_besselWeight_half_sq]
  calc ∫⁻ ξ, (besselWeight n σ ξ : ℝ≥0∞) * (∫⁻ η, F (ξ - η) * G η) ^ 2
      ≤ ∫⁻ ξ, 2 * ENNReal.ofReal (4 ^ σ) * ((∫⁻ η, (v (ξ - η) * F (ξ - η)) * G η) ^ 2 +
          (∫⁻ η, F (ξ - η) * (v η * G η)) ^ 2) := lintegral_mono hsq
    _ = 2 * ENNReal.ofReal (4 ^ σ) * ((∫⁻ ξ, (∫⁻ η, (v (ξ - η) * F (ξ - η)) * G η) ^ 2) +
          ∫⁻ ξ, (∫⁻ η, F (ξ - η) * (v η * G η)) ^ 2) := by
        rw [lintegral_const_mul _ hAB, lintegral_add_left hA]
    _ ≤ _ := by
        refine mul_le_mul' le_rfl (add_le_add ?_ ?_)
        · exact (lintegral_convolution_sq_le_left hvF hG).trans_eq (by rw [hw])
        · exact (lintegral_convolution_sq_le_right hF hvG).trans_eq (by rw [hw])

/-! ## The tame product estimate -/

/-- **The tame product estimate on the Fourier side.** Let `σ ≥ 0`, let `f`, `g`, `h` be in
`L²(ℝⁿ)` with `h = f g` almost everywhere, and let `f̂` and `ĝ` be integrable. Then

`E_σ(h) ≤ 2 · 4^σ (E_σ(f) ‖ĝ‖₁² + ‖f̂‖₁² E_σ(g))`.

Each term has the full order on one factor only. -/
theorem besselEnergy_mul_le_of_integrable {σ : ℝ} (hσ : 0 ≤ σ)
    (f g h : Lp ℂ 2 (volume : Measure (ℝ^n)))
    (hf : Integrable (𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))))
    (hg : Integrable (𝓕 g : Lp ℂ 2 (volume : Measure (ℝ^n))))
    (hh : (h : ℝ^n → ℂ) =ᵐ[volume] fun x ↦ f x * g x) :
    besselEnergy σ (fun _ : Unit ↦ h) ≤ 2 * ENNReal.ofReal (4 ^ σ) *
      (besselEnergy σ (fun _ : Unit ↦ f) *
          (∫⁻ ξ, ‖(𝓕 g : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ) ^ 2 +
        (∫⁻ ξ, ‖(𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ) ^ 2 *
          besselEnergy σ (fun _ : Unit ↦ g)) := by
  have hF : Measurable fun ξ ↦ ‖(𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ :=
    (Lp.stronglyMeasurable _).eNorm
  have hG : Measurable fun ξ ↦ ‖(𝓕 g : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ :=
    (Lp.stronglyMeasurable _).eNorm
  simp only [besselEnergy_unit_eq_lintegral]
  refine le_trans (lintegral_mono_ae ?_)
    (lintegral_besselWeight_mul_convolution_sq_le hσ hF hG)
  filter_upwards [enorm_fourier_le_lintegral_of_ae_eq_mul f g h hf hg hh] with ξ hξ
  exact mul_le_mul' le_rfl (pow_le_pow_left₀ zero_le hξ 2)

/-! ## The algebra property -/

/-- If one factor is zero, a product in `L²` is zero. -/
private theorem eq_zero_of_ae_eq_mul {f g h : Lp ℂ 2 (volume : Measure (ℝ^n))}
    (hh : (h : ℝ^n → ℂ) =ᵐ[volume] fun x ↦ f x * g x) (h0 : f = 0 ∨ g = 0) : h = 0 := by
  refine Lp.ext ?_
  rcases h0 with rfl | rfl
  · filter_upwards [hh, Lp.coeFn_zero ℂ 2 (volume : Measure (ℝ^n))] with x hx h0x
    rw [hx, h0x, Pi.zero_apply, zero_mul]
  · filter_upwards [hh, Lp.coeFn_zero ℂ 2 (volume : Measure (ℝ^n))] with x hx h0x
    rw [hx, h0x, Pi.zero_apply, mul_zero]

/-- **The tame product estimate.** Let `σ ≥ 0` and `s > n/2`, and let `f`, `g`, `h` be in
`L²(ℝⁿ)` with `h = f g` almost everywhere. Then

`E_σ(h) ≤ 2 · 4^σ c (E_σ(f) E_s(g) + E_s(f) E_σ(g))`, `c = wienerConst n s`.

Nothing is assumed finite: if a factor is not in `H^s` and the other is not zero, the right side
is infinite. -/
theorem besselEnergy_mul_le {σ s : ℝ} (hσ : 0 ≤ σ) (hs : (n : ℝ) < 2 * s)
    (f g h : Lp ℂ 2 (volume : Measure (ℝ^n)))
    (hh : (h : ℝ^n → ℂ) =ᵐ[volume] fun x ↦ f x * g x) :
    besselEnergy σ (fun _ : Unit ↦ h) ≤ 2 * ENNReal.ofReal (4 ^ σ) * wienerConst n s *
      (besselEnergy σ (fun _ : Unit ↦ f) * besselEnergy s (fun _ : Unit ↦ g) +
        besselEnergy s (fun _ : Unit ↦ f) * besselEnergy σ (fun _ : Unit ↦ g)) := by
  -- a zero factor
  by_cases h0 : f = 0 ∨ g = 0
  · rw [eq_zero_of_ae_eq_mul hh h0, besselEnergy_fun_zero]
    exact zero_le
  rw [not_or] at h0
  have hEf : besselEnergy σ (fun _ : Unit ↦ f) ≠ 0 := fun hz ↦
    h0.1 (congrFun (besselEnergy_eq_zero_iff.1 hz) ())
  have hEg : besselEnergy σ (fun _ : Unit ↦ g) ≠ 0 := fun hz ↦
    h0.2 (congrFun (besselEnergy_eq_zero_iff.1 hz) ())
  have hc : 2 * ENNReal.ofReal (4 ^ σ) * wienerConst n s ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (ENNReal.ofReal_pos.2 (by positivity)).ne')
      (wienerConst_ne_zero n s)
  -- a factor of infinite energy of order `s`
  by_cases hf : besselEnergy s (fun _ : Unit ↦ f) < ⊤
  swap
  · rw [not_lt, top_le_iff] at hf
    rw [hf, ENNReal.top_mul hEg, add_top, ENNReal.mul_top hc]
    exact le_top
  by_cases hg : besselEnergy s (fun _ : Unit ↦ g) < ⊤
  swap
  · rw [not_lt, top_le_iff] at hg
    rw [hg, ENNReal.mul_top hEf, top_add, ENNReal.mul_top hc]
    exact le_top
  refine (besselEnergy_mul_le_of_integrable hσ f g h
    (integrable_fourier_of_besselEnergy_lt_top hs f hf)
    (integrable_fourier_of_besselEnergy_lt_top hs g hg) hh).trans ?_
  calc _ ≤ 2 * ENNReal.ofReal (4 ^ σ) * (besselEnergy σ (fun _ : Unit ↦ f) *
          (wienerConst n s * besselEnergy s (fun _ : Unit ↦ g)) +
        wienerConst n s * besselEnergy s (fun _ : Unit ↦ f) *
          besselEnergy σ (fun _ : Unit ↦ g)) :=
        mul_le_mul' le_rfl (add_le_add
          (mul_le_mul' le_rfl (sq_lintegral_enorm_fourier_le s g))
          (mul_le_mul' (sq_lintegral_enorm_fourier_le s f) le_rfl))
    _ = _ := by ring

/-- **`H^σ(ℝⁿ)` is an algebra for `σ > n/2`.** If `f`, `g`, `h` are in `L²(ℝⁿ)` and `h = f g`
almost everywhere, then

`E_σ(h) ≤ 4^{σ+1} c E_σ(f) E_σ(g)`, `c = wienerConst n σ`,

that is `‖fg‖_{H^σ} ≤ 2^{σ+1} √c ‖f‖_{H^σ} ‖g‖_{H^σ}`. Nothing is assumed finite. -/
theorem besselEnergy_mul_le_mul {σ : ℝ} (hσ : (n : ℝ) < 2 * σ)
    (f g h : Lp ℂ 2 (volume : Measure (ℝ^n)))
    (hh : (h : ℝ^n → ℂ) =ᵐ[volume] fun x ↦ f x * g x) :
    besselEnergy σ (fun _ : Unit ↦ h) ≤ ENNReal.ofReal (4 ^ (σ + 1)) * wienerConst n σ *
      (besselEnergy σ (fun _ : Unit ↦ f) * besselEnergy σ (fun _ : Unit ↦ g)) := by
  have hσ0 : 0 ≤ σ := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  refine (besselEnergy_mul_le hσ0 hσ f g h hh).trans_eq ?_
  have h4 : ENNReal.ofReal (4 ^ (σ + 1)) = 4 * ENNReal.ofReal (4 ^ σ) := by
    rw [Real.rpow_add_one (by norm_num), mul_comm, ENNReal.ofReal_mul (by norm_num)]
    norm_num
  rw [h4, ← two_mul]
  ring

/-! ## Products in `L²` -/

/-- **The product of a function of finite energy of order `s > n/2` with a function in `L²` is
in `L²`**: there is `h ∈ L²(ℝⁿ)` equal to `f g` almost everywhere. The first factor is bounded
by the integral of its transform (`ae_norm_le_integral_norm_fourier`), so the product estimates
of this module apply to `h`. -/
theorem exists_ae_eq_mul {s : ℝ} (hs : (n : ℝ) < 2 * s)
    (f g : Lp ℂ 2 (volume : Measure (ℝ^n))) (hf : besselEnergy s (fun _ : Unit ↦ f) < ⊤) :
    ∃ h : Lp ℂ 2 (volume : Measure (ℝ^n)), (h : ℝ^n → ℂ) =ᵐ[volume] fun x ↦ f x * g x := by
  have hint := integrable_fourier_of_besselEnergy_lt_top hs f hf
  have hmem : MemLp (fun x ↦ f x * g x) 2 (volume : Measure (ℝ^n)) := by
    refine (Lp.memLp g).of_le_mul (c := ∫ ξ, ‖(𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖)
      ((Lp.aestronglyMeasurable f).mul (Lp.aestronglyMeasurable g)) ?_
    filter_upwards [ae_norm_le_integral_norm_fourier f hint] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  exact ⟨hmem.toLp _, hmem.coeFn_toLp⟩

end SobolevSpace.Fractional
