/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import PDE.Analysis.Fourier.DoubleRiesz
public import PDE.Analysis.Fourier.IntegrableTransform
public import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Agmon's inequality in three dimensions

A square-integrable function `u` on `ℝ³` whose weak gradient and weak Laplacian are square
integrable is bounded, with `‖u‖_∞² ≤ ‖∇u‖₂ ‖Δu‖₂ / (2π)`. This is Agmon's inequality. The proof
is on the Fourier side and needs nothing about `û` beyond the two weighted energies, with no
splitting into low and high frequencies. The same argument gives
`‖u‖_∞ ≲ ‖∇ᵏu‖^θ ‖∇ᵐu‖^(1-θ)` in dimension `n` whenever `k < n/2 < m`; only `n = 3`, `k = 1`,
`m = 2` is proved here. The form for `C²` functions is in `PDE.Analysis.Fourier.AgmonContDiff`,
and the inequality on an annulus is built on that.

## Main results

* `integral_inv_norm_sq_add_norm_pow_four`: on every real inner product space of dimension
  three and for all `a, b > 0`, `∫ dξ / (a |ξ|² + b |ξ|⁴) = 2π² / √(ab)`.
* `integrable_and_integral_norm_le_two_pi_mul_sqrt`: for every measurable `g` on such a space,
  `‖g‖₁ ≤ 2π √(P Q)` when `‖ |ξ| g ‖₂ ≤ P` and `‖ |ξ|² g ‖₂ ≤ Q`.
* `ae_norm_le_of_fourier_moments`: the same bound for `|u|` almost everywhere, for every
  `u ∈ L²` with values in a complex Hilbert space, with `g = û`.
* `ae_norm_sq_le_of_hasComplexWeakDerivativeOn`: Agmon's inequality
  `|u|² ≤ ‖∇u‖ ‖Δu‖ / (2π)` almost everywhere, for every `u ∈ L²(ℝ³; ℂ)` with weak first
  derivatives and weak pure second derivatives in `L²`.
* `sum_norm_sq_le_of_hasComplexWeakDerivativeOn`: `‖∇u‖² ≤ ‖u‖ ‖Δu‖` for such `u` on `ℝⁿ`, in
  every dimension.

## How it works

The supremum of `u` is at most the `L¹` norm of `û` (`ae_norm_le_integral_norm_fourier`). With
the weight `w(ξ) = a |ξ|² + b |ξ|⁴`, the pointwise inequality `2x ≤ w x² + 1/w` bounds `‖û‖₁` by
half of `a ∫ |ξ|² |û|² + b ∫ |ξ|⁴ |û|² + ∫ dξ / w`. The weight `1/w` is integrable exactly
because the dimension is three: in polar coordinates
`∫ dξ / w = 4π ∫₀^∞ dr / (a + b r²) = 2π² / √(ab)`, and the last integral is Mathlib's
`∫₀^∞ ds / (1 + s²) = π / 2` after the substitution `s = √(b / a) r`. Choosing `a` and `b` to
balance the two energies gives the constant. A weak derivative `∂ᵢ` multiplies `û` by
`2πi ξᵢ`, and the weak Laplacian multiplies it by `-4π² |ξ|²`
(`fourier_sum_ae_of_hasComplexWeakDerivativeOn`), so by Plancherel the two energies are
`‖∇u‖² / (2π)²` and `‖Δu‖² / (2π)⁴`. The gradient bound is the Cauchy-Schwarz inequality for
`|û|` and `|ξ|² |û|`, read off the sign of the quadratic `t ↦ ∫ (t - |ξ|²)² |û|²`.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform Set Real

namespace PDE.Analysis.Fourier

/-! ## The radial integral -/

private theorem inv_add_mul_sq_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (y : ℝ) :
    (a + b * y ^ 2)⁻¹ = a⁻¹ * (1 + (√(b / a) * y) ^ 2)⁻¹ := by
  rw [mul_pow, Real.sq_sqrt (div_pos hb ha).le, ← mul_inv]
  congr 1
  field_simp

section Space

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The unit ball of a three-dimensional real inner product space has volume `4π/3`. -/
theorem volume_real_ball_zero_one_of_finrank_eq_three (hE : Module.finrank ℝ E = 3) :
    (volume : Measure E).real (Metric.ball 0 1) = 4 * π / 3 := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hΓ : Real.Gamma (((3 : ℕ) : ℝ) / 2 + 1) = 3 / 4 * √π := by
    rw [show (((3 : ℕ) : ℝ) / 2 + 1) = (1 / 2 + 1) + 1 by norm_num,
      Real.Gamma_add_one (by norm_num), Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    ring
  have hπ : √π ^ 3 = π * √π := by
    rw [pow_succ, Real.sq_sqrt Real.pi_pos.le]
  rw [measureReal_def, InnerProductSpace.volume_ball, hE, hΓ, ENNReal.ofReal_one, one_pow,
    one_mul, ENNReal.toReal_ofReal (by positivity), hπ]
  field_simp

/-- In dimension three the weight `1 / (a |ξ|² + b |ξ|⁴)` is integrable: it is `O(|ξ|⁻²)` at the
origin and `O(|ξ|⁻⁴)` at infinity. -/
theorem integrable_inv_norm_sq_add_norm_pow_four (hE : Module.finrank ℝ E = 3) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun ξ : E ↦ (a * ‖ξ‖ ^ 2 + b * ‖ξ‖ ^ 4)⁻¹) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  refine (integrable_fun_norm_addHaar volume
    (f := fun r : ℝ ↦ (a * r ^ 2 + b * r ^ 4)⁻¹)).2 ?_
  have hc : √(b / a) ≠ 0 := (Real.sqrt_pos.2 (div_pos hb ha)).ne'
  have hint : IntegrableOn (fun y : ℝ ↦ (a + b * y ^ 2)⁻¹) (Ioi 0) := by
    simp_rw [inv_add_mul_sq_eq ha hb]
    exact ((integrable_inv_one_add_sq.comp_mul_left' hc).const_mul a⁻¹).integrableOn
  refine hint.congr_fun (fun y hy ↦ ?_) measurableSet_Ioi
  have hy0 : y ≠ 0 := (mem_Ioi.1 hy).ne'
  simp only [hE, smul_eq_mul]
  rw [show a * y ^ 2 + b * y ^ 4 = y ^ 2 * (a + b * y ^ 2) by ring, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ hy0), one_mul]

/-- The polar-coordinate integral that makes Agmon's inequality three-dimensional:
`∫ dξ / (a |ξ|² + b |ξ|⁴) = 2π² / √(ab)`. -/
theorem integral_inv_norm_sq_add_norm_pow_four (hE : Module.finrank ℝ E = 3) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    ∫ ξ : E, (a * ‖ξ‖ ^ 2 + b * ‖ξ‖ ^ 4)⁻¹ = 2 * π ^ 2 / √(a * b) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  -- the radial integral: substitute `s = √(b / a) y` in Mathlib's `∫₀^∞ ds / (1 + s²) = π / 2`
  have hrad : ∫ y in Ioi (0 : ℝ), y ^ (3 - 1) • (a * y ^ 2 + b * y ^ 4)⁻¹ =
      π / (2 * √(a * b)) := by
    set c : ℝ := √(b / a)
    have hc0 : 0 < c := Real.sqrt_pos.2 (div_pos hb ha)
    have hc2 : c ^ 2 = b / a := Real.sq_sqrt (div_pos hb ha).le
    have hac : √(a * b) = a * c := by
      rw [Real.sqrt_eq_iff_mul_self_eq (mul_pos ha hb).le (mul_pos ha hc0).le]
      have h : a * c * (a * c) = a ^ 2 * c ^ 2 := by ring
      rw [h, hc2]
      field_simp
    have h1 : ∫ y in Ioi (0 : ℝ), (1 + (c * y) ^ 2)⁻¹ = c⁻¹ * (π / 2) := by
      have h := integral_comp_mul_left_Ioi (fun s : ℝ ↦ (1 + s ^ 2)⁻¹) 0 hc0
      rw [mul_zero, integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero] at h
      simpa using h
    calc ∫ y in Ioi (0 : ℝ), y ^ (3 - 1) • (a * y ^ 2 + b * y ^ 4)⁻¹
        = ∫ y in Ioi (0 : ℝ), a⁻¹ * (1 + (c * y) ^ 2)⁻¹ := by
          refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
          have hy0 : y ≠ 0 := (mem_Ioi.1 hy).ne'
          simp only [smul_eq_mul]
          rw [mul_pow, hc2]
          field_simp
      _ = a⁻¹ * (c⁻¹ * (π / 2)) := by rw [integral_const_mul, h1]
      _ = π / (2 * √(a * b)) := by
          rw [hac]
          field_simp
  have hab : 0 < √(a * b) := Real.sqrt_pos.2 (mul_pos ha hb)
  rw [integral_fun_norm_addHaar volume (fun r : ℝ ↦ (a * r ^ 2 + b * r ^ 4)⁻¹), hE, hrad,
    volume_real_ball_zero_one_of_finrank_eq_three hE]
  simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat]
  field_simp
  ring

private theorem ae_ne_zero_of_finrank_eq_three (hE : Module.finrank ℝ E = 3) :
    ∀ᵐ ξ : E, ξ ≠ 0 := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : E))] with ξ hξ using hξ

variable {F : Type*} [NormedAddCommGroup F]

/-- A function whose weighted energy `∫ |ξ|^k |g|²` vanishes is zero almost everywhere. -/
private theorem ae_eq_zero_of_integral_norm_pow_mul_le_zero (hE : Module.finrank ℝ E = 3)
    {g : E → F} {k : ℕ} (hk : Integrable (fun ξ ↦ ‖ξ‖ ^ k * ‖g ξ‖ ^ 2))
    (h0 : ∫ ξ, ‖ξ‖ ^ k * ‖g ξ‖ ^ 2 ≤ 0) : g =ᵐ[volume] 0 := by
  have hnonneg : 0 ≤ᵐ[volume] fun ξ : E ↦ ‖ξ‖ ^ k * ‖g ξ‖ ^ 2 :=
    Filter.Eventually.of_forall fun ξ ↦ by positivity
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnonneg hk).1
    (le_antisymm h0 (integral_nonneg_of_ae hnonneg))
  filter_upwards [hzero, ae_ne_zero_of_finrank_eq_three hE] with ξ hξ hξ0
  have hpos : 0 < ‖ξ‖ ^ k := pow_pos (norm_pos_iff.2 hξ0) k
  simpa [hpos.ne'] using hξ

/-- The weighted Cauchy–Schwarz step with free weights. If `|ξ| g` and `|ξ|² g` are square
integrable on a three-dimensional space, then `g` is integrable and, for all `a, b > 0`,
`∫ |g| ≤ (a ∫ |ξ|² |g|² + b ∫ |ξ|⁴ |g|²) / 2 + π² / √(ab)`. -/
theorem integrable_and_integral_norm_le_of_moments (hE : Module.finrank ℝ E = 3) {g : E → F}
    (hg : AEStronglyMeasurable g volume)
    (h2 : Integrable (fun ξ ↦ ‖ξ‖ ^ 2 * ‖g ξ‖ ^ 2))
    (h4 : Integrable (fun ξ ↦ ‖ξ‖ ^ 4 * ‖g ξ‖ ^ 2)) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable g ∧ ∫ ξ, ‖g ξ‖ ≤
      (a * (∫ ξ, ‖ξ‖ ^ 2 * ‖g ξ‖ ^ 2) + b * (∫ ξ, ‖ξ‖ ^ 4 * ‖g ξ‖ ^ 2)) / 2 +
        π ^ 2 / √(a * b) := by
  have hW := integrable_inv_norm_sq_add_norm_pow_four hE ha hb
  have h24 : Integrable (fun ξ : E ↦ a * (‖ξ‖ ^ 2 * ‖g ξ‖ ^ 2) + b * (‖ξ‖ ^ 4 * ‖g ξ‖ ^ 2)) :=
    (h2.const_mul a).add (h4.const_mul b)
  have hmaj : Integrable (fun ξ : E ↦ (a * (‖ξ‖ ^ 2 * ‖g ξ‖ ^ 2) + b * (‖ξ‖ ^ 4 * ‖g ξ‖ ^ 2) +
      (a * ‖ξ‖ ^ 2 + b * ‖ξ‖ ^ 4)⁻¹) / 2) :=
    (h24.add hW).div_const 2
  -- pointwise, `2 x ≤ w x² + 1/w` for `w > 0`
  have hle : ∀ᵐ ξ : E, ‖g ξ‖ ≤ (a * (‖ξ‖ ^ 2 * ‖g ξ‖ ^ 2) + b * (‖ξ‖ ^ 4 * ‖g ξ‖ ^ 2) +
      (a * ‖ξ‖ ^ 2 + b * ‖ξ‖ ^ 4)⁻¹) / 2 := by
    filter_upwards [ae_ne_zero_of_finrank_eq_three hE] with ξ hξ
    have hw : 0 < a * ‖ξ‖ ^ 2 + b * ‖ξ‖ ^ 4 := by
      have := norm_pos_iff.2 hξ
      positivity
    have hsq := mul_nonneg hw.le (sq_nonneg (‖g ξ‖ - (a * ‖ξ‖ ^ 2 + b * ‖ξ‖ ^ 4)⁻¹))
    have hinv := mul_inv_cancel₀ hw.ne'
    generalize (a * ‖ξ‖ ^ 2 + b * ‖ξ‖ ^ 4)⁻¹ = v at hsq hinv ⊢
    have hexp : (a * ‖ξ‖ ^ 2 + b * ‖ξ‖ ^ 4) * (‖g ξ‖ - v) ^ 2 =
        a * (‖ξ‖ ^ 2 * ‖g ξ‖ ^ 2) + b * (‖ξ‖ ^ 4 * ‖g ξ‖ ^ 2) - 2 * ‖g ξ‖ + v := by
      linear_combination (v - 2 * ‖g ξ‖) * hinv
    linarith
  have hint : Integrable g := hmaj.mono' hg hle
  refine ⟨hint, (integral_mono_ae hint.norm hmaj hle).trans_eq ?_⟩
  rw [integral_div, integral_add h24 hW, integral_add (h2.const_mul a) (h4.const_mul b),
    integral_const_mul, integral_const_mul, integral_inv_norm_sq_add_norm_pow_four hE ha hb]
  ring

/-- **Agmon's inequality, the `L¹` form.** On a three-dimensional space, if `‖ |ξ| g ‖₂ ≤ P` and
`‖ |ξ|² g ‖₂ ≤ Q`, then `g` is integrable and `‖g‖₁ ≤ 2π √(P Q)`. This is
`integrable_and_integral_norm_le_of_moments` with the weights that balance the two energies. -/
theorem integrable_and_integral_norm_le_two_pi_mul_sqrt (hE : Module.finrank ℝ E = 3)
    {g : E → F} (hg : AEStronglyMeasurable g volume)
    (h2 : Integrable (fun ξ ↦ ‖ξ‖ ^ 2 * ‖g ξ‖ ^ 2))
    (h4 : Integrable (fun ξ ↦ ‖ξ‖ ^ 4 * ‖g ξ‖ ^ 2)) {P Q : ℝ} (hP0 : 0 ≤ P) (hQ0 : 0 ≤ Q)
    (hP : ∫ ξ, ‖ξ‖ ^ 2 * ‖g ξ‖ ^ 2 ≤ P ^ 2) (hQ : ∫ ξ, ‖ξ‖ ^ 4 * ‖g ξ‖ ^ 2 ≤ Q ^ 2) :
    Integrable g ∧ ∫ ξ, ‖g ξ‖ ≤ 2 * π * √(P * Q) := by
  have hint := (integrable_and_integral_norm_le_of_moments hE hg h2 h4 one_pos one_pos).1
  refine ⟨hint, ?_⟩
  have hzero : g =ᵐ[volume] 0 → ∫ ξ, ‖g ξ‖ ≤ 2 * π * √(P * Q) := fun h ↦ by
    have h0 : ∫ ξ, ‖g ξ‖ = 0 := by
      rw [← integral_zero E ℝ]
      exact integral_congr_ae (h.mono fun ξ hξ ↦ by simp [hξ])
    rw [h0]
    positivity
  rcases hP0.eq_or_lt with rfl | hPpos
  · exact hzero (ae_eq_zero_of_integral_norm_pow_mul_le_zero hE h2 (by simpa using hP))
  rcases hQ0.eq_or_lt with rfl | hQpos
  · exact hzero (ae_eq_zero_of_integral_norm_pow_mul_le_zero hE h4 (by simpa using hQ))
  -- the balanced weights `a = s / P²`, `b = s / Q²` with `s = π √(P Q)`
  have hs : 0 < π * √(P * Q) := mul_pos pi_pos (Real.sqrt_pos.2 (mul_pos hPpos hQpos))
  have hs2 : (π * √(P * Q)) ^ 2 = π ^ 2 * (P * Q) := by
    rw [mul_pow, Real.sq_sqrt (mul_pos hPpos hQpos).le]
  have ha : 0 < π * √(P * Q) / P ^ 2 := by positivity
  have hb : 0 < π * √(P * Q) / Q ^ 2 := by positivity
  have hroot : √(π * √(P * Q) / P ^ 2 * (π * √(P * Q) / Q ^ 2)) = π * √(P * Q) / (P * Q) := by
    rw [show π * √(P * Q) / P ^ 2 * (π * √(P * Q) / Q ^ 2) = (π * √(P * Q) / (P * Q)) ^ 2 by
      field_simp, Real.sqrt_sq (by positivity)]
  have hbound := (integrable_and_integral_norm_le_of_moments hE hg h2 h4 ha hb).2
  rw [hroot] at hbound
  have h1 : π * √(P * Q) / P ^ 2 * ∫ ξ, ‖ξ‖ ^ 2 * ‖g ξ‖ ^ 2 ≤ π * √(P * Q) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left hP hs.le
  have h2' : π * √(P * Q) / Q ^ 2 * ∫ ξ, ‖ξ‖ ^ 4 * ‖g ξ‖ ^ 2 ≤ π * √(P * Q) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left hQ hs.le
  have h3 : π ^ 2 / (π * √(P * Q) / (P * Q)) = π * √(P * Q) := by
    rw [div_div_eq_mul_div, div_eq_iff hs.ne', ← sq, hs2]
  rw [h3] at hbound
  linarith

end Space

section Hilbert

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Agmon's inequality on the Fourier side.** Let `u ∈ L²` on a three-dimensional space, with
values in a complex Hilbert space. If `‖ |ξ| û ‖₂ ≤ P` and `‖ |ξ|² û ‖₂ ≤ Q`, then
`|u| ≤ 2π √(P Q)` almost everywhere: `û` is integrable by
`integrable_and_integral_norm_le_two_pi_mul_sqrt`, and `u` is bounded by its `L¹` norm. -/
theorem ae_norm_le_of_fourier_moments (hE : Module.finrank ℝ E = 3)
    (u : Lp F 2 (volume : Measure E)) {P Q : ℝ} (hP0 : 0 ≤ P) (hQ0 : 0 ≤ Q)
    (h2 : Integrable (fun ξ ↦ ‖ξ‖ ^ 2 * ‖(𝓕 u : Lp F 2 (volume : Measure E)) ξ‖ ^ 2))
    (h4 : Integrable (fun ξ ↦ ‖ξ‖ ^ 4 * ‖(𝓕 u : Lp F 2 (volume : Measure E)) ξ‖ ^ 2))
    (hP : ∫ ξ, ‖ξ‖ ^ 2 * ‖(𝓕 u : Lp F 2 (volume : Measure E)) ξ‖ ^ 2 ≤ P ^ 2)
    (hQ : ∫ ξ, ‖ξ‖ ^ 4 * ‖(𝓕 u : Lp F 2 (volume : Measure E)) ξ‖ ^ 2 ≤ Q ^ 2) :
    ∀ᵐ x, ‖u x‖ ≤ 2 * π * √(P * Q) := by
  obtain ⟨hint, hle⟩ := integrable_and_integral_norm_le_two_pi_mul_sqrt hE
    (Lp.aestronglyMeasurable (𝓕 u)) h2 h4 hP0 hQ0 hP hQ
  filter_upwards [ae_norm_le_integral_norm_fourier u hint] with x hx
  exact hx.trans hle

end Hilbert

/-! ## Agmon's inequality for weak derivatives on `ℝ³` -/

/-- The Fourier multiplier of a derivative word of length one. -/
theorem prod_single_apply {n : ℕ} (c : ℂ) (ξ : ℝ^n) (i : Fin n) :
    (∏ m : Fin [i].length, c * (ξ ([i].get m) : ℂ)) = c * ξ i := by
  change ∏ m : Fin 1, c * (ξ ([i].get m) : ℂ) = _
  rw [Fin.prod_univ_one]
  rfl

/-- If `V̂ = m û` almost everywhere, then `|m|² |û|²` is integrable with integral `‖V‖²`
(Plancherel). -/
private theorem integrable_and_integral_mul_fourier_sq {n : ℕ}
    (u V : Lp ℂ 2 (volume : Measure (ℝ^n))) (m : ℝ^n → ℂ)
    (h : (fun ξ ↦ m ξ * (𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ) =ᵐ[volume]
      (𝓕 V : Lp ℂ 2 (volume : Measure (ℝ^n)))) :
    Integrable (fun ξ ↦ ‖m ξ‖ ^ 2 * ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ ^ 2) ∧
      ∫ ξ, ‖m ξ‖ ^ 2 * ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ ^ 2 = ‖V‖ ^ 2 := by
  have hfun : (fun ξ ↦ ‖(𝓕 V : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ ^ 2) =ᵐ[volume]
      fun ξ ↦ ‖m ξ‖ ^ 2 * ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ ^ 2 := by
    filter_upwards [h] with ξ hξ
    rw [← hξ, norm_mul, mul_pow]
  refine ⟨(Lp.memLp (𝓕 V)).norm.integrable_sq.congr hfun, ?_⟩
  rw [← integral_congr_ae hfun, ← Lp.norm_sq_eq_integral_norm_sq, Lp.norm_fourier_eq]

/-- **The two energies on the Fourier side.** Let `u ∈ L²(ℝⁿ; ℂ)` have weak first derivatives
`d i` and weak pure second derivatives `l k` in `L²`. Then `|ξ|² |û|²` and `|ξ|⁴ |û|²` are
integrable, with `∫ |ξ|² |û|² = ‖∇u‖² / (2π)²` and `∫ |ξ|⁴ |û|² = ‖Δu‖² / (2π)⁴`, where
`‖∇u‖² = ∑ ‖d i‖²` and `Δu = ∑ l k`. -/
theorem integral_norm_pow_mul_fourier_sq_of_hasComplexWeakDerivativeOn {n : ℕ}
    (u : Lp ℂ 2 (volume : Measure (ℝ^n))) (d l : Fin n → Lp ℂ 2 (volume : Measure (ℝ^n)))
    (hd : ∀ i, SobolevSpace.HasComplexWeakDerivativeOn univ [i] u (d i))
    (hl : ∀ k, SobolevSpace.HasComplexWeakDerivativeOn univ [k, k] u (l k)) :
    (Integrable (fun ξ : ℝ^n ↦ ‖ξ‖ ^ 2 * ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ ^ 2) ∧
      ∫ ξ : ℝ^n, ‖ξ‖ ^ 2 * ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ ^ 2 =
        (√(∑ i, ‖d i‖ ^ 2) / (2 * π)) ^ 2) ∧
    (Integrable (fun ξ : ℝ^n ↦ ‖ξ‖ ^ 4 * ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ ^ 2) ∧
      ∫ ξ : ℝ^n, ‖ξ‖ ^ 4 * ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ ^ 2 =
        (‖∑ k, l k‖ / (2 * π) ^ 2) ^ 2) := by
  have hπ : (0 : ℝ) < 2 * π := by positivity
  -- the gradient energy on the Fourier side
  have hgrad (i : Fin n) := integrable_and_integral_mul_fourier_sq u (d i)
    (fun ξ ↦ 2 * π * Complex.I * (ξ i : ℂ)) (by
      simpa only [prod_single_apply] using
        (SobolevSpace.hasComplexWeakDerivativeOn_iff_fourier [i] u (d i)).1 (hd i))
  have hnorm (ξ : ℝ^n) (i : Fin n) :
      ‖2 * π * Complex.I * (ξ i : ℂ)‖ ^ 2 = (2 * π) ^ 2 * ξ i ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, mul_pow,
      Real.norm_eq_abs, sq_abs, show ‖(2 * π : ℂ)‖ = 2 * π by
        rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.norm_real,
          Real.norm_of_nonneg hπ.le]]
  have hsum (ξ : ℝ^n) : ‖ξ‖ ^ 2 * ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ ^ 2 =
      ((2 * π) ^ 2)⁻¹ * ∑ i, ‖2 * π * Complex.I * (ξ i : ℂ)‖ ^ 2 *
        ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ ^ 2 := by
    simp only [hnorm, ← Finset.sum_mul, ← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq]
    field_simp
  have h2 : Integrable (fun ξ : ℝ^n ↦ ‖ξ‖ ^ 2 *
      ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ ^ 2) := by
    simp_rw [hsum]
    exact (integrable_finsetSum _ fun i _ ↦ (hgrad i).1).const_mul _
  have hP : ∫ ξ : ℝ^n, ‖ξ‖ ^ 2 * ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ ^ 2 =
      (√(∑ i, ‖d i‖ ^ 2) / (2 * π)) ^ 2 := by
    simp_rw [hsum]
    rw [integral_const_mul, integral_finsetSum _ fun i _ ↦ (hgrad i).1, div_pow,
      Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)]
    simp_rw [fun i ↦ (hgrad i).2]
    rw [inv_mul_eq_div]
  -- the Laplacian energy on the Fourier side
  have hlap := integrable_and_integral_mul_fourier_sq u (∑ k, l k)
    (fun ξ ↦ -((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ))
    (fourier_sum_ae_of_hasComplexWeakDerivativeOn u l hl).symm
  have hnorm4 (ξ : ℝ^n) : ‖-((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ)‖ ^ 2 = (2 * π) ^ 4 * ‖ξ‖ ^ 4 := by
    rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    ring
  have hsum4 (ξ : ℝ^n) : ‖ξ‖ ^ 4 * ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ ^ 2 =
      ((2 * π) ^ 4)⁻¹ * (‖-((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ)‖ ^ 2 *
        ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ ^ 2) := by
    rw [hnorm4]
    field_simp
  have h4 : Integrable (fun ξ : ℝ^n ↦ ‖ξ‖ ^ 4 *
      ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ ^ 2) := by
    simp_rw [hsum4]
    exact hlap.1.const_mul _
  have hQ : ∫ ξ : ℝ^n, ‖ξ‖ ^ 4 * ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ ^ 2 =
      (‖∑ k, l k‖ / (2 * π) ^ 2) ^ 2 := by
    simp_rw [hsum4]
    rw [integral_const_mul, hlap.2, div_pow, inv_mul_eq_div, ← pow_mul]
  exact ⟨⟨h2, hP⟩, h4, hQ⟩

/-- **The gradient is controlled by the function and its Laplacian.** Let `u ∈ L²(ℝⁿ; ℂ)` have
weak first derivatives `d i` and weak pure second derivatives `l k` in `L²`. Then
`‖∇u‖² ≤ ‖u‖ ‖Δu‖`, where `‖∇u‖² = ∑ ‖d i‖²` and `Δu = ∑ l k`. On the Fourier side this is the
Cauchy-Schwarz inequality for `|û|` and `|ξ|² |û|`; it is proved from the sign of the quadratic
`t ↦ ∫ (t - |ξ|²)² |û|²`. -/
theorem sum_norm_sq_le_of_hasComplexWeakDerivativeOn {n : ℕ}
    (u : Lp ℂ 2 (volume : Measure (ℝ^n))) (d l : Fin n → Lp ℂ 2 (volume : Measure (ℝ^n)))
    (hd : ∀ i, SobolevSpace.HasComplexWeakDerivativeOn univ [i] u (d i))
    (hl : ∀ k, SobolevSpace.HasComplexWeakDerivativeOn univ [k, k] u (l k)) :
    ∑ i, ‖d i‖ ^ 2 ≤ ‖u‖ * ‖∑ k, l k‖ := by
  obtain ⟨⟨h2, hP⟩, h4, hQ⟩ :=
    integral_norm_pow_mul_fourier_sq_of_hasComplexWeakDerivativeOn u d l hd hl
  have hS0 : 0 ≤ ∑ i, ‖d i‖ ^ 2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  rw [div_pow, Real.sq_sqrt hS0] at hP
  have h0 : Integrable (fun ξ : ℝ^n ↦ ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ ^ 2) :=
    (Lp.memLp (𝓕 u)).norm.integrable_sq
  have hB : ∫ ξ : ℝ^n, ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [← Lp.norm_sq_eq_integral_norm_sq, Lp.norm_fourier_eq]
  have hquad (t : ℝ) : 0 ≤ ‖u‖ ^ 2 * (t * t) +
      -2 * ((∑ i, ‖d i‖ ^ 2) / (2 * π) ^ 2) * t + (‖∑ k, l k‖ / (2 * π) ^ 2) ^ 2 := by
    have e0 : (fun ξ : ℝ^n ↦ (t - ‖ξ‖ ^ 2) ^ 2 *
        ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ ^ 2) = fun ξ ↦
          (t * t * ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ ^ 2 -
            2 * t * (‖ξ‖ ^ 2 * ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ ^ 2)) +
            ‖ξ‖ ^ 4 * ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ ^ 2 := by
      funext ξ
      ring
    have e1 := integral_add ((h0.const_mul (t * t)).sub (h2.const_mul (2 * t))) h4
    have e2 := integral_sub (h0.const_mul (t * t)) (h2.const_mul (2 * t))
    have hint : ∫ ξ : ℝ^n, (t - ‖ξ‖ ^ 2) ^ 2 *
        ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ ^ 2 = ‖u‖ ^ 2 * (t * t) +
          -2 * ((∑ i, ‖d i‖ ^ 2) / (2 * π) ^ 2) * t + (‖∑ k, l k‖ / (2 * π) ^ 2) ^ 2 := by
      rw [e0]
      refine (e1.trans (congrArg (fun z ↦ z + ∫ ξ : ℝ^n, ‖ξ‖ ^ 4 *
        ‖(𝓕 u : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ ^ 2) e2)).trans ?_
      rw [integral_const_mul, integral_const_mul, hB, hP, hQ]
      ring
    rw [← hint]
    exact integral_nonneg fun ξ ↦ by positivity
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  have hπ : (0 : ℝ) < (2 * π) ^ 2 := by positivity
  have hkey : (∑ i, ‖d i‖ ^ 2) ^ 2 ≤ (‖u‖ * ‖∑ k, l k‖) ^ 2 := by
    have h1 : ((∑ i, ‖d i‖ ^ 2) / (2 * π) ^ 2) ^ 2 ≤
        ‖u‖ ^ 2 * (‖∑ k, l k‖ / (2 * π) ^ 2) ^ 2 := by nlinarith
    rw [div_pow, div_pow, ← mul_div_assoc, div_le_div_iff_of_pos_right (by positivity)] at h1
    rw [mul_pow]
    exact h1
  exact (pow_le_pow_iff_left₀ hS0 (by positivity) two_ne_zero).1 hkey

/-- **Agmon's inequality on `ℝ³`.** Let `u ∈ L²(ℝ³; ℂ)` have weak first derivatives `d i` and
weak pure second derivatives `l k` in `L²`. Then, almost everywhere,
`|u|² ≤ ‖∇u‖ ‖Δu‖ / (2π)`, where `‖∇u‖² = ∑ ‖d i‖²` and `Δu = ∑ l k`. The proof reads the two
energies on the Fourier side and applies `ae_norm_le_of_fourier_moments`. -/
theorem ae_norm_sq_le_of_hasComplexWeakDerivativeOn (u : Lp ℂ 2 (volume : Measure (ℝ^3)))
    (d l : Fin 3 → Lp ℂ 2 (volume : Measure (ℝ^3)))
    (hd : ∀ i, SobolevSpace.HasComplexWeakDerivativeOn univ [i] u (d i))
    (hl : ∀ k, SobolevSpace.HasComplexWeakDerivativeOn univ [k, k] u (l k)) :
    ∀ᵐ x, ‖u x‖ ^ 2 ≤ √(∑ i, ‖d i‖ ^ 2) * ‖∑ k, l k‖ / (2 * π) := by
  have hπ : (0 : ℝ) < 2 * π := by positivity
  obtain ⟨⟨h2, hP⟩, h4, hQ⟩ :=
    integral_norm_pow_mul_fourier_sq_of_hasComplexWeakDerivativeOn u d l hd hl
  have hfin : Module.finrank ℝ (ℝ^3) = 3 := by simp
  filter_upwards [ae_norm_le_of_fourier_moments hfin u (P := √(∑ i, ‖d i‖ ^ 2) / (2 * π))
    (Q := ‖∑ k, l k‖ / (2 * π) ^ 2) (by positivity) (by positivity) h2 h4 hP.le hQ.le]
    with x hx
  have hPQ : 0 ≤ √(∑ i, ‖d i‖ ^ 2) / (2 * π) * (‖∑ k, l k‖ / (2 * π) ^ 2) := by positivity
  calc ‖u x‖ ^ 2 ≤ (2 * π * √(√(∑ i, ‖d i‖ ^ 2) / (2 * π) * (‖∑ k, l k‖ / (2 * π) ^ 2))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hx 2
    _ = √(∑ i, ‖d i‖ ^ 2) * ‖∑ k, l k‖ / (2 * π) := by
        rw [mul_pow, Real.sq_sqrt hPQ]
        field_simp

end PDE.Analysis.Fourier
