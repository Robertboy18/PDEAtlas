/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import PDE.Analysis.MeasureTheory.Lp.IntermediateExponent
public import PDE.Analysis.Fourier.IntegrableTransform
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Energy

/-!
# Sobolev functions above the critical order are bounded and lie in every `L^q`

For `s > n/2`, a function `f ∈ L²(ℝⁿ)` of finite energy `E_s(f)` has an integrable Fourier
transform, is bounded, and lies in every `L^q` with `2 ≤ q ≤ ∞`, with explicit constants:
`‖f‖_∞ ≤ √c ‖f‖_{H^s}` and `‖f‖_q ≤ (1 + √c) ‖f‖_{H^s}`, where `c = ∫ (1 + |ξ|²)^{-s} dξ` is
`wienerConst n s`. This is how a bound in `H^s` becomes an integrability statement, and the bound
of `‖f̂‖₁` is the input of the product estimates `SobolevSpace.Fractional.besselEnergy_mul_le`.
For an element of the real space `H^s` with `s > n/2 + 1`, `HsSpaceReal.c1RepresentativeCLM`
gives the `C¹` representative as a bounded operator; the bounds here are for the energy and carry
the constant. The embedding below the critical order,
`H^s ⊂ L^q` for `s < n/2` and `1/q = 1/2 - s/n`, is not proved here; it needs the
Hardy–Littlewood–Sobolev inequality or a Littlewood–Paley argument.

## Main results

* `wienerConst`, `wienerConst_lt_top`: the constant `c`, finite for `s > n/2`.
* `sq_lintegral_enorm_fourier_le`: `‖f̂‖₁² ≤ c E_s(f)` for every real `s` and every `f ∈ L²`.
* `integrable_fourier_of_besselEnergy_lt_top`: `f̂` is integrable when `s > n/2` and `E_s(f) < ∞`.
* `ae_enorm_sq_le`, `eLpNorm_top_le`: for `s > n/2`, `|f|² ≤ c E_s(f)` almost everywhere, so
  `‖f‖_∞ ≤ √c ‖f‖_{H^s}`.
* `eLpNorm_le_of_two_le`: `‖f‖_q ≤ (1 + √c) ‖f‖_{H^s}` for `s > n/2` and `2 ≤ q ≤ ∞`.

## How it works

By the Cauchy–Schwarz inequality on the Fourier side,
`‖f̂‖₁² ≤ (∫ (1 + |ξ|²)^{-s} dξ) (∫ (1 + |ξ|²)^s |f̂|² dξ)`, and the first integral is finite for
`2s > n`. A function in `L²` with an integrable transform is bounded by `‖f̂‖₁`
(`PDE.Analysis.Fourier.ae_norm_le_integral_norm_fourier`). Between `L²` and `L^∞`, every `L^q`
norm is at most the sum of the two (`MeasureTheory.eLpNorm_le_eLpNorm_add_eLpNorm_top`).

## References

* C. Morosi and L. Pizzocchero, "On the constants for some Sobolev imbeddings",
  *J. Inequal. Appl.* 6 (2001), no. 6, 665-679, numbering of arXiv:math/0011141v1,
  Propositions 2.1 and 3.1, (2.4). <https://arxiv.org/abs/math/0011141v1>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter FourierTransform
open PDE.Analysis PDE.Analysis.Fourier
open scoped ENNReal NNReal

namespace SobolevSpace.Fractional

variable {n : ℕ}

/-! ## Integrable transforms -/

/-- The constant `∫ (1 + |ξ|²)^{-s} dξ` over `ℝⁿ`, finite for `s > n/2`. It is the constant `c`
of `‖f̂‖₁² ≤ c E_s(f)` (`sq_lintegral_enorm_fourier_le`). -/
def wienerConst (n : ℕ) (s : ℝ) : ℝ≥0∞ := ∫⁻ ξ : ℝ^n, (besselWeight n (-s) ξ : ℝ≥0∞)

/-- The constant is finite for `s > n/2`. -/
theorem wienerConst_lt_top {s : ℝ} (hs : (n : ℝ) < 2 * s) : wienerConst n s < ⊤ := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ^n) (μ := volume) (r := 2 * s)
    (by simpa using hs)
  have he : (fun ξ : ℝ^n ↦ (1 + ‖ξ‖ ^ 2) ^ (-(2 * s) / 2)) = fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (-s) := by
    funext ξ
    congr 1
    ring
  rw [he] at h
  simpa only [wienerConst, coe_besselWeight] using h.lintegral_lt_top

/-- The constant is not zero. -/
theorem wienerConst_ne_zero (n : ℕ) (s : ℝ) : wienerConst n s ≠ 0 := by
  have hm : Measurable fun ξ : ℝ^n ↦ (besselWeight n (-s) ξ : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp (measurable_besselWeight _)
  refine ((lintegral_pos_iff_support hm).2 ?_).ne'
  have hsupp : Function.support (fun ξ : ℝ^n ↦ (besselWeight n (-s) ξ : ℝ≥0∞)) = univ := by
    refine eq_univ_of_forall fun ξ ↦ ?_
    rw [Function.mem_support, coe_besselWeight]
    exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos (by positivity) _)).ne'
  rw [hsupp]
  exact isOpen_univ.measure_pos volume univ_nonempty

/-- **The `L¹` norm of the transform is controlled by the energy**: for every real `s`,
`‖f̂‖₁² ≤ wienerConst n s · E_s(f)`. This is the Cauchy–Schwarz inequality; it has content for
`s > n/2`, where the constant is finite. -/
theorem sq_lintegral_enorm_fourier_le (s : ℝ) (f : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    (∫⁻ ξ, ‖(𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ) ^ 2 ≤
      wienerConst n s * besselEnergy s (fun _ : Unit ↦ f) := by
  -- Hölder with the exponents `2`, `2` for `(1 + |ξ|²)^{-s/2}` and `(1 + |ξ|²)^{s/2} |f̂|`
  have hA : Measurable fun ξ : ℝ^n ↦ (besselWeight n (-s / 2) ξ : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp (measurable_besselWeight _)
  have hB : Measurable fun ξ : ℝ^n ↦ (besselWeight n (s / 2) ξ : ℝ≥0∞) *
      ‖(𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ :=
    (measurable_coe_nnreal_ennreal.comp (measurable_besselWeight _)).mul
      (Lp.stronglyMeasurable _).eNorm
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure (ℝ^n))
    Real.HolderConjugate.two_two hA.aemeasurable hB.aemeasurable
  have e1 (ξ : ℝ^n) : (besselWeight n (-s / 2) ξ : ℝ≥0∞) * ((besselWeight n (s / 2) ξ : ℝ≥0∞) *
      ‖(𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ) =
        ‖(𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ := by
    rw [← mul_assoc, ← ENNReal.coe_mul, ← besselWeight_add, neg_div, neg_add_cancel,
      coe_besselWeight_zero, one_mul]
  have e2 (ξ : ℝ^n) : (besselWeight n (-s / 2) ξ : ℝ≥0∞) ^ (2 : ℝ) = besselWeight n (-s) ξ := by
    rw [coe_besselWeight_rpow, div_mul_cancel₀ _ (two_ne_zero' ℝ)]
  have e3 (ξ : ℝ^n) : ((besselWeight n (s / 2) ξ : ℝ≥0∞) *
      ‖(𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ) ^ (2 : ℝ) =
        besselWeight n s ξ * ‖(𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ ^ 2 := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), coe_besselWeight_rpow, ENNReal.rpow_two,
      div_mul_cancel₀ _ (two_ne_zero' ℝ)]
  simp only [Pi.mul_apply, e1, e2, e3] at h
  rw [wienerConst, besselEnergy_unit_eq_lintegral]
  refine (pow_le_pow_left₀ zero_le h 2).trans_eq ?_
  rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul]
  norm_num

/-- **A function of finite energy of order `s > n/2` has an integrable transform**:
`∫ |f̂| ≤ (c E_s(f))^{1/2} < ∞` with `c = wienerConst n s`, by the Cauchy–Schwarz inequality
against the weight `(1 + |ξ|²)^{-s}`, which is integrable for `2s > n`. This is what makes `f`
bounded (`ae_enorm_sq_le`), and it is the hypothesis of the product estimates. -/
theorem integrable_fourier_of_besselEnergy_lt_top {s : ℝ} (hs : (n : ℝ) < 2 * s)
    (f : Lp ℂ 2 (volume : Measure (ℝ^n))) (hf : besselEnergy s (fun _ : Unit ↦ f) < ⊤) :
    Integrable (𝓕 f : Lp ℂ 2 (volume : Measure (ℝ^n))) := by
  refine ⟨Lp.aestronglyMeasurable _, ?_⟩
  have h := (sq_lintegral_enorm_fourier_le s f).trans_lt
    (ENNReal.mul_lt_top (wienerConst_lt_top hs) hf)
  by_contra hcon
  rw [HasFiniteIntegral, not_lt, top_le_iff] at hcon
  rw [hcon] at h
  simp at h

/-! ## Bounded functions -/

/-- **A function of finite energy of order `s > n/2` is bounded**: almost everywhere,
`|f|² ≤ wienerConst n s · E_s(f)`. -/
theorem ae_enorm_sq_le {s : ℝ} (hs : (n : ℝ) < 2 * s) (f : Lp ℂ 2 (volume : Measure (ℝ^n)))
    (hf : besselEnergy s (fun _ : Unit ↦ f) < ⊤) :
    ∀ᵐ x, ‖f x‖ₑ ^ 2 ≤ wienerConst n s * besselEnergy s (fun _ : Unit ↦ f) := by
  have hint := integrable_fourier_of_besselEnergy_lt_top hs f hf
  filter_upwards [ae_norm_le_integral_norm_fourier f hint] with x hx
  refine le_trans (pow_le_pow_left₀ zero_le ?_ 2) (sq_lintegral_enorm_fourier_le s f)
  rw [← ofReal_integral_norm_eq_lintegral_eNorm hint, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hx

/-- **The Sobolev embedding into `L^∞`**: for `s > n/2` and every `f ∈ L²(ℝⁿ)`,
`‖f‖_∞ ≤ √c ‖f‖_{H^s}` with `c = wienerConst n s`. If `f` is not in `H^s` the right side is
infinite. -/
theorem eLpNorm_top_le {s : ℝ} (hs : (n : ℝ) < 2 * s) (f : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    eLpNorm f ∞ volume ≤ wienerConst n s ^ (1 / 2 : ℝ) *
      besselEnergy s (fun _ : Unit ↦ f) ^ (1 / 2 : ℝ) := by
  by_cases hf : besselEnergy s (fun _ : Unit ↦ f) < ⊤
  · rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable f)]
    refine eLpNormEssSup_le_of_ae_eNorm_bound ?_
    filter_upwards [ae_enorm_sq_le hs f hf] with x hx
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), one_div,
      ENNReal.le_rpow_inv_iff (by norm_num : (0 : ℝ) < 2), ENNReal.rpow_two]
    exact hx
  · rw [not_lt, top_le_iff] at hf
    rw [hf, ENNReal.top_rpow_of_pos (by norm_num), ENNReal.mul_top]
    · exact le_top
    · exact (ENNReal.rpow_pos (pos_iff_ne_zero.2 (wienerConst_ne_zero n s))
        (wienerConst_lt_top hs).ne).ne'

/-- The `L²` norm is the square root of the energy of order zero. -/
theorem eLpNorm_two_eq_besselEnergy_zero (f : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    eLpNorm f 2 volume = besselEnergy 0 (fun _ : Unit ↦ f) ^ (1 / 2 : ℝ) := by
  rw [besselEnergy_zero, Finset.univ_unique, Finset.sum_singleton,
    ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num), ← Real.sqrt_eq_rpow,
    Real.sqrt_sq (norm_nonneg _), ofReal_norm, Lp.eNorm_def]

/-- **The Sobolev embedding into `L^q` above the critical order**: for `s > n/2`, every
`2 ≤ q ≤ ∞` and every `f ∈ L²(ℝⁿ)`, `‖f‖_q ≤ (1 + √c) ‖f‖_{H^s}` with `c = wienerConst n s`.
If `f` is not in `H^s` the right side is infinite. -/
theorem eLpNorm_le_of_two_le {s : ℝ} (hs : (n : ℝ) < 2 * s)
    (f : Lp ℂ 2 (volume : Measure (ℝ^n))) {q : ℝ≥0∞} (hq : 2 ≤ q) :
    eLpNorm f q volume ≤ (1 + wienerConst n s ^ (1 / 2 : ℝ)) *
      besselEnergy s (fun _ : Unit ↦ f) ^ (1 / 2 : ℝ) := by
  have hs0 : 0 ≤ s := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  refine (eLpNorm_le_eLpNorm_add_eLpNorm_top (by norm_num) hq).trans ?_
  rw [add_mul, one_mul]
  refine add_le_add ?_ (eLpNorm_top_le hs f)
  rw [eLpNorm_two_eq_besselEnergy_zero]
  exact ENNReal.rpow_le_rpow (besselEnergy_mono hs0 _) (by norm_num)

end SobolevSpace.Fractional
