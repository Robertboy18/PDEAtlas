/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Membership at intermediate Lebesgue exponents

The sum of two integrable norm powers dominates every power between them.
This gives intermediate membership on arbitrary measures, including infinite
measure spaces where monotonicity in the exponent alone does not apply.
For `0 < p ≤ q ≤ ∞` the bound `‖f‖_q ≤ ‖f‖_p^{p/q} ‖f‖_∞^{1 - p/q}` gives
`‖f‖_q ≤ ‖f‖_p + ‖f‖_∞`, so `Lᵖ ∩ L∞ ⊂ Lᵠ`.
Hölder's inequality bounds the cubic lower integral by `‖f‖₂^{3/2} ‖f‖₆^{3/2}`.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  {μ : Measure α} {f : α → E} {p q r : ℝ}

/-- Two finite positive Lebesgue exponents give membership at every intermediate
exponent, with no finiteness assumption on the measure. -/
theorem MemLp.of_exponent_between (hp : 0 < p) (hpr : p ≤ r) (hrq : r ≤ q)
    (hfp : MemLp f (ENNReal.ofReal p) μ) (hfq : MemLp f (ENNReal.ofReal q) μ) :
    MemLp f (ENNReal.ofReal r) μ := by
  have hr : 0 < r := hp.trans_le hpr
  have hq : 0 < q := hr.trans_le hrq
  have hi (s : ℝ) (hs : 0 < s) (hf : MemLp f (ENNReal.ofReal s) μ) :
      Integrable (fun x ↦ ‖f x‖ ^ s) μ := by
    simpa only [ENNReal.toReal_ofReal hs.le] using
      hf.integrable_norm_rpow (by positivity) ENNReal.ofReal_ne_top
  apply (integrable_norm_rpow_iff hfp.aestronglyMeasurable
    (by positivity : ENNReal.ofReal r ≠ 0) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal hr.le]
  refine ((hi p hp hfp).add (hi q hq hfq)).mono'
    ((Real.continuous_rpow_const hr.le).comp_aestronglyMeasurable
      hfp.aestronglyMeasurable.norm) ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    by_cases hx : ‖f x‖ ≤ 1
    · exact (Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hx hp.le hpr).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _))
    · exact (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx) hrq).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _))

/-- For `0 < p ≤ q ≤ ∞` the `Lᵠ` seminorm is at most the sum of the `Lᵖ` and `L∞` seminorms,
from `‖f‖_q ≤ ‖f‖_p^{p/q} ‖f‖_∞^{1 - p/q}`. -/
theorem eLpNorm_le_eLpNorm_add_eLpNorm_top {p q : ℝ≥0∞} (hp : p ≠ 0) (hpq : p ≤ q) :
    eLpNorm f q μ ≤ eLpNorm f p μ + eLpNorm f ∞ μ := by
  rcases eq_or_ne q ∞ with rfl | hq
  · exact le_add_self
  have hp' : p ≠ ∞ := ne_top_of_le_ne_top hq hpq
  have hq0 : q ≠ 0 := (pos_iff_ne_zero.mpr hp |>.trans_le hpq).ne'
  by_cases hf : AEStronglyMeasurable f μ
  swap
  · simp [eLpNorm_of_not_aestronglyMeasurable hf]
  set M := eLpNorm f ∞ μ
  rcases eq_or_ne M ∞ with hM | hM
  · rw [hM, add_top]
    exact le_top
  have hP : 0 < p.toReal := ENNReal.toReal_pos hp hp'
  have hQ : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  have hPQ : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq hpq
  have hae : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ M := by
    rw [show M = eLpNormEssSup f μ from eLpNorm_exponent_top hf]
    exact ae_le_eLpNormEssSup
  set I := ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ
  have hint : ∫⁻ x, ‖f x‖ₑ ^ q.toReal ∂μ ≤ M ^ (q.toReal - p.toReal) * I := by
    rw [← lintegral_const_mul' _ _
      (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.mpr hPQ) hM)]
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with x hx
    calc
      ‖f x‖ₑ ^ q.toReal = ‖f x‖ₑ ^ (q.toReal - p.toReal) * ‖f x‖ₑ ^ p.toReal := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.mpr hPQ) hP.le, sub_add_cancel]
      _ ≤ M ^ (q.toReal - p.toReal) * ‖f x‖ₑ ^ p.toReal := by
        gcongr
  set a := eLpNorm f p μ
  have ha : a = I ^ (1 / p.toReal) := eLpNorm_eq_lintegral_rpow_enorm_toReal hp hp' hf
  have hI : I = a ^ p.toReal := by
    rw [ha, ← ENNReal.rpow_mul, one_div_mul_cancel hP.ne', ENNReal.rpow_one]
  set θ := p.toReal / q.toReal
  have hθ0 : 0 ≤ θ := div_nonneg hP.le hQ.le
  have hθ1 : 0 ≤ 1 - θ := sub_nonneg.mpr (div_le_one_of_le₀ hPQ hQ.le)
  calc
    eLpNorm f q μ = (∫⁻ x, ‖f x‖ₑ ^ q.toReal ∂μ) ^ (1 / q.toReal) :=
      eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq hf
    _ ≤ (M ^ (q.toReal - p.toReal) * I) ^ (1 / q.toReal) := by gcongr
    _ = M ^ (1 - θ) * a ^ θ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), hI, ← ENNReal.rpow_mul,
        ← ENNReal.rpow_mul]
      congr 2
      · simp only [θ]
        field_simp
      · simp only [θ]
        field_simp
    _ ≤ (a + M) ^ (1 - θ) * (a + M) ^ θ := by
      gcongr
      · exact le_add_self
      · exact le_self_add
    _ = a + M := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ hθ1 hθ0, sub_add_cancel, ENNReal.rpow_one]

/-- A function in `Lᵖ` and in `L∞` lies in every `Lᵠ`, `p ≤ q ≤ ∞`, `p ≠ 0`. -/
theorem MemLp.of_le_exponent_of_memLp_top {p q : ℝ≥0∞} (hfp : MemLp f p μ) (hf : MemLp f ∞ μ)
    (hp : p ≠ 0) (hpq : p ≤ q) : MemLp f q μ :=
  lt_of_le_of_lt (eLpNorm_le_eLpNorm_add_eLpNorm_top hp hpq)
    (ENNReal.add_lt_top.mpr ⟨hfp.eLpNorm_lt_top, hf.eLpNorm_lt_top⟩)

/-- The lower Lebesgue integral of `‖f‖³` is at most `‖f‖₂^{3/2} ‖f‖₆^{3/2}`, by Hölder's
inequality with exponents `4/3` and `4` applied to `‖f‖²` and `‖f‖⁶`. -/
theorem lintegral_enorm_cube_le (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, ‖f x‖ₑ ^ 3 ∂μ ≤ eLpNorm f 2 μ ^ (3 / 2 : ℝ) * eLpNorm f 6 μ ^ (3 / 2 : ℝ) := by
  have hint (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpt : p ≠ ⊤) :
      ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ = eLpNorm f p μ ^ p.toReal := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hf, ← ENNReal.rpow_mul, one_div,
      inv_mul_cancel₀ (ENNReal.toReal_pos hp0 hpt).ne', ENNReal.rpow_one]
  have h2 := hint 2 (by norm_num) (by norm_num)
  have h6 := hint 6 (by norm_num) (by norm_num)
  rw [ENNReal.toReal_ofNat] at h2 h6
  have hpow (x : ℝ≥0∞) : x ^ 3 = (x ^ (2 : ℝ)) ^ (3 / 4 : ℝ) * (x ^ (6 : ℝ)) ^ (1 / 4 : ℝ) := by
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num)
      (by norm_num)]
    norm_num
  calc ∫⁻ x, ‖f x‖ₑ ^ 3 ∂μ
      = ∫⁻ x, (‖f x‖ₑ ^ (2 : ℝ)) ^ (3 / 4 : ℝ) * (‖f x‖ₑ ^ (6 : ℝ)) ^ (1 / 4 : ℝ) ∂μ := by
        simp_rw [hpow]
    _ ≤ (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (3 / 4 : ℝ) * (∫⁻ x, ‖f x‖ₑ ^ (6 : ℝ) ∂μ) ^ (1 / 4 : ℝ) :=
        ENNReal.lintegral_mul_norm_pow_le (hf.enorm.pow_const _) (hf.enorm.pow_const _)
          (by norm_num) (by norm_num) (by norm_num)
    _ = eLpNorm f 2 μ ^ (3 / 2 : ℝ) * eLpNorm f 6 μ ^ (3 / 2 : ℝ) := by
        rw [h2, h6, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num

end MeasureTheory
