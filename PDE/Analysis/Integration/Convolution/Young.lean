/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.Prod
import CAS.ExactTactic
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

/-!
# Young's convolution inequality

Weighted Hölder and Tonelli give the convolution estimate for positive finite
exponents satisfying 1/p + 1/q = 1 + 1/r and p,q ≤ r. The ENNReal bounds retain
infinite norms and allow zero Hölder weights, including the L¹ cases. Real
Bochner convolution satisfies the same norm bound; finite input norms also
ensure that its integrand is integrable almost everywhere.

For exponents `1 ≤ p, q ≤ ∞` with `1/p + 1/q = 1 + 1/r` the inequality holds for nonnegative
convolutions at every `r ∈ [1, ∞]`. For finite `r` the exponents are finite and the first
inequality applies; for `r = ∞` the exponents `p` and `q` are conjugate, and the bound is
Hölder's inequality at every point, since a translated and reflected function keeps its `Lᵖ`
norm. `ENNReal.youngExponent p r` is the kernel exponent `q` for given `p ≤ r`.

The measure is s-finite, translation invariant and reflection invariant on
an additive commutative group.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ENNReal

/-- The nonnegative three-factor decomposition for Young's inequality, including zero weights. -/
theorem young_factorization {p q r : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hpr : p ≤ r) (hqr : q ≤ r) (a b : ℝ≥0∞) :
    (a ^ p * b ^ q) ^ (1 / r) *
      ((a ^ p) ^ (1 / p - 1 / r) * (b ^ q) ^ (1 / q - 1 / r)) = a * b := by
  have hr : 0 < r := by linarith
  have hpw : 0 ≤ 1 / p - 1 / r := sub_nonneg.mpr (one_div_le_one_div_of_le hp hpr)
  have hqw : 0 ≤ 1 / q - 1 / r := sub_nonneg.mpr (one_div_le_one_div_of_le hq hqr)
  rw [mul_rpow_of_nonneg _ _ (by positivity)]
  simp only [← rpow_mul]
  calc
    _ = (a ^ (p * (1 / r)) * a ^ (p * (1 / p - 1 / r))) *
        (b ^ (q * (1 / r)) * b ^ (q * (1 / q - 1 / r))) := by ac_rfl
    _ = a ^ (p * (1 / r) + p * (1 / p - 1 / r)) *
        b ^ (q * (1 / r) + q * (1 / q - 1 / r)) := by
      rw [rpow_add_of_nonneg _ _ (by positivity) (mul_nonneg hp.le hpw),
        rpow_add_of_nonneg _ _ (by positivity) (mul_nonneg hq.le hqw)]
    _ = a * b := by
      have hp' : p * (1 / r) + p * (1 / p - 1 / r) = 1 := by cas using [hp, hq, hr]
      have hq' : q * (1 / r) + q * (1 / q - 1 / r) = 1 := by cas using [hp, hq, hr]
      rw [hp', hq', rpow_one, rpow_one]

/-- Three-factor Hölder in the form used for finite-exponent Young inequalities. -/
theorem lintegral_mul_rpow_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p q r : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hpr : p ≤ r) (hqr : q ≤ r) (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, f x * g x ∂μ) ^ r ≤ (∫⁻ x, f x ^ p * g x ^ q ∂μ) *
      ((∫⁻ x, f x ^ p ∂μ) ^ (r / p - 1) *
        (∫⁻ x, g x ^ q ∂μ) ^ (r / q - 1)) := by
  have hr : 0 < r := by linarith
  let F : Fin 3 → α → ℝ≥0∞ :=
    ![fun x ↦ f x ^ p * g x ^ q, fun x ↦ f x ^ p, fun x ↦ g x ^ q]
  let w : Fin 3 → ℝ := ![1 / r, 1 / p - 1 / r, 1 / q - 1 / r]
  have h := lintegral_prod_norm_pow_le Finset.univ
    (μ := μ) (f := F) (p := w)
    (by intro i _; fin_cases i <;> dsimp [F] <;> fun_prop)
    (by simp only [w, Fin.sum_univ_succ]; dsimp; linarith)
    (by
      intro i _
      fin_cases i
      · dsimp [w]; positivity
      · exact sub_nonneg.mpr (one_div_le_one_div_of_le hp hpr)
      · exact sub_nonneg.mpr (one_div_le_one_div_of_le hq hqr))
  simp only [Fin.prod_univ_succ, F, w, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.prod_univ_zero, mul_one] at h
  simp_rw [young_factorization hp hq hpr hqr] at h
  have hpow := rpow_le_rpow h hr.le
  have hw₀ : (1 / r) * r = 1 := by cas using [hp, hq, hr]
  have hw₁ : (1 / p - 1 / r) * r = r / p - 1 := by cas using [hp, hq, hr]
  have hw₂ : (1 / q - 1 / r) * r = r / q - 1 := by cas using [hp, hq, hr]
  simpa only [mul_rpow_of_nonneg _ _ hr.le, ← rpow_mul, hw₀, hw₁, hw₂, rpow_one] using hpow

/-- Young's power-integral inequality for all finite positive admissible exponents. -/
theorem lintegral_convolution_rpow_le {G : Type*} [MeasurableSpace G]
    [AddCommGroup G] [MeasurableAdd₂ G] [MeasurableNeg G] (μ : Measure G)
    [SFinite μ] [Measure.IsAddLeftInvariant μ] [Measure.IsNegInvariant μ]
    {p q r : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hpr : p ≤ r) (hqr : q ≤ r) (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    {f g : G → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, (∫⁻ y, f (x - y) * g y ∂μ) ^ r ∂μ) ≤
      (∫⁻ x, f x ^ p ∂μ) ^ (r / p) * (∫⁻ x, g x ^ q ∂μ) ^ (r / q) := by
  have hr : 0 < r := by linarith
  let a := ∫⁻ x, f x ^ p ∂μ
  let b := ∫⁻ x, g x ^ q ∂μ
  let F : G → G → ℝ≥0∞ := fun x y ↦ f (x - y) ^ p * g y ^ q
  have hF : Measurable (Function.uncurry F) := by dsimp [F]; fun_prop
  have hpoint (x : G) : (∫⁻ y, f (x - y) * g y ∂μ) ^ r ≤
      (∫⁻ y, F x y ∂μ) * (a ^ (r / p - 1) * b ^ (r / q - 1)) := by
    simpa only [a, b, F, lintegral_sub_left_eq_self (fun z ↦ f z ^ p) x] using
      lintegral_mul_rpow_le (μ := μ) (f := fun y ↦ f (x - y)) hp hq hpr hqr hpqr
        (hf.comp (measurable_const.sub measurable_id)) hg
  have htotal : (∫⁻ x, ∫⁻ y, F x y ∂μ ∂μ) = a * b := by
    rw [lintegral_lintegral_swap hF.aemeasurable]
    have hinner (y : G) : (∫⁻ x, F x y ∂μ) = a * g y ^ q := by
      dsimp [F]
      rw [lintegral_mul_const _ (show Measurable (fun x : G ↦ f (x - y) ^ p)
        from (hf.comp (measurable_id.sub measurable_const)).pow_const _),
        lintegral_sub_right_eq_self (fun z ↦ f z ^ p) y]
    simp_rw [hinner]
    exact lintegral_const_mul _ (hg.pow_const _)
  calc
    _ ≤ ∫⁻ x, (∫⁻ y, F x y ∂μ) * (a ^ (r / p - 1) * b ^ (r / q - 1)) ∂μ :=
      lintegral_mono hpoint
    _ = (a * b) * (a ^ (r / p - 1) * b ^ (r / q - 1)) := by
      rw [lintegral_mul_const _ hF.lintegral_prod_right, htotal]
    _ = (a * a ^ (r / p - 1)) * (b * b ^ (r / q - 1)) := by ac_rfl
    _ = a ^ (r / p) * b ^ (r / q) := by
      have ha : 0 ≤ r / p - 1 := sub_nonneg.mpr ((one_le_div hp).mpr hpr)
      have hb : 0 ≤ r / q - 1 := sub_nonneg.mpr ((one_le_div hq).mpr hqr)
      calc
        _ = (a ^ (1 : ℝ) * a ^ (r / p - 1)) *
            (b ^ (1 : ℝ) * b ^ (r / q - 1)) := by rw [rpow_one, rpow_one]
        _ = _ := by
          rw [← rpow_add_of_nonneg 1 _ zero_le_one ha,
            ← rpow_add_of_nonneg 1 _ zero_le_one hb]
          congr 2 <;> ring

/-- Young's inequality for finite positive exponents, without finite-norm assumptions. -/
theorem eLpNorm_lintegral_convolution_le {G : Type*} [MeasurableSpace G]
    [AddCommGroup G] [MeasurableAdd₂ G] [MeasurableNeg G] (μ : Measure G)
    [SFinite μ] [Measure.IsAddLeftInvariant μ] [Measure.IsNegInvariant μ]
    {p q r : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hpr : p ≤ r) (hqr : q ≤ r) (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    {f g : G → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    eLpNorm (fun x ↦ ∫⁻ y, f (x - y) * g y ∂μ) (ENNReal.ofReal r) μ ≤
      eLpNorm f (ENNReal.ofReal p) μ * eLpNorm g (ENNReal.ofReal q) μ := by
  have hr : 0 < r := by linarith
  have hkernel : Measurable (fun z : G × G ↦ f (z.1 - z.2) * g z.2) := by fun_prop
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ne_of_gt (ofReal_pos.mpr hr)) ofReal_ne_top
      hkernel.lintegral_prod_right.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (ne_of_gt (ofReal_pos.mpr hp)) ofReal_ne_top
      hf.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (ne_of_gt (ofReal_pos.mpr hq)) ofReal_ne_top
      hg.aestronglyMeasurable]
  simp only [toReal_ofReal hp.le, toReal_ofReal hq.le, toReal_ofReal hr.le, enorm_eq_self]
  have h := rpow_le_rpow (lintegral_convolution_rpow_le μ hp hq hpr hqr hpqr hf hg)
    (by positivity : (0 : ℝ) ≤ 1 / r)
  have hpr' : r / p * (1 / r) = 1 / p := by cas using [hp, hq, hr]
  have hqr' : r / q * (1 / r) = 1 / q := by cas using [hp, hq, hr]
  simpa only [mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / r),
    ← rpow_mul, hpr', hqr'] using h

section AllExponents

variable {G : Type*} [MeasurableSpace G] [AddCommGroup G] [MeasurableAdd₂ G] [MeasurableNeg G]
  (μ : Measure G) [SFinite μ] [Measure.IsAddLeftInvariant μ] [Measure.IsNegInvariant μ]

/-- The exponent relation forces `p ≤ r` when `q ≥ 1`. -/
theorem le_of_inv_add_inv_eq {p q r : ℝ≥0∞} (hq : 1 ≤ q) (hpqr : p⁻¹ + q⁻¹ = 1 + r⁻¹) :
    p ≤ r := by
  have hq' : q⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr hq
  have h : 1 + r⁻¹ ≤ 1 + p⁻¹ := by
    rw [← hpqr, add_comm 1 p⁻¹]
    exact add_le_add_right hq' _
  exact ENNReal.inv_le_inv.mp ((ENNReal.add_le_add_iff_left one_ne_top).mp h)

/-- Young's inequality for nonnegative convolutions with exponents in `[1, ∞]`. -/
theorem eLpNorm_lintegral_convolution_le_of_one_le {p q r : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpqr : p⁻¹ + q⁻¹ = 1 + r⁻¹) {f g : G → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    eLpNorm (fun x ↦ ∫⁻ y, f (x - y) * g y ∂μ) r μ ≤ eLpNorm f p μ * eLpNorm g q μ := by
  have hpr : p ≤ r := le_of_inv_add_inv_eq hq hpqr
  have hqr : q ≤ r := le_of_inv_add_inv_eq hp (by rwa [add_comm])
  by_cases hr : r = ∞
  · subst hr
    have hconj : p.HolderConjugate q := ⟨by simpa using hpqr⟩
    have hpoint (x : G) : (∫⁻ y, f (x - y) * g y ∂μ) ≤ eLpNorm f p μ * eLpNorm g q μ := by
      have hshift : Measurable (fun y ↦ f (x - y)) := hf.comp (measurable_const.sub measurable_id)
      have hholder := eLpNorm_le_eLpNorm_mul_eLpNorm_ennreal (μ := μ) (p := p) (q := q) (r := 1)
        hshift.aestronglyMeasurable hg.aestronglyMeasurable
      rw [eLpNorm_one_eq_lintegral_enorm ((hshift.mul hg).aestronglyMeasurable)] at hholder
      have htrans : eLpNorm (fun y ↦ f (x - y)) p μ = eLpNorm f p μ :=
        eLpNorm_comp_measurePreserving (g := f) (f := fun y ↦ x - y)
          hf.aestronglyMeasurable (Measure.measurePreserving_sub_left μ x)
      simpa only [Pi.mul_apply, enorm_eq_self, htrans] using hholder
    have hkernel : Measurable (fun z : G × G ↦ f (z.1 - z.2) * g z.2) := by fun_prop
    rw [eLpNorm_exponent_top hkernel.lintegral_prod_right.aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_enorm_bound (Filter.Eventually.of_forall fun x ↦ by
      simpa only [enorm_eq_self] using hpoint x)
  · have hp' : p ≠ ∞ := ne_top_of_le_ne_top hr hpr
    have hq' : q ≠ ∞ := ne_top_of_le_ne_top hr hqr
    have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp'
    have hq0 : 0 < q.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hq).ne' hq'
    have hr0 : 0 < r.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (hp.trans hpr)).ne' hr
    have hreal : 1 / p.toReal + 1 / q.toReal = 1 + 1 / r.toReal := by
      have h := congrArg ENNReal.toReal hpqr
      rw [ENNReal.toReal_add (ENNReal.inv_ne_top.mpr (zero_lt_one.trans_le hp).ne')
          (ENNReal.inv_ne_top.mpr (zero_lt_one.trans_le hq).ne'),
        ENNReal.toReal_add one_ne_top
          (ENNReal.inv_ne_top.mpr (zero_lt_one.trans_le (hp.trans hpr)).ne'),
        ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_one] at h
      simpa only [one_div] using h
    have h := eLpNorm_lintegral_convolution_le μ hp0 hq0
      ((ENNReal.toReal_le_toReal hp' hr).mpr hpr) ((ENNReal.toReal_le_toReal hq' hr).mpr hqr)
      hreal hf hg
    simpa only [ENNReal.ofReal_toReal hp', ENNReal.ofReal_toReal hq', ENNReal.ofReal_toReal hr]
      using h


/-- The kernel exponent `q` of Young's inequality for data in `Lᵖ` and output in `Lʳ`, with
`1/p + 1/q = 1 + 1/r`. -/
noncomputable def youngExponent (p r : ℝ≥0∞) : ℝ≥0∞ :=
  (1 + r⁻¹ - p⁻¹)⁻¹

theorem one_le_youngExponent {p r : ℝ≥0∞} (hpr : p ≤ r) : 1 ≤ youngExponent p r := by
  unfold youngExponent
  rw [ENNReal.one_le_inv, tsub_le_iff_right]
  exact add_le_add_right (ENNReal.inv_le_inv.mpr hpr) 1

theorem inv_add_inv_youngExponent {p : ℝ≥0∞} (r : ℝ≥0∞) (hp : 1 ≤ p) :
    p⁻¹ + (youngExponent p r)⁻¹ = 1 + r⁻¹ := by
  unfold youngExponent
  rw [inv_inv]
  exact add_tsub_cancel_of_le ((ENNReal.inv_le_one.mpr hp).trans le_self_add)

end AllExponents

end ENNReal

namespace MeasureTheory

/-- Young's finite-exponent inequality for real convolution, with its Bochner integral. -/
theorem eLpNorm_integral_convolution_le {G : Type*} [MeasurableSpace G]
    [AddCommGroup G] [MeasurableAdd₂ G] [MeasurableNeg G] (μ : Measure G)
    [SFinite μ] [Measure.IsAddLeftInvariant μ] [Measure.IsNegInvariant μ]
    {p q r : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hpr : p ≤ r) (hqr : q ≤ r) (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    {f g : G → ℝ} (hf : Measurable f) (hg : Measurable g) :
    eLpNorm (fun x ↦ ∫ y, f (x - y) * g y ∂μ) (ENNReal.ofReal r) μ ≤
      eLpNorm f (ENNReal.ofReal p) μ * eLpNorm g (ENNReal.ofReal q) μ := by
  have hr : 0 < r := by linarith
  have hkernel : Measurable (fun z : G × G ↦ f (z.1 - z.2) * g z.2) := by fun_prop
  calc
    _ ≤ eLpNorm (fun x ↦ ∫⁻ y, ‖f (x - y)‖ₑ * ‖g y‖ₑ ∂μ) (ENNReal.ofReal r) μ := by
      apply eLpNorm_mono_enorm hkernel.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
      intro x
      simpa only [enorm_eq_self, enorm_mul] using
        enorm_integral_le_lintegral_enorm (μ := μ) (fun y ↦ f (x - y) * g y)
    _ ≤ eLpNorm (fun x ↦ ‖f x‖ₑ) (ENNReal.ofReal p) μ *
        eLpNorm (fun x ↦ ‖g x‖ₑ) (ENNReal.ofReal q) μ :=
      ENNReal.eLpNorm_lintegral_convolution_le μ hp hq hpr hqr hpqr hf.enorm hg.enorm
    _ = _ := by
      rw [eLpNorm_enorm f hf.aestronglyMeasurable, eLpNorm_enorm g hg.aestronglyMeasurable]

/-- Finite Young data give an actual integrable convolution integrand almost everywhere. -/
theorem ae_integrable_convolution_of_memLp {G : Type*} [MeasurableSpace G]
    [AddCommGroup G] [MeasurableAdd₂ G] [MeasurableNeg G] (μ : Measure G)
    [SFinite μ] [Measure.IsAddLeftInvariant μ] [Measure.IsNegInvariant μ]
    {p q r : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hpr : p ≤ r) (hqr : q ≤ r) (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    {f g : G → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfp : MemLp f (ENNReal.ofReal p) μ) (hgq : MemLp g (ENNReal.ofReal q) μ) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ f (x - y) * g y) μ := by
  have hr : 0 < r := by linarith
  have hfp' : (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) < ⊤ := by
    simpa only [ENNReal.toReal_ofReal hp.le] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top hfp
  have hgq' : (∫⁻ x, ‖g x‖ₑ ^ q ∂μ) < ⊤ := by
    simpa only [ENNReal.toReal_ofReal hq.le] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (ne_of_gt (ENNReal.ofReal_pos.mpr hq)) ENNReal.ofReal_ne_top hgq
  have hbound := ENNReal.lintegral_convolution_rpow_le μ hp hq hpr hqr hpqr hf.enorm hg.enorm
  have hfin : (∫⁻ x, (∫⁻ y, ‖f (x - y)‖ₑ * ‖g y‖ₑ ∂μ) ^ r ∂μ) < ⊤ :=
    hbound.trans_lt (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (div_nonneg hr.le hp.le) hfp'.ne)
      (ENNReal.rpow_lt_top_of_nonneg (div_nonneg hr.le hq.le) hgq'.ne))
  have hm : Measurable (fun z : G × G ↦ ‖f (z.1 - z.2)‖ₑ * ‖g z.2‖ₑ) := by fun_prop
  filter_upwards [ae_lt_top (hm.lintegral_prod_right.pow_const r) hfin.ne] with x hx
  refine ⟨((hf.comp (measurable_const.sub measurable_id)).mul hg).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simp only [enorm_mul]
  by_contra h
  have heq : (∫⁻ y, ‖f (x - y)‖ₑ * ‖g y‖ₑ ∂μ) = ⊤ := top_unique (not_lt.mp h)
  rw [heq, ENNReal.top_rpow_of_pos hr] at hx
  exact (lt_irrefl _ hx)

end MeasureTheory
