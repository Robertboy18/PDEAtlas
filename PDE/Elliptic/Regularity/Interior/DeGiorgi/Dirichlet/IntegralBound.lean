/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.DivergenceForm
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Support measure in the scalar load estimate

Hölder's inequality bounds the integral of a function supported in `E` by
its `Lᑫ` norm times `|E|^(1-1/q)`. Together with the scalar forcing bound,
this gives the load estimate for the zero-boundary superlevel test.
The measure estimate is Mathlib's Chebyshev inequality in real-valued form.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev InnerProductSpace

namespace PDE.Elliptic.Regularity.DeGiorgi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- Hölder's support factor for the `L¹` norm, including a null support set. -/
theorem integral_norm_le_eLpNorm_mul_measure
    {q : ℝ≥0∞} (hq : 1 ≤ q) (hqt : q ≠ ∞) {f : X → ℝ} (hf : MemLp f q μ)
    {E : Set X} (hE : MeasurableSet E)
    (hsupport : ∀ᵐ x ∂μ, x ∉ E → f x = 0) :
    (∫ x, ‖f x‖ ∂μ) ≤
      (eLpNorm f q μ).toReal * μ.real E ^ (1 - 1 / q.toReal) := by
  have heq : E.indicator f =ᵐ[μ] f := by
    filter_upwards [hsupport] with x hx
    by_cases hxE : x ∈ E
    · exact indicator_of_mem hxE f
    · rw [indicator_of_notMem hxE, hx hxE]
  have hn : eLpNorm f 1 μ = eLpNorm f 1 (μ.restrict E) := by
    rw [← eLpNorm_congr_ae heq, eLpNorm_indicator_eq_eLpNorm_restrict hE.nullMeasurableSet]
  have hb : eLpNorm f 1 μ ≤ eLpNorm f q μ * μ E ^ (1 - 1 / q.toReal) := by
    rw [hn]
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq
      (hf.restrict E).aestronglyMeasurable
    simp only [Measure.restrict_apply_univ, ENNReal.toReal_one, div_one] at h
    refine h.trans ?_
    gcongr
    exact Measure.restrict_le_self
  have hqr : 1 ≤ q.toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hqt hq
  have hpow : μ E ^ (1 - 1 / q.toReal) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg
      (sub_nonneg.mpr (by simpa using one_div_le_one_div_of_le zero_lt_one hqr))
      (measure_ne_top _ _)
  have hR := ENNReal.toReal_mono (ENNReal.mul_ne_top hf.eLpNorm_ne_top hpow) hb
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at hR
  rw [← lpNorm_one_eq_integral_norm hf.aestronglyMeasurable, ← toReal_eLpNorm]
  exact hR

omit [IsFiniteMeasure μ] in
/-- Chebyshev's inequality on any measurable subset of a norm superlevel.
The threshold is positive and the exponent is finite and nonzero. -/
theorem measure_mul_rpow_le_eLpNorm
    {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqt : q ≠ ∞) {f : X → ℝ} (hf : MemLp f q μ)
    {E : Set X} {h : ℝ} (hh : 0 < h)
    (hE : ∀ᵐ x ∂μ, x ∈ E → h ≤ ‖f x‖) :
    h ^ q.toReal * μ.real E ≤ (eLpNorm f q μ).toReal ^ q.toReal := by
  have hm : μ E ≤ μ {x | ENNReal.ofReal h ≤ ‖f x‖ₑ} := by
    apply measure_mono_ae
    filter_upwards [hE] with x hx hxE
    exact (ENNReal.ofReal_le_ofReal (hx hxE)).trans_eq (ofReal_norm _)
  have hb : ENNReal.ofReal h ^ q.toReal * μ E ≤ eLpNorm f q μ ^ q.toReal :=
    (mul_le_mul le_rfl hm bot_le bot_le).trans
      (mul_meas_ge_le_pow_eLpNorm' μ hq0 hqt (ENNReal.ofReal h))
  have hbR := ENNReal.toReal_mono
    (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hf.eLpNorm_ne_top) hb
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hh.le, measureReal_def] using hbR

end PDE.Elliptic.Regularity.DeGiorgi

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set ℝ^n} [IsFiniteMeasure (domainMeasure n Ω)]

/-- A bounded scalar load gains the measure of the support of its test
function. The `Lᑫ` hypothesis concerns that test, not the weak solution. -/
theorem loadFunctional_le_eLpNorm_mul_measure
    (f : DerivLp n 2 Ω) {M : ℝ}
    (hf : ∀ᵐ x ∂domainMeasure n Ω, ‖f x‖ ≤ M)
    (v : H¹₀(Ω)) {q : ℝ≥0∞} (hq : 1 ≤ q) (hqt : q ≠ ∞)
    (hv : MemLp (baseCoordCLM v) q (domainMeasure n Ω))
    {E : Set ℝ^n} (hE : MeasurableSet E)
    (hsupport : ∀ᵐ x ∂domainMeasure n Ω, x ∉ E → baseCoordCLM v x = 0)
    (hM : 0 ≤ M) :
    loadFunctional f v ≤ M * (eLpNorm (baseCoordCLM v) q (domainMeasure n Ω)).toReal *
      (domainMeasure n Ω).real E ^ (1 - 1 / q.toReal) := by
  have hbound : loadFunctional f v ≤ M * ∫ x, ‖baseCoordCLM v x‖ ∂domainMeasure n Ω := by
    rw [loadFunctional_apply, L2.inner_def, ← integral_const_mul]
    apply integral_mono_ae (L2.integrable_inner f (baseCoordCLM v))
      (((Lp.memLp (baseCoordCLM v)).integrable (by norm_num)).norm.const_mul M)
    filter_upwards [hf] with x hx
    exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  exact hbound.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (PDE.Elliptic.Regularity.DeGiorgi.integral_norm_le_eLpNorm_mul_measure
        hq hqt hv hE hsupport) hM)

end SobolevSpace.GraphSpace
