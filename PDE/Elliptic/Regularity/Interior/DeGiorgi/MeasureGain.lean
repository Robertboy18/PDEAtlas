/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Superlevel measure gain

Hölder's inequality on the support of a higher truncation converts an `Lᑫ`
estimate, `q > 2`, into an `L²` estimate with a positive power of the support
measure. This is the measure gain in the De Giorgi tail-energy recurrence.
The proof uses Mathlib's comparison of integral norms on a restricted measure.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Elliptic.Regularity.DeGiorgi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- An `L²` function supported in `E` and dominated by an `Lᑫ` function gains
the factor `μ(E)^(1-2/q)` in its squared norm. Null sets are allowed. -/
theorem integral_sq_le_eLpNorm_sq_mul_measure
    {q : ℝ≥0∞} (hq : 2 ≤ q) {f g : X → ℝ} {E : Set X}
    (hE : MeasurableSet E) (hf : MemLp f 2 μ) (hg : MemLp g q μ)
    (hsupport : ∀ᵐ x ∂μ, x ∉ E → f x = 0)
    (hdom : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
    (∫ x, f x ^ 2 ∂μ) ≤
      (eLpNorm g q μ).toReal ^ 2 * μ.real E ^ (1 - 2 / q.toReal) := by
  have heq : E.indicator f =ᵐ[μ] f := by
    filter_upwards [hsupport] with x hx
    by_cases hxE : x ∈ E
    · exact indicator_of_mem hxE f
    · rw [indicator_of_notMem hxE, hx hxE]
  have hn : eLpNorm f 2 μ = eLpNorm f 2 (μ.restrict E) := by
    rw [← eLpNorm_congr_ae heq, eLpNorm_indicator_eq_eLpNorm_restrict hE.nullMeasurableSet]
  have hlocal := eLpNorm_mono_ae (hf.restrict E).aestronglyMeasurable
    (hdom.filter_mono (ae_mono Measure.restrict_le_self)) (p := 2)
  have hHolder := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq
    (hg.restrict E).aestronglyMeasurable
  simp only [Measure.restrict_apply_univ, ENNReal.toReal_ofNat] at hHolder
  have hb : eLpNorm f 2 μ ≤
      eLpNorm g q μ * μ E ^ (1 / 2 - 1 / q.toReal) := by
    rw [hn]
    refine hlocal.trans (hHolder.trans ?_)
    gcongr
    exact Measure.restrict_le_self
  have hpow : μ E ^ (1 / 2 - 1 / q.toReal) ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg
    · have hq' : 1 / q.toReal ≤ 1 / (2 : ℝ) := by
        by_cases htop : q = ∞
        · simp [htop]
        · exact one_div_le_one_div_of_le (by norm_num) (by
            simpa using ENNReal.toReal_mono htop hq)
      linarith
    · exact measure_ne_top _ _
  have hbR := ENNReal.toReal_mono (ENNReal.mul_ne_top hg.eLpNorm_ne_top hpow) hb
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at hbR
  have hs := pow_le_pow_left₀ ENNReal.toReal_nonneg hbR 2
  rw [mul_pow] at hs
  change (eLpNorm f 2 μ).toReal ^ 2 ≤
    (eLpNorm g q μ).toReal ^ 2 * (μ.real E ^ (1 / 2 - 1 / q.toReal)) ^ 2 at hs
  have hr : (μ.real E ^ (1 / 2 - 1 / q.toReal)) ^ 2 =
      μ.real E ^ (1 - 2 / q.toReal) := by
    have hp := Real.rpow_mul_natCast (show 0 ≤ μ.real E from measureReal_nonneg)
      (1 / 2 - 1 / q.toReal) 2
    norm_num only [Nat.cast_ofNat] at hp
    rw [← hp]
    congr 1
    ring
  rw [hr] at hs
  rw [hf.integral_sq_eq_lpNorm_sq, ← toReal_eLpNorm]
  exact hs

end PDE.Elliptic.Regularity.DeGiorgi
