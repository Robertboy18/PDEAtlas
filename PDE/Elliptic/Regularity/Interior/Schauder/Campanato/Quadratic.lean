/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Moments.Variance

/-!
# Comparing quadratic mean oscillations

The integral average minimizes mean-square deviation. Applying this fact before
a comparison separates the error energy from the oscillation of the comparison
field. The minimizing property is Mathlib's variance inequality applied to the
normalized restricted measure.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Elliptic.Regularity.Campanato

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {s : Set X}

/-- The average minimizes mean-square deviation. On a set of finite positive measure this is the
variance inequality for the normalized restricted measure; on a set of measure zero or infinite
measure both averages vanish. -/
theorem setAverage_norm_sub_average_sq_le
    {f : X → ℝ}
    (hf : MemLp f 2 (μ.restrict s)) (c : ℝ) :
    (⨍ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ 2 ∂μ) ≤
      ⨍ x in s, ‖f x - c‖ ^ 2 ∂μ := by
  by_cases hs0 : μ s = 0
  · simp [setAverage_eq, measureReal_def, hs0]
  by_cases hsfin : μ s = ∞
  · simp [setAverage_eq, measureReal_def, hsfin]
  let ν : Measure X := (μ s)⁻¹ • μ.restrict s
  have : IsProbabilityMeasure ν := ⟨by
    simp only [ν, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hs0 hsfin⟩
  have hfn : MemLp f 2 ν := hf.smul_measure (ENNReal.inv_ne_top.mpr hs0)
  have hvar := ProbabilityTheory.variance_le_expectation_sq
    (hfn.sub (memLp_const c)).aestronglyMeasurable
  change ProbabilityTheory.variance (fun x ↦ f x - c) ν ≤ ∫ x, (f x - c) ^ 2 ∂ν at hvar
  rw [ProbabilityTheory.variance_sub_const hfn.aestronglyMeasurable,
    ProbabilityTheory.variance_eq_integral hfn.aemeasurable] at hvar
  simpa only [average, Measure.restrict_apply_univ, Real.norm_eq_abs, sq_abs,
    Pi.pow_apply] using hvar

/-- Splitting a field into a comparison and an error bounds its mean-square
deviation by twice the error energy and twice the comparison deviation. -/
theorem setAverage_norm_sub_sq_le
    {f g : X → ℝ}
    (hf : MemLp f 2 (μ.restrict s)) (hg : MemLp g 2 (μ.restrict s)) (c : ℝ) :
    (⨍ x in s, ‖f x - c‖ ^ 2 ∂μ) ≤
      2 * (⨍ x in s, ‖f x - g x‖ ^ 2 ∂μ) +
        2 * (⨍ x in s, ‖g x - c‖ ^ 2 ∂μ) := by
  by_cases hsfin : μ s = ∞
  · simp [setAverage_eq, measureReal_def, hsfin]
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hsfin
  have hfc := (hf.sub (memLp_const c)).norm.integrable_sq
  have hfg := (hf.sub hg).norm.integrable_sq
  have hgc := (hg.sub (memLp_const c)).norm.integrable_sq
  simp only [Pi.sub_apply] at hfc hfg hgc
  have hpt (x : X) : ‖f x - c‖ ^ 2 ≤ 2 * ‖f x - g x‖ ^ 2 + 2 * ‖g x - c‖ ^ 2 := by
    simp only [Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg (f x - 2 * g x + c)]
  have hi : (∫ x in s, ‖f x - c‖ ^ 2 ∂μ) ≤
      ∫ x in s, 2 * ‖f x - g x‖ ^ 2 + 2 * ‖g x - c‖ ^ 2 ∂μ :=
    integral_mono hfc ((hfg.const_mul 2).add (hgc.const_mul 2)) hpt
  rw [integral_add (hfg.const_mul 2) (hgc.const_mul 2),
    integral_const_mul, integral_const_mul] at hi
  simp only [setAverage_eq, smul_eq_mul]
  have := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (measureReal_nonneg : 0 ≤ μ.real s))
  nlinarith

/-- A comparison controls mean-square oscillation through its own oscillation
and the mean-square error. No equality of the two averages is required. -/
theorem setAverage_oscillation_sq_le_comparison
    {f g : X → ℝ}
    (hf : MemLp f 2 (μ.restrict s)) (hg : MemLp g 2 (μ.restrict s)) :
    (⨍ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ 2 ∂μ) ≤
      2 * (⨍ x in s, ‖f x - g x‖ ^ 2 ∂μ) +
        2 * (⨍ x in s, ‖g x - ⨍ y in s, g y ∂μ‖ ^ 2 ∂μ) :=
  (setAverage_norm_sub_average_sq_le hf _).trans
    (setAverage_norm_sub_sq_le hf hg _)

end PDE.Elliptic.Regularity.Campanato
