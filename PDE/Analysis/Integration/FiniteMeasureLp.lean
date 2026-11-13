/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Bounds independent of the Lebesgue exponent on a finite measure space

Hölder's inequality bounds the integral norm by the `Lᵖ` norm for every
`1 ≤ p ≤ ∞`. Replacing the measure factor by its maximum with one makes
the constant independent of the exponent.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory

variable {α X : Type*} [MeasurableSpace α] [NormedAddCommGroup X]
  {μ : Measure α}

/-- On a finite measure space, the `L¹` norm is bounded by the `Lᵖ` norm with
a constant independent of `p ∈ [1, ∞]`. -/
theorem MemLp.integral_norm_le_max_measure_mul_lpNorm
    [IsFiniteMeasure μ] {f : α → X} {p : ℝ≥0∞} (hf : MemLp f p μ) (hp : 1 ≤ p) :
    (∫ x, ‖f x‖ ∂μ) ≤ max 1 (μ.real Set.univ) * lpNorm f p μ := by
  have hexp : 0 ≤ 1 - p.toReal⁻¹ := by
    by_cases htop : p = ∞
    · simp [htop]
    · have hreal : 1 ≤ p.toReal := by
        simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono htop hp
      exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hreal)
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hf.aestronglyMeasurable
  simp only [ENNReal.toReal_one, one_div, inv_one] at h
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hf.eLpNorm_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top μ Set.univ))) h
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, toReal_eLpNorm, toReal_eLpNorm,
    lpNorm_one_eq_integral_norm hf.aestronglyMeasurable] at hreal
  have hpow : (μ.real Set.univ) ^ (1 - p.toReal⁻¹) ≤ max 1 (μ.real Set.univ) := by
    rcases le_total (μ.real Set.univ) 1 with hμ | hμ
    · exact (Real.rpow_le_one (measureReal_nonneg) hμ hexp).trans (le_max_left _ _)
    · exact (Real.rpow_le_self_of_one_le hμ
        (sub_le_self _ (inv_nonneg.mpr ENNReal.toReal_nonneg))).trans (le_max_right _ _)
  exact hreal.trans ((mul_le_mul_of_nonneg_left hpow lpNorm_nonneg).trans_eq (mul_comm _ _))

/-- The sum of two `Lᵖ` norms is controlled by the norm obtained by adding
their `p`th powers before integration, uniformly in the positive exponent. -/
theorem lpNorm_add_lpNorm_le_two_mul_integral_rpow_add
    {Y : Type*} [NormedAddCommGroup Y] {f : α → X} {g : α → Y} {p : ℝ≥0∞}
    (hf : MemLp f p μ) (hg : MemLp g p μ) (hp0 : p ≠ 0) (hpt : p ≠ ∞) :
    lpNorm f p μ + lpNorm g p μ ≤
      2 * (∫ x, ‖f x‖ ^ p.toReal + ‖g x‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹ := by
  have hfi := hf.integrable_norm_rpow hp0 hpt
  have hgi := hg.integrable_norm_rpow hp0 hpt
  have hfpos : 0 ≤ ∫ x, ‖f x‖ ^ p.toReal ∂μ :=
    integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg _) _
  have hgpos : 0 ≤ ∫ x, ‖g x‖ ^ p.toReal ∂μ :=
    integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg _) _
  rw [lpNorm_eq_integral_norm_rpow_toReal hp0 hpt hf.aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal hp0 hpt hg.aestronglyMeasurable,
    integral_add hfi hgi]
  have hfbound := Real.rpow_le_rpow (z := p.toReal⁻¹) hfpos (le_add_of_nonneg_right hgpos)
    (inv_nonneg.mpr ENNReal.toReal_nonneg)
  have hgbound := Real.rpow_le_rpow (z := p.toReal⁻¹) hgpos (le_add_of_nonneg_left hfpos)
    (inv_nonneg.mpr ENNReal.toReal_nonneg)
  linarith

end MeasureTheory
