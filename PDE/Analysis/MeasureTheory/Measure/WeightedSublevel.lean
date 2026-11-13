/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
import CAS.ExactTactic

/-!
# Weighted measures of sublevel sets

A weight bounded by the sublevel function turns linear measure growth into
quadratic weighted growth. Squaring the sublevel function restores linear growth.
-/

@[expose] public noncomputable section

open Filter Set

namespace MeasureTheory

/-- Linear decay of a density upgrades linear sublevel growth to quadratic
weighted sublevel growth. -/
theorem measureReal_withDensity_sublevel_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {w ρ : α → ℝ} {C L r : ℝ}
    (hw : Integrable w μ) (hwpos : 0 ≤ᵐ[μ] w) (hL : 0 ≤ L) (hr : 0 < r)
    (hρ : Measurable ρ) (hbound : ∀ᵐ x ∂μ, w x ≤ L * ρ x)
    (hlayer : μ.real {x | ρ x ≤ r} ≤ C * r) :
    (μ.withDensity (fun x ↦ ENNReal.ofReal (w x))).real {x | ρ x ≤ r} ≤
      L * C * r ^ 2 := by
  have hs : MeasurableSet {x | ρ x ≤ r} := measurableSet_le hρ measurable_const
  have heq : (μ.withDensity (fun x ↦ ENNReal.ofReal (w x))).real {x | ρ x ≤ r} =
      ∫ x in {x | ρ x ≤ r}, w x ∂μ := by
    rw [measureReal_def, withDensity_apply _ hs]
    exact (integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae hwpos)
      hw.aestronglyMeasurable.restrict).symm
  rw [heq]
  calc
    (∫ x in {x | ρ x ≤ r}, w x ∂μ) ≤ ∫ _ in {x | ρ x ≤ r}, L * r ∂μ := by
      apply integral_mono_ae hw.integrableOn (integrable_const _)
      filter_upwards [ae_restrict_mem hs, ae_restrict_of_ae hbound] with x hx hb
      exact hb.trans (mul_le_mul_of_nonneg_left hx hL)
    _ = μ.real {x | ρ x ≤ r} * (L * r) := by rw [setIntegral_const, smul_eq_mul]
    _ ≤ (C * r) * (L * r) := mul_le_mul_of_nonneg_right hlayer (mul_nonneg hL hr.le)
    _ = L * C * r ^ 2 := by cas

/-- Squaring the collar coordinate converts quadratic weighted sublevel growth
into the linear growth used by the inverse-square integral estimate. -/
theorem measureReal_withDensity_sq_sublevel_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {w ρ : α → ℝ} {C L r : ℝ}
    (hw : Integrable w μ) (hwpos : 0 ≤ᵐ[μ] w) (hL : 0 ≤ L) (hr : 0 < r)
    (hρ : Measurable ρ) (hbound : ∀ᵐ x ∂μ, w x ≤ L * ρ x)
    (hlayer : ∀ s > 0, μ.real {x | ρ x ≤ s} ≤ C * s) :
    (μ.withDensity (fun x ↦ ENNReal.ofReal (w x))).real {x | ρ x ^ 2 ≤ r} ≤
      L * C * r := by
  let : IsFiniteMeasure (μ.withDensity (fun x ↦ ENNReal.ofReal (w x))) :=
    isFiniteMeasure_withDensity_ofReal hw.hasFiniteIntegral
  calc
    (μ.withDensity (fun x ↦ ENNReal.ofReal (w x))).real {x | ρ x ^ 2 ≤ r} ≤
        (μ.withDensity (fun x ↦ ENNReal.ofReal (w x))).real
          {x | ρ x ≤ Real.sqrt r} :=
      measureReal_mono (fun x hx ↦ Real.le_sqrt_of_sq_le hx)
    _ ≤ L * C * (Real.sqrt r) ^ 2 :=
      measureReal_withDensity_sublevel_le hw hwpos hL (Real.sqrt_pos.mpr hr)
        hρ hbound (hlayer _ (Real.sqrt_pos.mpr hr))
    _ = L * C * r := by rw [Real.sq_sqrt hr.le]

end MeasureTheory
