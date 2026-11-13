/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.WeightedL2.IntegralBound
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Weighted control of increments from a finite derivative energy

The fundamental theorem of calculus and weighted Cauchy–Schwarz give the
reciprocal-weight primitive as the exact coefficient of the derivative norm.
The weight is required to be positive only on the integration interval.
-/

@[expose] public section

noncomputable section

open Set

namespace MeasureTheory

/-- The reciprocal-weight primitive controls the increment of a C¹ function
by its finite weighted derivative energy. -/
theorem abs_sub_zero_le_weighted_derivative_energy
    {ω σ : ℝ → ℝ} {L x : ℝ} (hω : ContDiff ℝ 1 ω) (hx : x ∈ Ioo 0 L)
    (hσ : AEStronglyMeasurable σ (volume.restrict (Ioo 0 L)))
    (hσpos : ∀ y ∈ Ioo 0 L, 0 < σ y)
    (hinverse : IntegrableOn (fun y ↦ 1 / σ y) (Ioo 0 L))
    (henergy : IntegrableOn (fun y ↦ deriv ω y ^ 2 * σ y) (Ioo 0 L)) :
    |ω x - ω 0| ≤ √(∫ y in Ioo 0 x, 1 / σ y) *
      √(∫ y in Ioo 0 L, deriv ω y ^ 2 * σ y) := by
  have hsub : Ioo (0 : ℝ) x ⊆ Ioo 0 L :=
    Ioo_subset_Ioo le_rfl hx.2.le
  have hσx := hσ.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hpos : ∀ᵐ y ∂volume.restrict (Ioo 0 x), 0 < σ y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact hσpos y (hsub hy)
  have hcs := abs_integral_le_weighted_sqrt
    (measurable_deriv ω).aestronglyMeasurable hσx hpos
    (hinverse.mono_set hsub) (henergy.mono_set hsub)
  have hftc : (∫ y in Ioo 0 x, deriv ω y) = ω x - ω 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ ↦ (hω.differentiable one_ne_zero y).hasDerivAt)
      (hω.continuous_deriv_one.intervalIntegrable 0 x)
    rwa [intervalIntegral.integral_of_le hx.1.le, integral_Ioc_eq_integral_Ioo] at h
  rw [hftc] at hcs
  refine hcs.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_)
    (Real.sqrt_nonneg _))
  apply setIntegral_mono_set henergy ?_ (Filter.Eventually.of_forall hsub)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  exact mul_nonneg (sq_nonneg _) (hσpos y hy).le

end MeasureTheory
