/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.WeightedL2.Increment
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Weighted increments from interior regularity

The segment from the origin to an interior point lies entirely in the
smooth region. Weighted Cauchy–Schwarz therefore controls the increment
even when the compact extension has a corner at the edge of its support.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace MeasureTheory

/-- Interior `C¹` regularity across the origin suffices for the weighted FTC
bound at every point strictly inside the support interval. -/
theorem abs_sub_zero_le_weighted_derivative_energy_of_contDiffOn
    {q σ : ℝ → ℝ} {L x : ℝ}
    (hq : ContDiffOn ℝ 1 q (Ioo (-L) L)) (hx : x ∈ Ioo 0 L)
    (hσ : AEStronglyMeasurable σ (volume.restrict (Ioo 0 L)))
    (hσpos : ∀ y ∈ Ioo 0 L, 0 < σ y)
    (hinverse : IntegrableOn (fun y ↦ 1 / σ y) (Ioo 0 L))
    (henergy : IntegrableOn (fun y ↦ deriv q y ^ 2 * σ y) (Ioo 0 L)) :
    |q x - q 0| ≤ √(∫ y in Ioo 0 x, 1 / σ y) *
      √(∫ y in Ioo 0 L, deriv q y ^ 2 * σ y) := by
  have hsub : Ioo (0 : ℝ) x ⊆ Ioo 0 L := Ioo_subset_Ioo le_rfl hx.2.le
  have hσx := hσ.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hpos : ∀ᵐ y ∂volume.restrict (Ioo 0 x), 0 < σ y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact hσpos y (hsub hy)
  have hcs := abs_integral_le_weighted_sqrt
    (measurable_deriv q).aestronglyMeasurable hσx hpos
    (hinverse.mono_set hsub) (henergy.mono_set hsub)
  have hi : Icc (0 : ℝ) x ⊆ Ioo (-L) L := by
    intro y hy
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hftc : (∫ y in Ioo 0 x, deriv q y) = q x - q 0 := by
    have hc := (hq.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono hi
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y hy ↦ ((hq.contDiffAt (isOpen_Ioo.mem_nhds
        (hi (by simpa only [uIcc_of_le hx.1.le] using hy)))).differentiableAt
          one_ne_zero).hasDerivAt)
      (hc.intervalIntegrable_of_Icc hx.1.le)
    rwa [intervalIntegral.integral_of_le hx.1.le, integral_Ioc_eq_integral_Ioo] at h
  rw [hftc] at hcs
  refine hcs.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_)
    (Real.sqrt_nonneg _))
  apply setIntegral_mono_set henergy ?_ (Eventually.of_forall hsub)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  exact mul_nonneg (sq_nonneg _) (hσpos y hy).le

end MeasureTheory
