/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.WeightedL2.IntegralBound
public import PDE.Spaces.Sobolev.Inequalities.Morrey.FiniteExponent.OneDimensional.WeakBound

/-!
# Weighted increments for a weak derivative

The weak fundamental theorem of calculus and weighted Cauchy–Schwarz
bound an increment by the derivative energy and the primitive of the
reciprocal weight. Positivity is needed only on the integration interval.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Analysis

namespace MeasureTheory

/-- The reciprocal-weight primitive controls increments of a continuous function
with a global weak derivative by its finite weighted derivative energy. -/
theorem abs_sub_zero_le_weighted_weak_derivative_energy
    {ω η σ : ℝ → ℝ} {L x : ℝ}
    (hweak : PDE.Analysis.Evolution.HasWeakTimeDerivativeOn univ ω η)
    (hω : Continuous ω) (hx : x ∈ Ioo 0 L)
    (hσ : AEStronglyMeasurable σ (volume.restrict (Ioo 0 L)))
    (hσpos : ∀ y ∈ Ioo 0 L, 0 < σ y)
    (hinverse : IntegrableOn (fun y ↦ 1 / σ y) (Ioo 0 L))
    (henergy : IntegrableOn (fun y ↦ η y ^ 2 * σ y) (Ioo 0 L)) :
    |ω x - ω 0| ≤ √(∫ y in Ioo 0 x, 1 / σ y) *
      √(∫ y in Ioo 0 L, η y ^ 2 * σ y) := by
  have hsub : Ioo (0 : ℝ) x ⊆ Ioo 0 L :=
    Ioo_subset_Ioo le_rfl hx.2.le
  have hσx := hσ.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hpos : ∀ᵐ y ∂volume.restrict (Ioo 0 x), 0 < σ y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact hσpos y (hsub hy)
  have hη := (locallyIntegrableOn_univ.mp hweak.locallyIntegrable_g).aestronglyMeasurable
  have hcs := abs_integral_le_weighted_sqrt hη.restrict hσx hpos
    (hinverse.mono_set hsub) (henergy.mono_set hsub)
  have hftc : (∫ y in Ioo 0 x, η y) = ω x - ω 0 := by
    rw [← hweak.intervalIntegral_eq_sub hω 0 x,
      intervalIntegral.integral_of_le hx.1.le, integral_Ioc_eq_integral_Ioo]
  rw [hftc] at hcs
  refine hcs.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_)
    (Real.sqrt_nonneg _))
  apply setIntegral_mono_set henergy ?_ (Filter.Eventually.of_forall hsub)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  exact mul_nonneg (sq_nonneg _) (hσpos y hy).le

end MeasureTheory
