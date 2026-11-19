/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.Average
public import PDE.Spaces.Sobolev.GraphSpace.Operators.ExponentRestriction
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Gradient
import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity
import PDE.Spaces.Sobolev.Inequalities.Poincare.Mean.ZeroGradient

/-!
# Subtracting the spatial mean in a Sobolev space

On a finite-measure domain, constant functions belong to `W¹ᵖ` for every `1 ≤ p ≤ ∞`.
Subtracting Mathlib's integral average preserves the weak gradient and makes the integral
zero. On a connected open domain these two conditions identify the zero Sobolev element.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}
  [IsFiniteMeasure (domainMeasure n Ω)]

/-- Constants have zero vector-valued weak gradient. -/
@[simp]
theorem wkpGradientCLM_constant (c : ℝ) :
    ∇ (wkpConstant (n := n) (p := p) (Ω := Ω) c) = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [wkpConstant_deriv_eq_zero, norm_zero, Finset.sum_const_zero] using
    wkpGradientCLM_norm_le_sum (wkpConstant (n := n) (p := p) (Ω := Ω) c)

/-- Integration of the base coordinate is a continuous linear functional on `W¹ᵖ`. -/
def wkpIntegralCLM : W^{1,p}(Ω) →L[ℝ] ℝ :=
  L1.integralCLM.comp
    ((wkpBaseCoordinateCLM (n := n) (m := 1) (p := 1) (Ω := Ω)).comp
      (lowerExponentOfFiniteMeasureCLM (Fact.out : 1 ≤ p)))

/-- The Sobolev integral functional is the Bochner integral of its base coordinate. -/
theorem wkpIntegralCLM_apply (U : W^{1,p}(Ω)) :
    wkpIntegralCLM U = ∫ x, wkpBaseCoordinateCLM U x ∂domainMeasure n Ω := by
  rw [wkpIntegralCLM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ← L1.integral_eq, L1.integral_eq_integral]
  exact integral_congr_ae
    (lowerExponentOfFiniteMeasure_apply_ae (Fact.out : 1 ≤ p) U (baseIndex n 1))

/-- Subtract the spatial integral average from a Sobolev element. -/
def subtractMean (U : W^{1,p}(Ω)) : W^{1,p}(Ω) :=
  U - wkpConstant (⨍ x, wkpBaseCoordinateCLM U x ∂domainMeasure n Ω)

/-- Mean subtraction represents the original function minus its spatial average. -/
theorem subtractMean_base_ae (U : W^{1,p}(Ω)) :
    (wkpBaseCoordinateCLM (subtractMean U) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦ wkpBaseCoordinateCLM U x -
        ⨍ y, wkpBaseCoordinateCLM U y ∂domainMeasure n Ω := by
  rw [subtractMean, map_sub]
  filter_upwards [Lp.coeFn_sub (wkpBaseCoordinateCLM U)
    (wkpBaseCoordinateCLM (wkpConstant (p := p) (Ω := Ω)
      (⨍ y, wkpBaseCoordinateCLM U y ∂domainMeasure n Ω))), wkpConstant_base_ae
    (p := p) (Ω := Ω) (⨍ y, wkpBaseCoordinateCLM U y ∂domainMeasure n Ω)] with x hx hc
  rw [hx, Pi.sub_apply, hc]

/-- Mean subtraction does not alter the weak gradient. -/
@[simp]
theorem wkpGradientCLM_subtractMean (U : W^{1,p}(Ω)) :
    ∇ (subtractMean U) = ∇ U := by
  simp [subtractMean]

/-- The mean-subtracted Sobolev element has integral zero, also when the domain is empty. -/
@[simp]
theorem wkpIntegralCLM_subtractMean (U : W^{1,p}(Ω)) :
    wkpIntegralCLM (subtractMean U) = 0 := by
  rw [wkpIntegralCLM_apply, integral_congr_ae (subtractMean_base_ae U)]
  exact integral_sub_average _ _

/-- On a connected open domain, a Sobolev element with zero integral and zero gradient is zero.
This identifies the kernel needed in the mean-subtracted Poincaré inequality. -/
theorem eq_zero_of_integral_eq_zero_of_gradient_eq_zero
    (hΩ : IsOpen Ω) (hconn : IsConnected Ω) (U : W^{1,p}(Ω))
    (hint : wkpIntegralCLM U = 0) (hgrad : ∇ U = 0) : U = 0 := by
  have hderiv (i : Fin n) :
      (U : WkpAmbientOn n 1 p Ω) (singleDerivIndex n i) = 0 := by
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa [hgrad] using norm_derivCoordinate_le_wkpGradientCLM U i)
      (norm_nonneg _)
  have hweak (i : Fin n) :
      HasWeakDerivativeOn Ω [i] (wkpBaseCoordinateCLM U) 0 := by
    have h := U.property.hasWeakDerivativeOn_first (by decide : 0 < 1) i
    simp only [firstDerivIndex_one, hderiv] at h
    exact (hasWeakDerivativeOn_congr_ae Filter.EventuallyEq.rfl
      (Lp.coeFn_zero ℝ p (domainMeasure n Ω))).mp h
  have hInt : IntegrableOn (wkpBaseCoordinateCLM U : ℝ^n → ℝ) Ω :=
    (Lp.memLp (wkpBaseCoordinateCLM U)).integrable (Fact.out : 1 ≤ p)
  obtain ⟨c, hc⟩ := exists_ae_eq_const_of_weak_gradient_zero hΩ hconn hInt hweak
  have hc0 : c = 0 := by
    rw [wkpIntegralCLM_apply, integral_congr_ae hc, integral_const] at hint
    have hμ : (domainMeasure n Ω).real univ ≠ 0 := by
      rw [measureReal_def, Measure.restrict_apply_univ]
      exact ENNReal.toReal_ne_zero.mpr
        ⟨(hΩ.measure_pos volume hconn.nonempty).ne', by
          simpa only [Measure.restrict_apply_univ] using
            measure_ne_top (domainMeasure n Ω) univ⟩
    exact (smul_eq_zero.mp hint).resolve_left hμ
  apply wkpBaseCoordinateCLM_injective hΩ
  rw [map_zero]
  apply Lp.ext
  have hzero : (wkpBaseCoordinateCLM U : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] 0 := by
    simpa only [hc0, Pi.zero_def] using hc
  exact hzero.trans (Lp.coeFn_zero ℝ p (domainMeasure n Ω)).symm

end SobolevSpace.GraphSpace
