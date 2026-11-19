/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Poincare.Mean.Centering
import PDE.Analysis.Normed.PiLp.CompareExp

/-!
# Mean subtraction and restriction of the Sobolev exponent

Lowering the exponent on a finite-measure domain preserves both the base function and its
spatial average. The vector-valued gradients agree almost everywhere, so Mathlib's
finite-measure `Lᵖ` comparison gives the corresponding gradient estimate, including `p = ∞`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

private theorem norm_le_of_ae_eq_lowerExponent
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} [IsFiniteMeasure μ] {p q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hqp : q ≤ p) (u : Lp E p μ) (v : Lp E q μ) (hvu : v =ᵐ[μ] u) :
    ‖v‖ ≤ (μ univ ^ (1 / q.toReal - 1 / p.toReal)).toReal * ‖u‖ := by
  have hraw : eLpNorm v q μ ≤ eLpNorm u p μ * μ univ ^
      (1 / q.toReal - 1 / p.toReal) := by
    rw [eLpNorm_congr_ae hvu]
    exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ hqp (Lp.aestronglyMeasurable u)
  have hfinite : eLpNorm u p μ * μ univ ^
      (1 / q.toReal - 1 / p.toReal) ≠ ∞ :=
    ENNReal.mul_ne_top (Lp.eLpNorm_ne_top u)
      (ENNReal.rpow_ne_top_of_nonneg (PiLp.exponentGap_nonneg hqp) (measure_ne_top μ univ))
  simpa only [Lp.norm_def, ENNReal.toReal_mul, mul_comm] using
    ENNReal.toReal_mono hfinite hraw

variable {n : ℕ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {Ω : Set (ℝ^n)}
  [IsFiniteMeasure (domainMeasure n Ω)]

/-- Lowering the exponent preserves the mean-subtracted base function almost everywhere. -/
theorem subtractMean_lowerExponent_base_ae (hqp : q ≤ p) (U : W^{1,p}(Ω)) :
    (wkpBaseCoordinateCLM
      (subtractMean (lowerExponentOfFiniteMeasureCLM hqp U)) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] wkpBaseCoordinateCLM (subtractMean U) := by
  have hb := lowerExponentOfFiniteMeasure_apply_ae hqp U (baseIndex n 1)
  have havg := average_congr hb
  filter_upwards [subtractMean_base_ae (lowerExponentOfFiniteMeasureCLM hqp U),
    subtractMean_base_ae U, hb] with x hlow hhigh hx
  rw [hlow, hhigh]
  exact congrArg₂ (· - ·) hx havg

/-- Exponent restriction preserves the vector-valued weak gradient almost everywhere. -/
theorem lowerExponent_gradient_ae (hqp : q ≤ p) (U : W^{1,p}(Ω)) :
    (∇ (lowerExponentOfFiniteMeasureCLM hqp U) : ℝ^n → ℝ^n)
      =ᵐ[domainMeasure n Ω] ∇ U := by
  have hrows : ∀ᵐ x ∂domainMeasure n Ω, ∀ i : Fin n,
      (lowerExponentOfFiniteMeasureCLM hqp U : WkpAmbientOn n 1 q Ω)
          (singleDerivIndex n i) x =
        (U : WkpAmbientOn n 1 p Ω) (singleDerivIndex n i) x :=
    ae_all_iff.mpr fun i ↦
      lowerExponentOfFiniteMeasure_apply_ae hqp U (singleDerivIndex n i)
  filter_upwards [wkpGradientCLM_apply_ae (lowerExponentOfFiniteMeasureCLM hqp U),
    wkpGradientCLM_apply_ae U, hrows] with x hlo hhi hrow
  ext i
  rw [hlo, hhi, hrow]

/-- The gradient obeys the usual finite-measure exponent comparison. The source exponent
may be infinity; the real reciprocal of that exponent is then zero. -/
theorem norm_lowerExponent_gradient_le (hqp : q ≤ p) (U : W^{1,p}(Ω)) :
    ‖∇ (lowerExponentOfFiniteMeasureCLM hqp U)‖ ≤
      ((domainMeasure n Ω) univ ^ (1 / q.toReal - 1 / p.toReal)).toReal *
        ‖∇ U‖ :=
  norm_le_of_ae_eq_lowerExponent hqp _ _ (lowerExponent_gradient_ae hqp U)

end SobolevSpace.GraphSpace
