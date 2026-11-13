/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import PDE.Solution.Singularity.FiniteTime.Norm.SpatialSupremum

/-!
# Weighted spatial moments

A weighted moment of a scalar field is bounded by its spatial supremum norm times the
total mass of the weight. The spatial
type and measure are arbitrary; Euclidean structure enters only in model-specific choices of
weight. The estimate records the total mass of a nonnegative integrable weight in `ℝ≥0∞`. The
ambient measure may be infinite, as for Lebesgue measure. The field itself need not be measurable
globally: integrability of the weighted field is assumed at the times where the estimate is used.

The resulting bound transfers divergence of any positive-mass weighted moment to divergence of
`spatialSupNorm`; the weight need not have mass one. Moment methods for finite-time blow-up use
this step.
-/

@[expose] public section

namespace PDE.Solution.Singularity.FiniteTime

open Filter MeasureTheory Topology
open scoped ENNReal

/-- The spatial moment of `u` against the density `weight` and measure `μ` at time `t`. -/
noncomputable def weightedSpatialMoment {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (weight : X → ℝ) (u : X → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x, weight x * u x t ∂μ

/-- Against a nonnegative weight, the absolute moment is bounded by the extended spatial
supremum times the weight's mass.

Integrability of the weighted field is kept explicit because no measurability assumption is
imposed on `u`, and because Mathlib's Bochner integral is zero for a nonintegrable function. -/
theorem ofReal_abs_weighted_spatial_moment_le_spatial_sup_norm_mul_mass
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {weight : X → ℝ}
    {u : X → ℝ → ℝ} {t : ℝ}
    (hweight_nonneg : 0 ≤ᵐ[μ] weight)
    (hweight_integrable : Integrable weight μ)
    (hfield_integrable : Integrable (fun x ↦ weight x * u x t) μ) :
    ENNReal.ofReal |weightedSpatialMoment μ weight u t| ≤
      spatialSupNorm u t * ENNReal.ofReal (∫ x, weight x ∂μ) := by
  unfold weightedSpatialMoment
  calc
    ENNReal.ofReal |∫ x, weight x * u x t ∂μ|
        ≤ ENNReal.ofReal (∫ x, |weight x * u x t| ∂μ) :=
      ENNReal.ofReal_le_ofReal abs_integral_le_integral_abs
    _ = ∫⁻ x, ‖weight x * u x t‖ₑ ∂μ := by
      simpa only [Real.norm_eq_abs] using
        ofReal_integral_norm_eq_lintegral_enorm hfield_integrable
    _ ≤ ∫⁻ x, spatialSupNorm u t * ENNReal.ofReal (weight x) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hweight_nonneg] with x hx
      rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg hx,
        ENNReal.ofReal_mul hx]
      calc
        ENNReal.ofReal (weight x) * ENNReal.ofReal |u x t|
            ≤ ENNReal.ofReal (weight x) * spatialSupNorm u t := by
          gcongr
          simpa only [Real.norm_eq_abs] using
            ofReal_norm_le_spatial_sup_norm u t x
        _ = spatialSupNorm u t * ENNReal.ofReal (weight x) := mul_comm _ _
    _ = spatialSupNorm u t * ∫⁻ x, ENNReal.ofReal (weight x) ∂μ := by
      rw [lintegral_const_mul''
        (spatialSupNorm u t) hweight_integrable.aemeasurable.ennreal_ofReal]
    _ = spatialSupNorm u t * ENNReal.ofReal (∫ x, weight x ∂μ) := by
      rw [ofReal_integral_eq_lintegral_ofReal hweight_integrable hweight_nonneg]

/-- Divergence of an absolute weighted moment against a nonnegative positive-mass weight forces
the extended spatial supremum to tend to `⊤`.

The proof divides the moment estimate by the positive weight mass. The extended supremum allows
this divergence statement without boundedness of the spatial slices. Finite-time blow-up also
requires eventual finiteness of those slices. -/
theorem tendsto_spatial_sup_norm_nhds_top_of_abs_weighted_spatial_moment
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {weight : X → ℝ} {u : X → ℝ → ℝ} {l : Filter ℝ}
    (hweight_nonneg : 0 ≤ᵐ[μ] weight)
    (hweight_integrable : Integrable weight μ)
    (hweight_mass_pos : 0 < ∫ x, weight x ∂μ)
    (hfield_integrable : ∀ᶠ t in l, Integrable (fun x ↦ weight x * u x t) μ)
    (hmoment :
      Tendsto (fun t ↦ |weightedSpatialMoment μ weight u t|) l atTop) :
    Tendsto (spatialSupNorm u) l (nhds ⊤) := by
  exact tendsto_nhds_top_mono
    (ENNReal.tendsto_ofReal_nhds_top.mpr
      (Filter.Tendsto.atTop_div_const hweight_mass_pos hmoment))
    (by
      filter_upwards [hfield_integrable] with t ht
      rw [ENNReal.ofReal_div_of_pos hweight_mass_pos]
      exact ENNReal.div_le_of_le_mul <|
        ofReal_abs_weighted_spatial_moment_le_spatial_sup_norm_mul_mass
          hweight_nonneg hweight_integrable ht)

end PDE.Solution.Singularity.FiniteTime
