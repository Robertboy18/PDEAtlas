/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.FirstDerivative
public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarGradientVector
import CAS.ExactTactic

/-!
# Quantitative planar half-space Green gradient bounds

The Green gradient is a vector integral against the canonical odd source.
A bound near the observation point controls the singular disk by `Mρ`.
The complement retains its distance weight; a coarser global estimate uses
the source's half-plane mass. These estimates also hold on the boundary.

## Main results

* `norm_oddHalfSpaceExtension_le`: a bound on the source on the upper half-plane bounds its odd
  extension everywhere.
* `integral_norm_oddHalfSpaceExtension`: the odd extension has twice the half-plane mass of the
  source.
* `gradient_halfSpaceGreenPotential_eq_integral`: the Green gradient equals its absolutely
  convergent vector-kernel integral, also at boundary points.
* `norm_gradient_halfSpaceGreenPotential_le_near_add_far`: a local source bound gives a gradient
  bound by `Mρ` plus the inverse-distance integral outside the singular disk.
* `norm_gradient_halfSpaceGreenPotential_le_mass`: a uniform source bound and the half-plane
  mass bound the gradient at every point, for any positive splitting radius.
-/

@[expose] public section

noncomputable section

namespace GreenFunction

open MeasureTheory Filter Set SobolevSpace
open scoped Convolution Gradient

/-- The odd extension's norm is the sum of the two reflected norm indicators.
Their supports are disjoint, so taking the norm loses no factor. -/
theorem norm_oddHalfSpaceExtension (f : ℝ^2 → ℝ) (y : ℝ^2) :
    ‖oddHalfSpaceExtension f y‖ =
      (HalfSpace.upper 2).indicator (fun z ↦ ‖f z‖) y +
      (HalfSpace.lower 2).indicator (fun z ↦ ‖f (HalfSpace.reflect 2 z)‖) y := by
  by_cases hu : y ∈ HalfSpace.upper 2
  · have hl : y ∉ HalfSpace.lower 2 := by
      change ¬y 1 < 0
      exact not_lt_of_gt (show 0 < y 1 from hu)
    simp [oddHalfSpaceExtension, hu, hl]
  · by_cases hl : y ∈ HalfSpace.lower 2 <;> simp [oddHalfSpaceExtension, hu, hl]

/-- A bound on the upper half-plane source bounds its odd extension everywhere. -/
theorem norm_oddHalfSpaceExtension_le
    {f : ℝ^2 → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ y ∈ HalfSpace.upper 2, ‖f y‖ ≤ M) (y : ℝ^2) :
    ‖oddHalfSpaceExtension f y‖ ≤ M := by
  rw [norm_oddHalfSpaceExtension]
  by_cases hu : y ∈ HalfSpace.upper 2
  · have hl : y ∉ HalfSpace.lower 2 := by
      change ¬y 1 < 0
      exact not_lt_of_gt (show 0 < y 1 from hu)
    simpa only [indicator_of_mem hu, indicator_of_notMem hl, add_zero] using hbound y hu
  · by_cases hl : y ∈ HalfSpace.lower 2
    · simpa only [indicator_of_notMem hu, indicator_of_mem hl, zero_add] using
        hbound (HalfSpace.reflect 2 y) ((HalfSpace.mem_upper_reflect_iff 2 y).mpr hl)
    · simpa only [indicator_of_notMem hu, indicator_of_notMem hl, add_zero] using hM

/-- The odd extension of a continuous compact source is integrable even if
it jumps across the horizontal boundary. -/
theorem integrable_oddHalfSpaceExtension
    {f : ℝ^2 → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable (oddHalfSpaceExtension f) := by
  exact (integrableOn_iff_integrable_of_support_subset
    (subset_tsupport (oddHalfSpaceExtension f))).mp
      ((locallyIntegrable_oddHalfSpaceExtension hf).integrableOn_isCompact
        (hasCompactSupport_oddHalfSpaceExtension hc))

/-- Reflection doubles the half-plane source mass in the canonical odd extension. -/
theorem integral_norm_oddHalfSpaceExtension
    {f : ℝ^2 → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    (∫ y, ‖oddHalfSpaceExtension f y‖) = 2 * ∫ y in HalfSpace.upper 2, ‖f y‖ := by
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hc
  have href : Integrable (fun y ↦ ‖f (HalfSpace.reflect 2 y)‖) :=
    ((HalfSpace.measurePreserving_reflect (n := 2)).integrable_comp
      hfi.norm.aestronglyMeasurable).mpr hfi.norm
  simp_rw [norm_oddHalfSpaceExtension]
  rw [integral_add (hfi.norm.indicator (HalfSpace.measurableSet_upper 2))
    (href.indicator (HalfSpace.measurableSet_lower 2)),
    integral_indicator (HalfSpace.measurableSet_upper 2),
    integral_indicator (HalfSpace.measurableSet_lower 2)]
  rw [(HalfSpace.measurePreserving_reflect_restrict_lower 2).integral_comp
    (HalfSpace.reflectLinearIsometryEquiv 2).toMeasurableEquiv.measurableEmbedding
    (fun y ↦ ‖f y‖)]
  ring

/-- The Green gradient's vector integrand is absolutely integrable at every
observation point, including boundary points. -/
theorem integrable_oddHalfSpaceExtension_smul_gradientKernelVector
    {f : ℝ^2 → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) (x : ℝ^2) :
    Integrable (fun z ↦ oddHalfSpaceExtension f (x - z) •
      PotentialTheory.Planar.gradientKernelVector z) := by
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hc
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0)
  apply PotentialTheory.Planar.integrable_smul_gradientKernelVector
    ((integrable_oddHalfSpaceExtension hf hc).comp_sub_left x) (ρ := 1) (by norm_num)
    (M := M)
  filter_upwards [] with z
  exact norm_oddHalfSpaceExtension_le hM0 (fun y _ ↦ hM y) (x - z)

/-- The classical Green gradient equals its absolutely convergent vector-kernel integral. -/
theorem gradient_halfSpaceGreenPotential_eq_integral
    {f : ℝ^2 → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) (x : ℝ^2) :
    ∇ (halfSpaceGreenPotential f) x =
      ∫ z, oddHalfSpaceExtension f (x - z) • PotentialTheory.Planar.gradientKernelVector z := by
  have hi := integrable_oddHalfSpaceExtension_smul_gradientKernelVector hf hc x
  ext i
  rw [PDE.gradient_apply_eq_partialDeriv]
  unfold PDE.partialDeriv
  rw [(hasFDerivAt_halfSpaceGreenPotential hf hc x).fderiv]
  simp only [innerSL_apply_apply, EuclideanSpace.inner_single_right,
    starRingEnd_apply, star_trivial, one_mul]
  change (PotentialTheory.Planar.gradientKernel i ⋆[ContinuousLinearMap.mul ℝ ℝ]
    oddHalfSpaceExtension f) x = (EuclideanSpace.proj i) (∫ z,
      oddHalfSpaceExtension f (x - z) • PotentialTheory.Planar.gradientKernelVector z)
  rw [← (EuclideanSpace.proj i).integral_comp_comm hi]
  simp only [convolution, ContinuousLinearMap.mul_apply', EuclideanSpace.coe_proj,
    PiLp.smul_apply, smul_eq_mul, PotentialTheory.Planar.gradientKernelVector_apply, mul_comm]

/-- A local source bound gives a Green gradient bound that retains the
inverse-distance integral on the complement of the singular disk. -/
theorem norm_gradient_halfSpaceGreenPotential_le_near_add_far
    {f : ℝ^2 → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    (x : ℝ^2) {ρ M : ℝ} (hρ : 0 < ρ)
    (hbound : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℝ^2) ρ),
      ‖oddHalfSpaceExtension f (x - z)‖ ≤ M) :
    ‖∇ (halfSpaceGreenPotential f) x‖ ≤ M * ρ +
      (1 / (2 * Real.pi)) * ∫ z in (Metric.ball (0 : ℝ^2) ρ)ᶜ,
        ‖oddHalfSpaceExtension f (x - z)‖ / ‖z‖ := by
  rw [gradient_halfSpaceGreenPotential_eq_integral hf hc]
  exact PotentialTheory.Planar.norm_integral_smul_gradientKernelVector_le_near_add_far
    ((integrable_oddHalfSpaceExtension hf hc).comp_sub_left x) hρ hbound

/-- A uniform source bound and half-plane source mass control the Green gradient
at every point of the plane, for any positive splitting radius. -/
theorem norm_gradient_halfSpaceGreenPotential_le_mass
    {f : ℝ^2 → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ y ∈ HalfSpace.upper 2, ‖f y‖ ≤ M)
    (x : ℝ^2) {ρ : ℝ} (hρ : 0 < ρ) :
    ‖∇ (halfSpaceGreenPotential f) x‖ ≤
      M * ρ + (∫ y in HalfSpace.upper 2, ‖f y‖) / (Real.pi * ρ) := by
  rw [gradient_halfSpaceGreenPotential_eq_integral hf hc]
  have hlocal : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℝ^2) ρ),
      ‖oddHalfSpaceExtension f (x - z)‖ ≤ M :=
    Eventually.of_forall fun z ↦ norm_oddHalfSpaceExtension_le hM hbound (x - z)
  have h := PotentialTheory.Planar.norm_integral_smul_gradientKernelVector_le_mass
    ((integrable_oddHalfSpaceExtension hf hc).comp_sub_left x) hρ hlocal
  rw [integral_sub_left_eq_self (fun y ↦ ‖oddHalfSpaceExtension f y‖) volume x,
    integral_norm_oddHalfSpaceExtension hf hc] at h
  convert h using 1
  cas

end GreenFunction
