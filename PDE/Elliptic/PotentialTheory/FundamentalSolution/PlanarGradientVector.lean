/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Integral.PlanarInverseRadius
public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarGradient
import CAS.ExactTactic

/-!
# The vector-valued planar gradient kernel

The exact Euclidean norm of the logarithmic gradient kernel is `1/(2π|z|)`.
Taking the norm of the vector integral preserves this constant in the local
and far-field estimates.

## Main definitions

* `gradientKernelVector`: the vector gradient of the planar logarithmic kernel, zero at the pole.

## Main results

* `norm_gradientKernelVector`: the vector kernel has norm exactly `1/(2π|z|)`.
* `integrable_smul_gradientKernelVector`: a locally bounded integrable density gives an absolutely
  convergent vector gradient-kernel integral.
* `norm_integral_smul_gradientKernelVector_le`: the vector integral is bounded by its exact
  inverse-radius majorant.
* `norm_integral_smul_gradientKernelVector_le_near_add_far`: a local source bound contributes
  `Mρ`, and the complement keeps its inverse-distance weight.
* `norm_integral_smul_gradientKernelVector_le_mass`: the local source bound and the total source
  mass give a global bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace PotentialTheory.Planar

/-- The vector gradient of the planar logarithmic kernel, assigned zero at the pole. -/
def gradientKernelVector (z : ℝ^2) : ℝ^2 :=
  -(1 / (2 * Real.pi * ‖z‖ ^ 2)) • z

/-- Each coordinate of the vector kernel is the existing Cartesian gradient kernel. -/
theorem gradientKernelVector_apply (i : Fin 2) (z : ℝ^2) :
    gradientKernelVector z i = gradientKernel i z := by
  rw [gradientKernel_eq_div]
  change -(1 / (2 * Real.pi * ‖z‖ ^ 2)) * z i =
    -(1 / (2 * Real.pi)) * z i / ‖z‖ ^ 2
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The full vector kernel has exactly inverse-radius norm, with no loss
from estimating its coordinates separately. -/
theorem norm_gradientKernelVector (z : ℝ^2) :
    ‖gradientKernelVector z‖ = (1 / (2 * Real.pi)) * ‖z‖⁻¹ := by
  rw [gradientKernelVector, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.pi * ‖z‖ ^ 2))]
  by_cases hz : z = 0
  · subst z
    simp
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  field_simp

/-- The vector kernel is measurable, including its assigned value at the pole. -/
theorem measurable_gradientKernelVector : Measurable gradientKernelVector := by
  unfold gradientKernelVector
  fun_prop

/-- A locally bounded integrable density gives an absolutely convergent vector
gradient-kernel integral. -/
theorem integrable_smul_gradientKernelVector
    {h : ℝ^2 → ℝ} (hh : Integrable h) {ρ M : ℝ} (hρ : 0 < ρ)
    (hbound : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℝ^2) ρ), ‖h z‖ ≤ M) :
    Integrable (fun z ↦ h z • gradientKernelVector z) := by
  apply ((integrable_norm_div_norm_two hh hρ hbound).const_mul
    (1 / (2 * Real.pi))).mono'
    (hh.aestronglyMeasurable.smul measurable_gradientKernelVector.aestronglyMeasurable)
  filter_upwards [] with z
  change ‖h z • gradientKernelVector z‖ ≤ (1 / (2 * Real.pi)) * (‖h z‖ / ‖z‖)
  simp only [norm_smul, norm_gradientKernelVector, div_eq_mul_inv]
  exact le_of_eq (by ring)

/-- The vector gradient integral is bounded by its exact inverse-radius majorant. -/
theorem norm_integral_smul_gradientKernelVector_le
    {h : ℝ^2 → ℝ} (hh : Integrable h) {ρ M : ℝ} (hρ : 0 < ρ)
    (hbound : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℝ^2) ρ), ‖h z‖ ≤ M) :
    ‖∫ z, h z • gradientKernelVector z‖ ≤
      (1 / (2 * Real.pi)) * ∫ z, ‖h z‖ / ‖z‖ := by
  have hmajorant := (integrable_norm_div_norm_two hh hρ hbound).const_mul
    (1 / (2 * Real.pi))
  have hnorm : ∀ᵐ z ∂volume, ‖h z • gradientKernelVector z‖ ≤
      (1 / (2 * Real.pi)) * (‖h z‖ / ‖z‖) := by
    filter_upwards [] with z
    simp only [norm_smul, norm_gradientKernelVector, div_eq_mul_inv]
    exact le_of_eq (by ring)
  simpa only [integral_const_mul] using norm_integral_le_of_norm_le hmajorant hnorm

/-- A local source bound contributes `Mρ`; the complement retains its inverse-distance
weight for subsequent subdivision. -/
theorem norm_integral_smul_gradientKernelVector_le_near_add_far
    {h : ℝ^2 → ℝ} (hh : Integrable h) {ρ M : ℝ} (hρ : 0 < ρ)
    (hbound : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℝ^2) ρ), ‖h z‖ ≤ M) :
    ‖∫ z, h z • gradientKernelVector z‖ ≤ M * ρ +
      (1 / (2 * Real.pi)) *
        ∫ z in (Metric.ball (0 : ℝ^2) ρ)ᶜ, ‖h z‖ / ‖z‖ := by
  apply (norm_integral_smul_gradientKernelVector_le hh hρ hbound).trans
  calc
    _ ≤ (1 / (2 * Real.pi)) * (2 * Real.pi * M * ρ +
        ∫ z in (Metric.ball (0 : ℝ^2) ρ)ᶜ, ‖h z‖ / ‖z‖) :=
      mul_le_mul_of_nonneg_left (integral_norm_div_norm_two_le_near_add_far hh hρ hbound)
        (by positivity)
    _ = _ := by cas

/-- The local source bound and total source mass give a global vector-kernel bound. -/
theorem norm_integral_smul_gradientKernelVector_le_mass
    {h : ℝ^2 → ℝ} (hh : Integrable h) {ρ M : ℝ} (hρ : 0 < ρ)
    (hbound : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℝ^2) ρ), ‖h z‖ ≤ M) :
    ‖∫ z, h z • gradientKernelVector z‖ ≤
      M * ρ + (∫ z, ‖h z‖) / (2 * Real.pi * ρ) := by
  apply (norm_integral_smul_gradientKernelVector_le hh hρ hbound).trans
  calc
    _ ≤ (1 / (2 * Real.pi)) * (2 * Real.pi * M * ρ + (∫ z, ‖h z‖) / ρ) :=
      mul_le_mul_of_nonneg_left (integral_norm_div_norm_two_le hh hρ hbound) (by positivity)
    _ = _ := by cas

end PotentialTheory.Planar
