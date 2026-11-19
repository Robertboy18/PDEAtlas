/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.ScaleDerivative.Profiles
import PDE.Analysis.Calculus.IntegrationByParts.CompactSupport

/-!
# Cancellation of mollifier derivative profiles

Compact-support integration by parts gives zero mass for each spatial profile.
The same identity with a coordinate multiplier gives mass `-1` for
`z_i * ∂[i] ρ(z)`. Summing over coordinates proves cancellation of the scale
profile, including dimension zero, where the sum is empty.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace SobolevSpace.Approximation.Mollifier

variable {n : ℕ}

/-- Every spatial derivative profile has zero integral. -/
theorem integral_spatialDerivativeProfile (μ : Mollifier n) (i : Fin n) :
    (∫ z, μ.spatialDerivativeProfile i z) = 0 :=
  PDE.integral_fderiv_eq_zero_of_hasCompactSupport (μ.smooth.of_le (by simp))
    μ.compactSupport (EuclideanSpace.single i 1)

private theorem integrable_coordinate_mul_spatialDerivativeProfile
    (μ : Mollifier n) (i : Fin n) :
    Integrable (fun z : ℝ^n ↦ z i * μ.spatialDerivativeProfile i z) :=
  ((EuclideanSpace.proj i).continuous.mul
    (μ.contDiff_spatialDerivativeProfile i).continuous).integrable_of_hasCompactSupport
      (μ.hasCompactSupport_spatialDerivativeProfile i).mul_left

/-- The first coordinate moment of its corresponding derivative profile is minus one. -/
theorem integral_coordinate_mul_spatialDerivativeProfile (μ : Mollifier n) (i : Fin n) :
    (∫ z : ℝ^n, z i * μ.spatialDerivativeProfile i z) = -1 := by
  have hρ : Integrable μ.ρ :=
    μ.smooth.continuous.integrable_of_hasCompactSupport μ.compactSupport
  have hcoord : Differentiable ℝ (fun z : ℝ^n ↦ z i) :=
    (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).differentiable
  have hcoordD (z : ℝ^n) :
      fderiv ℝ (fun y : ℝ^n ↦ y i) z (EuclideanSpace.single i 1) = 1 := by
    change (∂[i] (fun y : ℝ^n ↦ y i)) z = 1
    simp [PDE.partialDeriv_coord]
  have hfg : Integrable (fun z : ℝ^n ↦ z i * μ.ρ z) :=
    ((EuclideanSpace.proj i).continuous.mul μ.smooth.continuous).integrable_of_hasCompactSupport
      μ.compactSupport.mul_left
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := fun z : ℝ^n ↦ z i) (g := μ.ρ)
    (v := EuclideanSpace.single i 1)
    (by simpa only [hcoordD, one_mul] using hρ)
    (μ.integrable_coordinate_mul_spatialDerivativeProfile i) hfg
    (fun z _ ↦ hcoord z) (fun z _ ↦ μ.smooth.differentiable (by simp) z)
  change (∫ z : ℝ^n, z i * fderiv ℝ μ.ρ z (EuclideanSpace.single i 1)) = -1
  simpa only [hcoordD, one_mul, μ.integral_one] using h

/-- Every scale derivative profile has zero integral. -/
theorem integral_normalDerivativeProfile (μ : Mollifier n) :
    (∫ z, μ.normalDerivativeProfile z) = 0 := by
  have hρ : Integrable μ.ρ :=
    μ.smooth.continuous.integrable_of_hasCompactSupport μ.compactSupport
  have hD : (fun z : ℝ^n ↦ fderiv ℝ μ.ρ z z) =
      fun z ↦ ∑ i : Fin n, z i * μ.spatialDerivativeProfile i z := by
    funext z
    simpa only [smul_eq_mul, spatialDerivativeProfile] using
      PDE.fderiv_apply_eq_sum_smul_partialDeriv μ.ρ z z
  have hDi : Integrable (fun z : ℝ^n ↦ fderiv ℝ μ.ρ z z) := by
    rw [hD]
    exact integrable_finsetSum _ fun i _ ↦ μ.integrable_coordinate_mul_spatialDerivativeProfile i
  change (∫ z, -(n : ℝ) * μ.ρ z - fderiv ℝ μ.ρ z z) = 0
  rw [integral_sub (hρ.const_mul _) hDi, integral_const_mul, μ.integral_one, hD,
    integral_finsetSum _ (fun i _ ↦ μ.integrable_coordinate_mul_spatialDerivativeProfile i)]
  simp [μ.integral_coordinate_mul_spatialDerivativeProfile]

end SobolevSpace.Approximation.Mollifier
