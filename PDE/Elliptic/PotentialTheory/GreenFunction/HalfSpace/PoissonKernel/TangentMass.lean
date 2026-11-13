/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.PoissonKernel.Normalization
public import PDE.Analysis.InnerProductSpace.RadialIntegral

/-!
# Poisson mass in physical tangent coordinates

The flat paired normal kernel has vector mass equal to its unit normal. The tangent
parametrization can be any injective linear map orthogonal to that normal. Its metric
determinant is retained, so the formula applies to derivatives of general C¹ charts.
The identity concerns a flat plane.
-/

@[expose] public noncomputable section

namespace GreenFunction

open MeasureTheory PDE.Analysis
open scoped InnerProductSpace

variable {n : ℕ} [Fact (0 < n)]

/-- The half-space distance separates squared height and squared tangential length. -/
theorem dist_smul_eLast_halfSpaceEmb_eq_sqrt (t : ℝ) (v : ℝ^(n - 1)) :
    dist (t • eLast (n := n)) (halfSpaceEmb (n := n) v) =
      Real.sqrt (t ^ 2 + ‖v‖ ^ 2) := by
  have hsq : dist (t • eLast (n := n)) (halfSpaceEmb (n := n) v) ^ 2 =
      t ^ 2 + ‖v‖ ^ 2 := by
    rw [dist_eq_norm, norm_sub_sq_real, norm_smul, norm_halfSpaceEmb,
      real_inner_smul_left]
    have hn : ‖eLast (n := n)‖ = 1 := by simp [eLast]
    have hi : inner ℝ (eLast (n := n)) (halfSpaceEmb (n := n) v) = 0 := by
      simp [eLast, EuclideanSpace.inner_single_left, lastCoord_halfSpaceEmb]
    rw [hn, hi, mul_one, Real.norm_eq_abs, sq_abs]
    ring
  rw [← hsq, Real.sqrt_sq (dist_nonneg : 0 ≤ dist _ _)]

omit [Fact (0 < n)] in
/-- A unit normal orthogonal to the tangent map gives the same radial distance formula. -/
theorem norm_smul_normal_sub_eq_sqrt (T : ℝ^(n - 1) →ₗ[ℝ] ℝ^n)
    (ν : ℝ^n) (hν : ‖ν‖ = 1) (horth : ∀ v, inner ℝ ν (T v) = 0)
    (t : ℝ) (v : ℝ^(n - 1)) :
    ‖t • ν - T v‖ = Real.sqrt (t ^ 2 + ‖T v‖ ^ 2) := by
  have hsq : ‖t • ν - T v‖ ^ 2 = t ^ 2 + ‖T v‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, real_inner_smul_left, hν, horth,
      mul_one, Real.norm_eq_abs, sq_abs]
    ring
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

/-- The ordinary half-space Poisson mass written as a radial integral at positive height. -/
theorem integral_poisson_radial_eq_one {t : ℝ} (ht : 0 < t) :
    (∫ v : ℝ^(n - 1), 2 * t /
      ((n : ℝ) * unitBallVolume n * Real.sqrt (t ^ 2 + ‖v‖ ^ 2) ^ n)) = 1 := by
  have hcoord : (t • eLast (n := n)) PDE.Common.lastIndex = t := by simp [eLast]
  have hupper : t • eLast (n := n) ∈ SobolevSpace.HalfSpace.upper n := by
    change 0 < (t • eLast (n := n)) PDE.Common.lastIndex
    simpa only [hcoord] using ht
  have h := poissonHalfSpaceExtension_one_eq_one (t • eLast (n := n)) hupper
  rw [poissonHalfSpaceExtension_eq_integral _ measurable_const, hcoord] at h
  rw [← integral_const_mul] at h
  convert h using 1
  apply integral_congr_ae
  filter_upwards [] with v
  rw [dist_smul_eLast_halfSpaceEmb_eq_sqrt]
  ring

/-- The scalar Poisson density has mass one in any injective physical tangent coordinates,
with the metric determinant supplying the surface area factor. -/
theorem integral_tangent_poisson_eq_one (T : ℝ^(n - 1) →ₗ[ℝ] ℝ^n)
    (hT : Function.Injective T) (ν : ℝ^n) (hν : ‖ν‖ = 1)
    (horth : ∀ v, inner ℝ ν (T v) = 0) {t : ℝ} (ht : 0 < t) :
    (∫ v : ℝ^(n - 1), T.normDet *
      (2 * t / ((n : ℝ) * unitBallVolume n * ‖t • ν - T v‖ ^ n))) = 1 := by
  simp_rw [norm_smul_normal_sub_eq_sqrt T ν hν horth]
  rw [T.integral_normDet_mul_comp_norm hT
    (fun r ↦ 2 * t / ((n : ℝ) * unitBallVolume n * Real.sqrt (t ^ 2 + r ^ 2) ^ n))]
  exact integral_poisson_radial_eq_one ht

/-- The scalar tangent-plane density is an integrable function. -/
theorem integrable_tangent_poisson (T : ℝ^(n - 1) →ₗ[ℝ] ℝ^n)
    (hT : Function.Injective T) (ν : ℝ^n) (hν : ‖ν‖ = 1)
    (horth : ∀ v, inner ℝ ν (T v) = 0) {t : ℝ} (ht : 0 < t) :
    Integrable (fun v : ℝ^(n - 1) ↦ T.normDet *
      (2 * t / ((n : ℝ) * unitBallVolume n * ‖t • ν - T v‖ ^ n))) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_tangent_poisson_eq_one T hT ν hν horth ht]
  exact one_ne_zero

/-- The flat paired normal kernel has vector mass equal to the unit normal. This exact
identity allows nonorthogonal tangent coordinates and every positive normal height. -/
theorem integral_tangent_poisson_smul_normal (T : ℝ^(n - 1) →ₗ[ℝ] ℝ^n)
    (hT : Function.Injective T) (ν : ℝ^n) (hν : ‖ν‖ = 1)
    (horth : ∀ v, inner ℝ ν (T v) = 0) {t : ℝ} (ht : 0 < t) :
    (∫ v : ℝ^(n - 1), (T.normDet *
      (2 * t / ((n : ℝ) * unitBallVolume n * ‖t • ν - T v‖ ^ n))) • ν) = ν := by
  rw [integral_smul_const, integral_tangent_poisson_eq_one T hT ν hν horth ht, one_smul]

/-- The vector tangent-plane density is Bochner integrable. -/
theorem integrable_tangent_poisson_smul_normal (T : ℝ^(n - 1) →ₗ[ℝ] ℝ^n)
    (hT : Function.Injective T) (ν : ℝ^n) (hν : ‖ν‖ = 1)
    (horth : ∀ v, inner ℝ ν (T v) = 0) {t : ℝ} (ht : 0 < t) :
    Integrable (fun v : ℝ^(n - 1) ↦ (T.normDet *
      (2 * t / ((n : ℝ) * unitBallVolume n * ‖t • ν - T v‖ ^ n))) • ν) :=
  (integrable_tangent_poisson T hT ν hν horth ht).smul_const ν

end GreenFunction
