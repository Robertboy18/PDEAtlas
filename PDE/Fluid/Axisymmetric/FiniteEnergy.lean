/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Cylindrical
public import PDE.Fluid.Axisymmetric.CartesianReconstruction
import Mathlib.MeasureTheory.Function.L2Space

import CAS.ExactTactic
import PDE.Spaces.Sobolev.Inequalities.Hardy.Weighted
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Finite energy of axisymmetric reconstructions

The squared speed of the division-free squared-radius reconstruction of an axisymmetric
velocity is the cylindrical lift of a meridian energy density, in which the radial and
azimuthal cross terms cancel. Integrating against the meridian measure `r dr dz` turns a
two-dimensional meridian energy bound into a three-dimensional `L²` velocity.

The weighted-moment theorems derive this integrability from the `r³ dr dz` moments of the
swirl, the streamfunction, and its physical radial and axial derivatives. Radial integration by
parts cancels the extra terms in `(2ψ + rψr)²`; the boundary flux vanishes as a consequence of
the moment bounds.

## Main results

* `axisymmetricVelocityEnergyDensity`,
  `norm_sq_axisymmetricVelocity_eq_cylindricalLift_energyDensity`: the meridian energy density
  and the pointwise identity `‖u‖² = cylindricalLift density`.
* `memLp_two_axisymmetricVelocity_of_integrable_meridian_energy`: an integrable meridian energy
  density gives an `L²` velocity on `ℝ^3`.
* `finite_energy_axisymmetricVelocity_of_weighted_moments`,
  `finite_energy_meridionalVelocityOfScalar_of_weighted_moments`: finite weighted moments give
  an `L²` velocity whose energy is `2π` times the meridian integral of the derivative moments.
-/

@[expose] public section

open PDE (coordinateLine)

noncomputable section

open MeasureTheory
open PDE.Analysis
open PDE.CoordinateSystems

namespace AxisymmetricFlow

set_option linter.missingDocs true

/-- Squared speed of the reconstructed velocity at cylindrical coordinates
`(r,z)`, expressed through profiles in squared-radius coordinates `(r²,z)`. -/
def axisymmetricVelocityEnergyDensity (U Ψ : ℝ^2 → ℝ) (r z : ℝ) : ℝ :=
  let q : ℝ^2 := WithLp.toLp 2 ![r ^ 2, z]
  r ^ 2 *
      (((∂[(1 : Fin 2)] Ψ) q) ^ 2 + (U q) ^ 2) +
    (2 * Ψ q + 2 * r ^ 2 * (∂[(0 : Fin 2)] Ψ) q) ^ 2

/-- The Cartesian squared norm of the reconstructed velocity is the
axisymmetric lift of its scalar meridian energy density. -/
theorem norm_sq_axisymmetricVelocity_eq_cylindricalLift_energyDensity
    (U Ψ : ℝ^2 → ℝ) (x : ℝ^3) :
    ‖axisymmetricVelocity U Ψ x‖ ^ 2 =
      cylindricalLift (axisymmetricVelocityEnergyDensity U Ψ) x := by
  have hq :
      WithLp.toLp 2 ![cylindricalRadius x ^ 2, axialCoordinate x] =
        squaredCylindricalMap x :=
    (squaredCylindricalMap_eq_toLp_cylindricalRadius_sq x).symm
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_three, axisymmetricVelocity_apply_zero,
    axisymmetricVelocity_apply_one, axisymmetricVelocity_apply_two]
  simp only [cylindricalLift, axisymmetricVelocityEnergyDensity, hq,
    squaredCylindricalLift]
  have hr : cylindricalRadius x ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    simp [cylindricalRadiusSq, cylindricalRadius_sq]
  rw [← cylindricalRadius_sq]
  linear_combination
    -(((∂[(1 : Fin 2)] Ψ) (squaredCylindricalMap x)) ^ 2 +
      (U (squaredCylindricalMap x)) ^ 2) * hr

/-- If the natural meridian integral of the reconstructed squared speed is
finite, then the reconstructed Cartesian velocity belongs to `L²(ℝ^3)`.
Only continuity of the swirl profile and `C¹` regularity of the streamfunction
are needed; differentiability of the reconstructed velocity is not required. -/
theorem memLp_two_axisymmetricVelocity_of_integrable_meridian_energy
    {U Ψ : ℝ^2 → ℝ}
    (hU : Continuous U) (hΨ : ContDiff ℝ 1 Ψ)
    (henergy : Integrable
      (fun q : MeridianHalfPlane ↦
        axisymmetricVelocityEnergyDensity U Ψ q.1.1 q.2)
      axisymmetricMeridianMeasure) :
    MemLp (axisymmetricVelocity U Ψ) 2 volume := by
  have hvelocityContinuous : Continuous (axisymmetricVelocity U Ψ) :=
    ((contDiff_meridionalVelocity_of_succ (n := 0) hΨ).add
      (contDiff_swirlVelocity (contDiff_zero.mpr hU))).continuous
  rw [memLp_two_iff_integrable_sq_norm
    hvelocityContinuous.aestronglyMeasurable]
  have hΨS : Continuous (fun q ↦ (∂[(0 : Fin 2)] Ψ) q) :=
    (PDE.contDiff_partialDeriv_of_succ (m := 0) hΨ).continuous
  have hΨZ : Continuous (fun q ↦ (∂[(1 : Fin 2)] Ψ) q) :=
    (PDE.contDiff_partialDeriv_of_succ (m := 0) hΨ).continuous
  have hdensityContinuous : Continuous (fun p : ℝ^2 × ℝ ↦
      axisymmetricVelocityEnergyDensity U Ψ ‖p.1‖ p.2) := by
    unfold axisymmetricVelocityEnergyDensity
    fun_prop
  have hintegrable := integrable_cylindricalLift_of_integrable_meridian
    (axisymmetricVelocityEnergyDensity U Ψ)
    hdensityContinuous.aestronglyMeasurable henergy
  exact hintegrable.congr <| Filter.Eventually.of_forall fun x ↦
    (norm_sq_axisymmetricVelocity_eq_cylindricalLift_energyDensity U Ψ x).symm

/-- Fubini transports the radial cancellation to the meridian measure. Its
nonnegative integrand lets the derivative moment control the outer integral,
even though no uniform bound on the streamfunction near the axis is assumed. -/
private theorem meridian_poloidal_energy
    {ψ ψr : ℝ → ℝ → ℝ}
    (hψ : ∀ z, ContDiff ℝ 1 (fun r ↦ ψ r z))
    (hc : Continuous (Function.uncurry ψ))
    (hcr : Continuous (Function.uncurry ψr))
    (hd : ∀ r z, deriv (fun s ↦ ψ s z) r = ψr r z)
    (h0 : Integrable (fun q : MeridianHalfPlane ↦ q.1.1 ^ 2 * ψ q.1.1 q.2 ^ 2)
      axisymmetricMeridianMeasure)
    (h1 : Integrable (fun q : MeridianHalfPlane ↦ q.1.1 ^ 2 * ψr q.1.1 q.2 ^ 2)
      axisymmetricMeridianMeasure) :
    Integrable (fun q : MeridianHalfPlane ↦ (2 * ψ q.1.1 q.2 + q.1.1 * ψr q.1.1 q.2) ^ 2)
      axisymmetricMeridianMeasure ∧
      (∫ q : MeridianHalfPlane, (2 * ψ q.1.1 q.2 + q.1.1 * ψr q.1.1 q.2) ^ 2
        ∂axisymmetricMeridianMeasure) =
      ∫ q : MeridianHalfPlane, q.1.1 ^ 2 * ψr q.1.1 q.2 ^ 2
        ∂axisymmetricMeridianMeasure := by
  have h0' : Integrable _ ((Measure.volumeIoiPow 1).prod volume) := h0
  have h1' : Integrable _ ((Measure.volumeIoiPow 1).prod volume) := h1
  have hslices : ∀ᵐ z : ℝ,
      Integrable (fun r : Set.Ioi (0 : ℝ) ↦ (2 * ψ r.1 z + r.1 * ψr r.1 z) ^ 2)
        (Measure.volumeIoiPow 1) ∧
      (∫ r : Set.Ioi (0 : ℝ), (2 * ψ r.1 z + r.1 * ψr r.1 z) ^ 2
        ∂Measure.volumeIoiPow 1) =
      ∫ r : Set.Ioi (0 : ℝ), r.1 ^ 2 * ψr r.1 z ^ 2 ∂Measure.volumeIoiPow 1 := by
    filter_upwards [h0'.prod_left_ae, h1'.prod_left_ae] with z h0z h1z
    have hz0 : IntegrableOn (fun r ↦ r ^ 3 * ψ r z ^ 2) (Set.Ioi 0) := by
      convert (integrable_volumeIoiPow_one_iff (fun r ↦ r ^ 2 * ψ r z ^ 2)).mp h0z using 1
      ext r
      cas
    have hz1 : IntegrableOn (fun r ↦ r ^ 3 * deriv (fun s ↦ ψ s z) r ^ 2) (Set.Ioi 0) := by
      convert (integrable_volumeIoiPow_one_iff (fun r ↦ r ^ 2 * ψr r z ^ 2)).mp h1z using 1
      ext r
      rw [hd r z]
      cas
    obtain ⟨hint, heq⟩ :=
      SobolevSpace.Hardy.integral_Ioi_mul_two_mul_add_mul_deriv_sq_eq_integral_Ioi_cube_mul_deriv_sq
        (hψ z) hz0 hz1
    simp only [hd] at hint heq
    refine ⟨(integrable_volumeIoiPow_one_iff
      (fun r : ℝ ↦ (2 * ψ r z + r * ψr r z) ^ 2)).mpr hint, ?_⟩
    rw [integral_volumeIoiPow_one
      (fun r : ℝ ↦ (2 * ψ r z + r * ψr r z) ^ 2),
      integral_volumeIoiPow_one (fun r : ℝ ↦ r ^ 2 * ψr r z ^ 2), heq]
    exact integral_congr_ae (.of_forall fun r ↦ by cas)
  have hp : Continuous (fun q : MeridianHalfPlane ↦ (q.1.1, q.2)) := by fun_prop
  have hmeas : AEStronglyMeasurable
      (fun q : MeridianHalfPlane ↦ (2 * ψ q.1.1 q.2 + q.1.1 * ψr q.1.1 q.2) ^ 2)
      ((Measure.volumeIoiPow 1).prod volume) :=
    (((continuous_const.mul (hc.comp hp)).add
      ((continuous_subtype_val.comp continuous_fst).mul (hcr.comp hp))).pow 2).aestronglyMeasurable
  -- the outer integrals of the norms are those of the slices
  have hnormeq (z : ℝ) :
      (∫ r : Set.Ioi (0 : ℝ), ‖(2 * ψ r.1 z + r.1 * ψr r.1 z) ^ 2‖ ∂Measure.volumeIoiPow 1) =
        ∫ r : Set.Ioi (0 : ℝ), (2 * ψ r.1 z + r.1 * ψr r.1 z) ^ 2 ∂Measure.volumeIoiPow 1 :=
    integral_congr_ae (.of_forall fun r ↦ Real.norm_of_nonneg (sq_nonneg _))
  have hnormeq' (z : ℝ) :
      (∫ r : Set.Ioi (0 : ℝ), ‖r.1 ^ 2 * ψr r.1 z ^ 2‖ ∂Measure.volumeIoiPow 1) =
        ∫ r : Set.Ioi (0 : ℝ), r.1 ^ 2 * ψr r.1 z ^ 2 ∂Measure.volumeIoiPow 1 :=
    integral_congr_ae (.of_forall fun r ↦ Real.norm_of_nonneg (by positivity))
  have hint : Integrable
      (fun q : MeridianHalfPlane ↦ (2 * ψ q.1.1 q.2 + q.1.1 * ψr q.1.1 q.2) ^ 2)
      ((Measure.volumeIoiPow 1).prod volume) := by
    refine (integrable_prod_iff' hmeas).mpr ⟨hslices.mono fun _ hz ↦ hz.1, ?_⟩
    refine h1'.integral_norm_prod_right.congr ?_
    filter_upwards [hslices] with z hz
    rw [hnormeq z, hnormeq' z, hz.2]
  refine ⟨hint, ?_⟩
  change (∫ q, _ ∂(Measure.volumeIoiPow 1).prod volume) =
    ∫ q, _ ∂(Measure.volumeIoiPow 1).prod volume
  rw [integral_prod_symm _ hint, integral_prod_symm _ h1']
  exact integral_congr_ae (hslices.mono fun _ hz ↦ hz.2)

/-- Differentiating in the physical radius contributes the factor `2r`
because the profile is written in the squared radius. -/
private theorem deriv_squared_radius_profile
    {Ψ : ℝ^2 → ℝ} (hΨ : ContDiff ℝ 1 Ψ) (r z : ℝ) :
    deriv (fun s : ℝ ↦ Ψ (WithLp.toLp 2 ![s ^ 2, z])) r =
      2 * r * (∂[(0 : Fin 2)] Ψ) (WithLp.toLp 2 ![r ^ 2, z]) := by
  have hv : HasDerivAt (fun s : ℝ ↦ ![s ^ 2, z]) ![2 * r, 0] r := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert! (hasDerivAt_id r).pow 2 using 1
      simp
    · simpa using (hasDerivAt_const (c := z) (x := r))
  have hq := (PiLp.hasFDerivAt_toLp (p := 2) (𝕜 := ℝ)
    ![r ^ 2, z]).comp_hasDerivAt r hv
  change HasDerivAt (fun s : ℝ ↦ WithLp.toLp 2 ![s ^ 2, z])
    (WithLp.toLp 2 ![2 * r, 0]) r at hq
  have hc := ((hΨ.differentiable one_ne_zero)
    (WithLp.toLp 2 ![r ^ 2, z])).hasFDerivAt.comp_hasDerivAt r hq
  change HasDerivAt (fun s : ℝ ↦ Ψ (WithLp.toLp 2 ![s ^ 2, z]))
    ((fderiv ℝ Ψ (WithLp.toLp 2 ![r ^ 2, z])) (WithLp.toLp 2 ![2 * r, 0])) r at hc
  rw [hc.deriv, PDE.fderiv_apply_eq_sum_partialDeriv_mul, Fin.sum_univ_two]
  change (∂[(0 : Fin 2)] Ψ) (WithLp.toLp 2 ![r ^ 2, z]) * (2 * r) +
    (∂[(1 : Fin 2)] Ψ) (WithLp.toLp 2 ![r ^ 2, z]) * 0 = _
  cas

/-- The Cartesian velocity has finite kinetic energy when the reduced
swirl, streamfunction, and its two physical derivatives have finite
`r³ dr dz` moments. The streamfunction moment fixes the decay normalization;
the independent swirl moment is not replaced by a bound on its derivatives.

The energy formula follows by applying the radial cancellation on almost
every axial slice, then the cylindrical change of variables. No trace at
infinity or integrability of the velocity is an input. -/
theorem finite_energy_axisymmetricVelocity_of_weighted_moments
    {U Ψ : ℝ^2 → ℝ} (hU : Continuous U) (hΨ : ContDiff ℝ 1 Ψ)
    (hU0 : Integrable (fun q : MeridianHalfPlane ↦
      q.1.1 ^ 2 * U (WithLp.toLp 2 ![q.1.1 ^ 2, q.2]) ^ 2)
      axisymmetricMeridianMeasure)
    (hΨ0 : Integrable (fun q : MeridianHalfPlane ↦
      q.1.1 ^ 2 * Ψ (WithLp.toLp 2 ![q.1.1 ^ 2, q.2]) ^ 2)
      axisymmetricMeridianMeasure)
    (hΨr : Integrable (fun q : MeridianHalfPlane ↦
      q.1.1 ^ 2 *
        (2 * q.1.1 * (∂[(0 : Fin 2)] Ψ)
          (WithLp.toLp 2 ![q.1.1 ^ 2, q.2])) ^ 2)
      axisymmetricMeridianMeasure)
    (hΨz : Integrable (fun q : MeridianHalfPlane ↦
      q.1.1 ^ 2 * (∂[(1 : Fin 2)] Ψ) (WithLp.toLp 2 ![q.1.1 ^ 2, q.2]) ^ 2)
      axisymmetricMeridianMeasure) :
    MemLp (axisymmetricVelocity U Ψ) 2 volume ∧
      (∫ x : ℝ^3, ‖axisymmetricVelocity U Ψ x‖ ^ 2) =
        2 * Real.pi * ∫ q : MeridianHalfPlane,
          q.1.1 ^ 2 * U (WithLp.toLp 2 ![q.1.1 ^ 2, q.2]) ^ 2 +
            q.1.1 ^ 2 *
              (2 * q.1.1 * (∂[(0 : Fin 2)] Ψ)
                (WithLp.toLp 2 ![q.1.1 ^ 2, q.2])) ^ 2 +
            q.1.1 ^ 2 *
              (∂[(1 : Fin 2)] Ψ) (WithLp.toLp 2 ![q.1.1 ^ 2, q.2]) ^ 2
          ∂axisymmetricMeridianMeasure := by
  let ψ : ℝ → ℝ → ℝ := fun r z ↦ Ψ (WithLp.toLp 2 ![r ^ 2, z])
  let ψr : ℝ → ℝ → ℝ := fun r z ↦
    2 * r * (∂[(0 : Fin 2)] Ψ) (WithLp.toLp 2 ![r ^ 2, z])
  have hcS : Continuous (∂[(0 : Fin 2)] Ψ) :=
    (PDE.contDiff_partialDeriv_of_succ (m := 0) hΨ).continuous
  have hcZ : Continuous (∂[(1 : Fin 2)] Ψ) :=
    (PDE.contDiff_partialDeriv_of_succ (m := 0) hΨ).continuous
  have hψ (z : ℝ) : ContDiff ℝ 1 (fun r ↦ ψ r z) := hΨ.comp <| (contDiff_piLp (2 : ENNReal)).2
    fun i ↦ by fin_cases i; exacts [contDiff_id.pow 2, contDiff_const]
  have hc : Continuous (Function.uncurry ψ) := by
    exact hΨ.continuous.comp (by fun_prop)
  have hcr : Continuous (Function.uncurry ψr) := by
    dsimp [ψr, Function.uncurry]
    fun_prop
  obtain ⟨hpol, hpolEq⟩ := meridian_poloidal_energy hψ hc hcr
    (fun r z ↦ deriv_squared_radius_profile hΨ r z) hΨ0 hΨr
  dsimp only [ψ, ψr] at hpol hpolEq
  -- the meridian energy density splits into the swirl, axial and poloidal parts
  have hsplit (q : MeridianHalfPlane) : axisymmetricVelocityEnergyDensity U Ψ q.1.1 q.2 =
      q.1.1 ^ 2 * U (WithLp.toLp 2 ![q.1.1 ^ 2, q.2]) ^ 2 +
        (2 * Ψ (WithLp.toLp 2 ![q.1.1 ^ 2, q.2]) +
          q.1.1 * (2 * q.1.1 * (∂[(0 : Fin 2)] Ψ) (WithLp.toLp 2 ![q.1.1 ^ 2, q.2]))) ^ 2 +
        q.1.1 ^ 2 * (∂[(1 : Fin 2)] Ψ) (WithLp.toLp 2 ![q.1.1 ^ 2, q.2]) ^ 2 := by
    dsimp only [axisymmetricVelocityEnergyDensity]
    cas
  have he : Integrable (fun q : MeridianHalfPlane ↦
      axisymmetricVelocityEnergyDensity U Ψ q.1.1 q.2) axisymmetricMeridianMeasure :=
    ((hU0.add hpol).add hΨz).congr (.of_forall fun q ↦ (hsplit q).symm)
  have hmem := memLp_two_axisymmetricVelocity_of_integrable_meridian_energy hU hΨ he
  refine ⟨hmem, ?_⟩
  have hcart : Integrable (cylindricalLift (axisymmetricVelocityEnergyDensity U Ψ)) :=
    ((memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem).congr
      (.of_forall (norm_sq_axisymmetricVelocity_eq_cylindricalLift_energyDensity U Ψ))
  calc
    _ = ∫ x : ℝ^3, cylindricalLift (axisymmetricVelocityEnergyDensity U Ψ) x :=
      integral_congr_ae (.of_forall
        (norm_sq_axisymmetricVelocity_eq_cylindricalLift_energyDensity U Ψ))
    _ = 2 * Real.pi * ∫ q : MeridianHalfPlane,
        axisymmetricVelocityEnergyDensity U Ψ q.1.1 q.2
          ∂axisymmetricMeridianMeasure :=
      integral_cylindricalLift _ hcart he
    _ = _ := by
      rw [integral_congr_ae (.of_forall hsplit), integral_add, integral_add hU0 hpol, hpolEq,
        integral_add, integral_add hU0 hΨr]
      exacts [hU0.add hΨr, hΨz, hU0.add hpol, hΨz]

/-- A smooth Cartesian meridian lift reconstructs a finite-energy poloidal
velocity from the three cubic moments of its physical profile. The scalar
moment fixes the decay normalization. Radial integration by parts then removes
it from the energy identity, leaving only the two derivative moments.

There is no squared-radius generator hypothesis: the Cartesian lift itself is
`C¹`. In particular this applies when the lift is a restriction of a smooth
radial potential in a higher-dimensional Cartesian space. -/
theorem finite_energy_meridionalVelocityOfScalar_of_weighted_moments
    {ψ : ℝ^2 → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hlift : ContDiff ℝ 1 (meridianLift ψ))
    (h0 : Integrable (fun q : MeridianHalfPlane ↦ q.1.1 ^ 2 *
      ψ (WithLp.toLp 2 ![q.1.1, q.2]) ^ 2) axisymmetricMeridianMeasure)
    (hr : Integrable (fun q : MeridianHalfPlane ↦ q.1.1 ^ 2 *
      (∂[(0 : Fin 2)] ψ) (WithLp.toLp 2 ![q.1.1, q.2]) ^ 2)
      axisymmetricMeridianMeasure)
    (hz : Integrable (fun q : MeridianHalfPlane ↦ q.1.1 ^ 2 *
      (∂[(1 : Fin 2)] ψ) (WithLp.toLp 2 ![q.1.1, q.2]) ^ 2)
      axisymmetricMeridianMeasure) :
    MemLp (meridionalVelocityOfScalar (meridianLift ψ)) 2 volume ∧
      (∫ x : ℝ^3, ‖meridionalVelocityOfScalar (meridianLift ψ) x‖ ^ 2) =
        2 * Real.pi * ∫ q : MeridianHalfPlane, q.1.1 ^ 2 *
          ((∂[(0 : Fin 2)] ψ) (WithLp.toLp 2 ![q.1.1, q.2]) ^ 2 +
            (∂[(1 : Fin 2)] ψ) (WithLp.toLp 2 ![q.1.1, q.2]) ^ 2)
          ∂axisymmetricMeridianMeasure := by
  let p : ℝ → ℝ → ℝ^2 := fun r z ↦ WithLp.toLp 2 ![r, z]
  let f : ℝ → ℝ → ℝ := fun r z ↦ ψ (p r z)
  let fr : ℝ → ℝ → ℝ := fun r z ↦ (∂[(0 : Fin 2)] ψ) (p r z)
  have hp (z : ℝ) : ContDiff ℝ 1 (fun r ↦ p r z) :=
    (contDiff_piLp (2 : ENNReal)).mpr fun i ↦ by fin_cases i; exacts [contDiff_id, contDiff_const]
  have hc : Continuous (Function.uncurry f) := hψ.continuous.comp (by fun_prop)
  have hcr : Continuous (∂[(0 : Fin 2)] ψ) :=
    (PDE.contDiff_partialDeriv_of_succ (m := 0) hψ).continuous
  have hcz : Continuous (∂[(1 : Fin 2)] ψ) :=
    (PDE.contDiff_partialDeriv_of_succ (m := 0) hψ).continuous
  have hfr : Continuous (Function.uncurry fr) := hcr.comp (by fun_prop)
  have hd (r z : ℝ) : deriv (fun s ↦ f s z) r = fr r z := by
    have he : (ψ ∘ coordinateLine (0 : Fin 2) (p r z)) = (fun s ↦ f s z) := by
      funext s
      change ψ (coordinateLine (0 : Fin 2) (p r z) s) = ψ (p s z)
      congr 1
      ext i
      fin_cases i <;> simp [coordinateLine, p]
    have ht := PDE.partialDeriv_eq_deriv_coordinateLine (0 : Fin 2) (p r z)
      hψ.contDiffAt.differentiableAt_one
    rw [he] at ht
    exact ht.symm
  obtain ⟨hpol, hpolEq⟩ := meridian_poloidal_energy
    (fun z ↦ hψ.comp (hp z)) hc hfr hd h0 hr
  let e : ℝ → ℝ → ℝ := fun r z ↦
    r ^ 2 * (∂[(1 : Fin 2)] ψ) (p r z) ^ 2 + (2 * f r z + r * fr r z) ^ 2
  have he : Integrable (fun q : MeridianHalfPlane ↦ e q.1.1 q.2)
      axisymmetricMeridianMeasure := hz.add hpol
  have hec : Continuous (fun q : ℝ^2 × ℝ ↦ e ‖q.1‖ q.2) := by
    dsimp [e, f, fr, p]
    fun_prop
  have hi : Integrable (cylindricalLift e) :=
    integrable_cylindricalLift_of_integrable_meridian e hec.aestronglyMeasurable he
  have hnorm (x : ℝ^3) :
      ‖meridionalVelocityOfScalar (meridianLift ψ) x‖ ^ 2 = cylindricalLift e x :=
    norm_sq_meridionalVelocityOfScalar_meridianLift hψ x
  have hv : Continuous (meridionalVelocityOfScalar (meridianLift ψ)) :=
    (contDiff_meridionalVelocityOfScalar_of_succ (n := 0) hlift).continuous
  have hmem : MemLp (meridionalVelocityOfScalar (meridianLift ψ)) 2 volume :=
    (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mpr
      (hi.congr (.of_forall fun x ↦ (hnorm x).symm))
  refine ⟨hmem, ?_⟩
  calc
    _ = ∫ x : ℝ^3, cylindricalLift e x := integral_congr_ae (.of_forall hnorm)
    _ = 2 * Real.pi * ∫ q : MeridianHalfPlane, e q.1.1 q.2
        ∂axisymmetricMeridianMeasure := integral_cylindricalLift e hi he
    _ = _ := by
      dsimp only [e, f, fr, p, Function.comp_apply] at hpol hpolEq ⊢
      rw [integral_add hz hpol, hpolEq, ← integral_add hz hr]
      exact congrArg _ (integral_congr_ae (.of_forall fun q ↦ by cas))

end AxisymmetricFlow

end
