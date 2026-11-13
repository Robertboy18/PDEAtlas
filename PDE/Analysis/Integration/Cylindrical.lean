/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Axisymmetric
public import PDE.Analysis.Integration.CoordinateSplit
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Cylindrical integration in three dimensions

An axisymmetric scalar field on `ℝ^3` depends only on the cylindrical radius
`r = √(x₀² + x₁²)` and the axial coordinate `z = x₂`; `cylindricalLift f` builds
such a field from a meridian profile `f : ℝ → ℝ → E`. We prove the cylindrical
change of variables

  `∫ x : ℝ^3, cylindricalLift f x = 2π ∫ z, ∫ r ∈ (0,∞), r · f r z`

together with the corresponding integrability transfer. The radial Jacobian `r`
is carried by the meridian measure `axisymmetricMeridianMeasure`, which is
`volumeIoiPow 1 ⊗ volume` on `MeridianHalfPlane = (0,∞) × ℝ`. The angular factor
`2π` comes from polar integration in the transverse plane.

The argument splits `ℝ^3` measure-preservingly as `ℝ^2 × ℝ` through
`lastCoordinateSplit` (see `lastCoordinateSplit_measurePreserving`), applies
Fubini, and reduces the inner integral over `ℝ^2` to Mathlib's
`integral_fun_norm_addHaar`, where the area `π` of the unit disc gives the
constant.

## Main results

* `integral_radialPlane`: `∫ y : ℝ^2, g ‖y‖ = 2π ∫ r ∈ (0,∞), r · g r`.
* `integral_volumeIoiPow_one`, `integrable_volumeIoiPow_one_iff`: integration
  against `volumeIoiPow 1` is integration against the density `r` on `(0,∞)`.
* `integrable_cylindricalLift_of_integrable_meridian`: a profile integrable
  for `r dr dz` has an integrable lift to `ℝ^3`.
* `memLp_two_cylindricalLift_of_integrable_meridian_norm_sq`: the `L²` version.
* `integral_cylindricalLift_iterated`, `integral_cylindricalLift`: the
  cylindrical integration formula, in iterated form and against the meridian
  measure.

This is the classical change to cylindrical coordinates.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley,
  1999.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace PDE.Analysis


/-- Lift a meridian profile to an axisymmetric function on Cartesian
three-space. -/
def cylindricalLift {E : Type*} (f : ℝ → ℝ → E) : ℝ^3 → E :=
  fun x ↦ f (PDE.CoordinateSystems.cylindricalRadius x)
    (PDE.CoordinateSystems.axialCoordinate x)

/-- Reassembling a point from `(y, z) ∈ ℝ^2 × ℝ`, the cylindrical radius `√(x₀² + x₁²)` is
the Euclidean norm of the transverse pair `y`. -/
@[simp]
theorem cylindricalRadius_lastCoordinateSplit_symm
    (p : ℝ^2 × ℝ) :
    PDE.CoordinateSystems.cylindricalRadius
        (lastCoordinateSplit.symm p) = ‖p.1‖ := by
  rw [PDE.CoordinateSystems.cylindricalRadius,
    PDE.CoordinateSystems.cylindricalRadiusSq,
    show (0 : Fin 3) = (0 : Fin 2).castSucc from rfl,
    show (1 : Fin 3) = (1 : Fin 2).castSucc from rfl,
    lastCoordinateSplit_symm_castSucc, lastCoordinateSplit_symm_castSucc,
    EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_two]

/-- Reassembling a point from `(y, z) ∈ ℝ^2 × ℝ`, the axial coordinate is `z`. -/
@[simp]
theorem axialCoordinate_lastCoordinateSplit_symm
    (p : ℝ^2 × ℝ) :
    PDE.CoordinateSystems.axialCoordinate
        (lastCoordinateSplit.symm p) = p.2 := by
  exact lastCoordinateSplit_symm_last p

/-- The axisymmetric lift at the point reassembled from `(y, z)` is the profile evaluated at
`(‖y‖, z)`. This is the identity that turns the `ℝ^3` integral into a planar-times-axial one. -/
@[simp]
theorem cylindricalLift_lastCoordinateSplit_symm
    {E : Type*} (f : ℝ → ℝ → E) (p : ℝ^2 × ℝ) :
    cylindricalLift f (lastCoordinateSplit.symm p) =
      f ‖p.1‖ p.2 := by
  simp [cylindricalLift]

/-- Radial integration in the two Cartesian coordinates transverse to the
symmetry axis. -/
theorem integral_radialPlane (g : ℝ → ℝ) :
    (∫ x : ℝ^2, g ‖x‖) =
      2 * Real.pi * ∫ r in Set.Ioi (0 : ℝ), r * g r := by
  simpa [MeasureTheory.Measure.real, EuclideanSpace.volume_ball_fin_two,
    ENNReal.toReal_ofReal Real.pi_nonneg, nsmul_eq_mul, mul_assoc] using
    (MeasureTheory.integral_fun_norm_addHaar
      (volume : Measure (ℝ^2)) g)

/-- Integration against `volumeIoiPow 1` is integration against the radial
density `r` on the positive half-line. -/
theorem integral_volumeIoiPow_one (g : ℝ → ℝ) :
    (∫ r : Set.Ioi (0 : ℝ), g r.1 ∂Measure.volumeIoiPow 1) =
      ∫ r in Set.Ioi (0 : ℝ), r * g r := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul
    ((measurable_subtype_coe.pow_const 1).real_toNNReal)
    (fun r : Set.Ioi (0 : ℝ) ↦ g r.1)]
  rw [integral_subtype_comap measurableSet_Ioi
    (fun r : ℝ ↦ Real.toNNReal (r ^ 1) • g r)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  simp [NNReal.smul_def, Real.coe_toNNReal _ (le_of_lt hr)]

/-- Integrability against `volumeIoiPow 1` is the usual positive-half-line
integrability after inserting the radial Jacobian. -/
theorem integrable_volumeIoiPow_one_iff (g : ℝ → ℝ) :
    Integrable (fun r : Set.Ioi (0 : ℝ) ↦ g r.1)
        (Measure.volumeIoiPow 1) ↔
      IntegrableOn (fun r : ℝ ↦ r * g r) (Set.Ioi 0) := by
  rw [integrableOn_iff_comap_subtypeVal, Measure.volumeIoiPow,
    integrable_withDensity_iff_integrable_smul', integrable_congr]
  · refine .of_forall ?_
    rintro ⟨r, hr : 0 < r⟩
    simp [smul_eq_mul, ENNReal.toReal_ofReal (le_of_lt hr)]
  · fun_prop
  · simp
  · measurability

/-- A meridian-integrable scalar profile has an integrable axisymmetric lift
to three-dimensional Cartesian space.  Measurability of the Cartesian split
is stated separately because applications normally obtain it from continuity
or smoothness of the profile. -/
theorem integrable_cylindricalLift_of_integrable_meridian
    (f : ℝ → ℝ → ℝ)
    (hmeas : AEStronglyMeasurable
      (fun p : ℝ^2 × ℝ ↦ f ‖p.1‖ p.2) (volume.prod volume))
    (hmeridian : Integrable
      (fun q : MeridianHalfPlane ↦ f q.1.1 q.2)
      axisymmetricMeridianMeasure) :
    Integrable (cylindricalLift f) := by
  have hmeridian' : Integrable
      (fun q : Set.Ioi (0 : ℝ) × ℝ ↦ f q.1.1 q.2)
      ((Measure.volumeIoiPow 1).prod volume) := by
    simpa [axisymmetricMeridianMeasure] using hmeridian
  have hradial : ∀ᵐ z ∂volume,
      Integrable (fun r : Set.Ioi (0 : ℝ) ↦ f r.1 z)
        (Measure.volumeIoiPow 1) :=
    hmeridian'.prod_left_ae
  have houter : Integrable
      (fun z : ℝ ↦ ∫ r : Set.Ioi (0 : ℝ), ‖f r.1 z‖
        ∂Measure.volumeIoiPow 1) volume :=
    hmeridian'.integral_norm_prod_right
  have hplane : ∀ᵐ z ∂volume,
      Integrable (fun y : ℝ^2 ↦ f ‖y‖ z) volume := by
    filter_upwards [hradial] with z hz
    refine (MeasureTheory.integrable_fun_norm_addHaar
      (F := ℝ) (volume : Measure (ℝ^2)) (f := fun r ↦ f r z)).2 ?_
    have hr := (integrable_volumeIoiPow_one_iff (fun r ↦ f r z)).1 hz
    simpa [show Module.finrank ℝ (ℝ^2) = 2 by simp, smul_eq_mul] using hr
  have houterPlane : Integrable
      (fun z : ℝ ↦ ∫ y : ℝ^2, ‖f ‖y‖ z‖) volume := by
    have hscaled := houter.const_mul (2 * Real.pi)
    refine hscaled.congr ?_
    filter_upwards with z
    rw [integral_radialPlane (fun r ↦ ‖f r z‖),
      ← integral_volumeIoiPow_one]
  have hsplit : Integrable
      (fun p : ℝ^2 × ℝ ↦ f ‖p.1‖ p.2) (volume.prod volume) :=
    (integrable_prod_iff' hmeas).2 ⟨hplane, houterPlane⟩
  have hcomp : Integrable
      (cylindricalLift f ∘ lastCoordinateSplit.symm) := by
    refine hsplit.congr ?_
    filter_upwards with p
    exact (cylindricalLift_lastCoordinateSplit_symm f p).symm
  exact ((lastCoordinateSplit_measurePreserving.symm
    lastCoordinateSplit).integrable_comp_emb
      lastCoordinateSplit.symm.measurableEmbedding).1 hcomp

/-- Square-integrability of an axisymmetric profile with respect to `r dr dz`
implies square-integrability of its Cartesian lift. -/
theorem memLp_two_cylindricalLift_of_integrable_meridian_norm_sq
    {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → ℝ → E)
    (hmeas : AEStronglyMeasurable (cylindricalLift f))
    (hsplitMeas : AEStronglyMeasurable
      (fun p : ℝ^2 × ℝ ↦ ‖f ‖p.1‖ p.2‖ ^ 2) (volume.prod volume))
    (hmeridian : Integrable
      (fun q : MeridianHalfPlane ↦ ‖f q.1.1 q.2‖ ^ 2)
      axisymmetricMeridianMeasure) :
    MemLp (cylindricalLift f) 2 volume := by
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hsquare := integrable_cylindricalLift_of_integrable_meridian
    (fun r z ↦ ‖f r z‖ ^ 2) hsplitMeas hmeridian
  refine hsquare.congr ?_
  filter_upwards with x
  rfl

/-- The meridian integral is the usual iterated integral with radial Jacobian
`r`. -/
theorem integral_axisymmetricMeridianMeasure_eq_iterated
    (f : ℝ → ℝ → ℝ)
    (hf : Integrable
      (fun q : MeridianHalfPlane ↦ f q.1.1 q.2)
      axisymmetricMeridianMeasure) :
    (∫ q : MeridianHalfPlane, f q.1.1 q.2
        ∂axisymmetricMeridianMeasure) =
      ∫ z : ℝ, ∫ r in Set.Ioi (0 : ℝ), r * f r z := by
  rw [axisymmetricMeridianMeasure, integral_prod_symm _ hf]
  apply integral_congr_ae
  filter_upwards with z
  exact integral_volumeIoiPow_one (fun r ↦ f r z)

/-- Cylindrical integration of an integrable axisymmetric scalar field on
three-space.  The right-hand side displays both the radial Jacobian and the
angular factor. -/
theorem integral_cylindricalLift_iterated
    (f : ℝ → ℝ → ℝ)
    (hf : Integrable (cylindricalLift f)) :
    (∫ x : ℝ^3, cylindricalLift f x) =
      2 * Real.pi * ∫ z : ℝ, ∫ r in Set.Ioi (0 : ℝ), r * f r z := by
  have hsplit : Integrable (fun p : ℝ^2 × ℝ ↦ f ‖p.1‖ p.2) := by
    have hcomp : Integrable
        (cylindricalLift f ∘ lastCoordinateSplit.symm) :=
      ((lastCoordinateSplit_measurePreserving.symm
        lastCoordinateSplit).integrable_comp_emb
          lastCoordinateSplit.symm.measurableEmbedding).2 hf
    apply hcomp.congr
    filter_upwards with p
    exact cylindricalLift_lastCoordinateSplit_symm f p
  calc
    (∫ x : ℝ^3, cylindricalLift f x) =
        ∫ p : ℝ^2 × ℝ,
          cylindricalLift f (lastCoordinateSplit.symm p) := by
      exact ((lastCoordinateSplit_measurePreserving.symm
        lastCoordinateSplit).integral_comp
          lastCoordinateSplit.symm.measurableEmbedding
          (cylindricalLift f)).symm
    _ = ∫ p : ℝ^2 × ℝ, f ‖p.1‖ p.2 := by
      apply integral_congr_ae
      filter_upwards with p
      exact cylindricalLift_lastCoordinateSplit_symm f p
    _ = ∫ z : ℝ, ∫ y : ℝ^2, f ‖y‖ z :=
      integral_prod_symm _ hsplit
    _ = ∫ z : ℝ,
          2 * Real.pi * ∫ r in Set.Ioi (0 : ℝ), r * f r z := by
      apply integral_congr_ae
      filter_upwards with z
      exact integral_radialPlane (fun r ↦ f r z)
    _ = 2 * Real.pi *
          ∫ z : ℝ, ∫ r in Set.Ioi (0 : ℝ), r * f r z := by
      rw [integral_const_mul]

/-- Cylindrical integration expressed using the canonical meridian measure
`r dr dz`.  The second integrability hypothesis is the explicit Fubini
condition for the meridian representative. -/
theorem integral_cylindricalLift
    (f : ℝ → ℝ → ℝ)
    (hf : Integrable (cylindricalLift f))
    (hmeridian : Integrable
      (fun q : MeridianHalfPlane ↦ f q.1.1 q.2)
      axisymmetricMeridianMeasure) :
    (∫ x : ℝ^3, cylindricalLift f x) =
      2 * Real.pi *
        ∫ q : MeridianHalfPlane, f q.1.1 q.2
          ∂axisymmetricMeridianMeasure := by
  rw [integral_cylindricalLift_iterated f hf,
    integral_axisymmetricMeridianMeasure_eq_iterated f hmeridian]

end PDE.Analysis

end
