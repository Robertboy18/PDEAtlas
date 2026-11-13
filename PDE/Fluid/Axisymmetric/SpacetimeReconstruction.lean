/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Axisymmetric.CartesianVorticity
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import PDE.Analysis.Calculus.LocalExtension
import PDE.FDeriv.Calculus
import PDE.FDeriv.SpaceTime
import CAS.ExactTactic

/-!
# Spacetime reconstruction of axis-regular velocity and vorticity

The squared-radius Cartesian reconstruction extends to time-dependent profiles. A profile is a
scalar field on `SpaceTime 2`, with coordinates `(t, s, z)`, while the reconstructed velocity is a
vector field on `SpaceTime 3`, with coordinates `(t, x₁, x₂, z)`.

At each fixed time the velocity is the spatial reconstruction `axisymmetricVelocity` of the profile
slices, and the vorticity is the spatial curl of that slice, given by
`spatialCurl_axisymmetricVelocity`. Consequently all identities remain valid on the symmetry axis
and never divide by the cylindrical radius. The results are kinematic: evaluation, joint spacetime
regularity, incompressibility, curl, and axis values.

## Main results

* `profileSlice`, `spacetimeSquaredCylindricalLift`: fixed-time slices of profiles and the lift
  of a profile to `(t, x₁, x₂, z)` spacetime through `(t, x) ↦ (t, x₁² + x₂², x₃)`.
* `spacetimeAxisymmetricVelocity`: the time-dependent reconstructed velocity, with the explicit
  division-free formula `spacetimeAxisymmetricVelocity_timeSpaceCons_eq_cartesianVector`.
* `contDiff_spacetimeAxisymmetricVelocity`: a `C^n` swirl profile and a `C^(n+1)` streamfunction
  profile give a jointly `C^n` velocity; `contDiffAt_spacetimeAxisymmetricVelocity` and
  `spacetimeAxisymmetricVelocity_eventuallyEq` are the local versions used for profiles that
  are smooth only on an open set of `(t, s, z)`.
* `spatialFieldDivergenceFree_velocitySlice_spacetimeAxisymmetricVelocity`: every fixed-time
  slice is divergence free on all of `ℝ^3`.
* `spacetimeAxisymmetricVorticity`, `spatialCurl_velocitySlice_spacetimeAxisymmetricVelocity`,
  `spacetimeAxisymmetricVorticity_timeSpaceCons_eq_cartesianVector`: the time-dependent
  vorticity is the spatial curl of each slice, with its explicit Cartesian formula.
* `spacetimeAxisymmetricVelocity_apply_two_of_mem_symmetryAxis`,
  `spacetimeAxisymmetricVorticity_apply_two_of_mem_symmetryAxis`: on the axis the velocity and
  vorticity are purely axial with values `2 Ψ(t, 0, z)` and `2 U(t, 0, z)`.

## How it works

Since `spacetimeAxisymmetricVelocity U Ψ` is defined slice by slice from `profileSlice U t` and
`profileSlice Ψ t`, divergence, curl and axis values are the spatial results applied at each time
(`velocitySlice_spacetimeAxisymmetricVelocity`). For joint regularity we write each velocity
component through `spacetimeSquaredCylindricalLift`, the composition with the smooth map
`(t, x) ↦ (t, x₁² + x₂², x₃)`, so `contDiff_spacetimeAxisymmetricVelocity` follows from the
smoothness of that map. The vorticity of smooth profiles is jointly smooth because its curl is a
combination of spacetime partial derivatives of the joint velocity
(`spacetimeAxisymmetricVorticity_timeSpaceCons_eq_spacetimeDerivatives`). The local versions reduce
to the global one. Profiles that are `C^m` near a point agree there with globally `C^m` profiles of
compact support (`ContDiffAt.exists_contDiff_compactSupport_eventuallyEq`), and velocities built
from profiles that agree near the image point agree near the point itself
(`spacetimeAxisymmetricVelocity_eventuallyEq`).
-/

@[expose] public section

open PDE (SpaceTime time)

namespace AxisymmetricFlow

open EuclideanSpace
open IncompressibleFlow
open PDE.Common
open PDE.CoordinateSystems

noncomputable section

/-- The fixed-time spatial slice of a profile on `(t, s, z)` spacetime. -/
def profileSlice (Φ : SpaceTime 2 → ℝ) (t : ℝ) : ℝ^2 → ℝ :=
  fun q ↦ Φ (timeSpaceCons t q)

/-- Evaluating a profile slice is evaluating the profile at `(t, q)`. -/
@[simp]
theorem profileSlice_apply (Φ : SpaceTime 2 → ℝ) (t : ℝ) (q : ℝ^2) :
    profileSlice Φ t q = Φ (timeSpaceCons t q) :=
  rfl

/-- Joint profile regularity restricts to every fixed-time profile slice. -/
theorem contDiff_profileSlice {n : ℕ∞} {Φ : SpaceTime 2 → ℝ}
    (hΦ : ContDiff ℝ n Φ) (t : ℝ) :
    ContDiff ℝ n (profileSlice Φ t) := by
  exact hΦ.comp (contDiff_timeSpaceCons_spatial 2 t)

/-- A spatial derivative of a fixed-time profile slice is the corresponding
spacetime coordinate derivative. -/
theorem partialDeriv_profileSlice
    {Φ : SpaceTime 2 → ℝ} (hΦ : Differentiable ℝ Φ)
    (i : Fin 2) (t : ℝ) (q : ℝ^2) :
    (∂[i] (profileSlice Φ t)) q =
      profileSlice (∂[i.succ] Φ) t q := by
  exact PDE.partialDeriv_timeSpaceCons_spatial i Φ t q hΦ.differentiableAt

/-- Function-valued form of the profile-slice derivative identity. -/
theorem partialDeriv_profileSlice_eq
    {Φ : SpaceTime 2 → ℝ} (hΦ : Differentiable ℝ Φ)
    (i : Fin 2) (t : ℝ) :
    (fun q ↦ (∂[i] (profileSlice Φ t)) q) =
      profileSlice (∂[i.succ] Φ) t := by
  funext q
  exact partialDeriv_profileSlice hΦ i t q

/-- The smooth spacetime map from time and Cartesian coordinates to time,
squared radius, and axial position. -/
def spacetimeSquaredCylindricalMap (xt : SpaceTime 3) : SpaceTime 2 :=
  timeSpaceCons (time xt) (squaredCylindricalMap (spatialPart xt))

/-- The spacetime squared-cylindrical map fixes time and applies `squaredCylindricalMap` to the
spatial part. -/
@[simp]
theorem spacetimeSquaredCylindricalMap_timeSpaceCons
    (t : ℝ) (x : ℝ^3) :
    spacetimeSquaredCylindricalMap (timeSpaceCons t x) =
      timeSpaceCons t (squaredCylindricalMap x) := by
  simp [spacetimeSquaredCylindricalMap]

/-- The squared cylindrical spacetime map is smooth through the axis. -/
theorem contDiff_spacetimeSquaredCylindricalMap {n : ℕ∞} :
    ContDiff ℝ n spacetimeSquaredCylindricalMap := by
  have ht : ContDiff ℝ n (fun xt : SpaceTime 3 ↦ time xt) :=
    (timeCLM 3).contDiff
  have hx : ContDiff ℝ n (fun xt : SpaceTime 3 ↦ spatialPart xt) :=
    (spatialPartCLM 3).contDiff
  have hsq : ContDiff ℝ n squaredCylindricalMap :=
    contDiff_squaredCylindricalMap.of_le
      (WithTop.coe_le_coe.mpr le_top)
  exact (contDiff_timeSpaceCons_uncurry 2).comp
    (ht.prodMk (hsq.comp hx))

/-- Lift a time-dependent squared-radius profile to Cartesian spacetime. -/
def spacetimeSquaredCylindricalLift
    (Φ : SpaceTime 2 → ℝ) (xt : SpaceTime 3) : ℝ :=
  Φ (spacetimeSquaredCylindricalMap xt)

/-- At a fixed time the spacetime lift is the spatial lift of the profile slice. -/
@[simp]
theorem spacetimeSquaredCylindricalLift_timeSpaceCons
    (Φ : SpaceTime 2 → ℝ) (t : ℝ) (x : ℝ^3) :
    spacetimeSquaredCylindricalLift Φ (timeSpaceCons t x) =
      squaredCylindricalLift (profileSlice Φ t) x := by
  simp [spacetimeSquaredCylindricalLift, squaredCylindricalLift]

/-- Joint profile regularity is preserved by the spacetime squared-radius
lift. -/
theorem contDiff_spacetimeSquaredCylindricalLift {n : ℕ∞}
    {Φ : SpaceTime 2 → ℝ} (hΦ : ContDiff ℝ n Φ) :
    ContDiff ℝ n (spacetimeSquaredCylindricalLift Φ) :=
  hΦ.comp contDiff_spacetimeSquaredCylindricalMap

/-- Time-dependent meridional velocity reconstructed one spatial slice at a
time. -/
def spacetimeMeridionalVelocity (Ψ : SpaceTime 2 → ℝ) :
    SpaceTime 3 → ℝ^3 :=
  fun xt ↦ meridionalVelocity (profileSlice Ψ (time xt)) (spatialPart xt)

/-- Time-dependent swirl velocity reconstructed one spatial slice at a time. -/
def spacetimeSwirlVelocity (U : SpaceTime 2 → ℝ) :
    SpaceTime 3 → ℝ^3 :=
  fun xt ↦ swirlVelocity (profileSlice U (time xt)) (spatialPart xt)

/-- Time-dependent axisymmetric velocity reconstructed from squared-radius
swirl and streamfunction profiles. -/
def spacetimeAxisymmetricVelocity (U Ψ : SpaceTime 2 → ℝ) :
    SpaceTime 3 → ℝ^3 :=
  fun xt ↦ axisymmetricVelocity
    (profileSlice U (time xt)) (profileSlice Ψ (time xt)) (spatialPart xt)

/-- At a fixed time the spacetime meridional velocity is the spatial reconstruction from the
streamfunction slice. -/
@[simp]
theorem spacetimeMeridionalVelocity_timeSpaceCons
    (Ψ : SpaceTime 2 → ℝ) (t : ℝ) (x : ℝ^3) :
    spacetimeMeridionalVelocity Ψ (timeSpaceCons t x) =
      meridionalVelocity (profileSlice Ψ t) x := by
  simp [spacetimeMeridionalVelocity]

/-- At a fixed time the spacetime swirl velocity is the spatial reconstruction from the swirl
slice. -/
@[simp]
theorem spacetimeSwirlVelocity_timeSpaceCons
    (U : SpaceTime 2 → ℝ) (t : ℝ) (x : ℝ^3) :
    spacetimeSwirlVelocity U (timeSpaceCons t x) =
      swirlVelocity (profileSlice U t) x := by
  simp [spacetimeSwirlVelocity]

/-- At a fixed time the spacetime axisymmetric velocity is the spatial reconstruction from the
two profile slices. -/
@[simp]
theorem spacetimeAxisymmetricVelocity_timeSpaceCons
    (U Ψ : SpaceTime 2 → ℝ) (t : ℝ) (x : ℝ^3) :
    spacetimeAxisymmetricVelocity U Ψ (timeSpaceCons t x) =
      axisymmetricVelocity (profileSlice U t) (profileSlice Ψ t) x := by
  simp [spacetimeAxisymmetricVelocity]

/-- The fixed-time slice of the spacetime meridional field is exactly the
spatial meridional reconstruction. -/
theorem velocitySlice_spacetimeMeridionalVelocity
    (Ψ : SpaceTime 2 → ℝ) (t : ℝ) :
    velocitySlice (spacetimeMeridionalVelocity Ψ) t =
      meridionalVelocity (profileSlice Ψ t) := by
  funext x
  exact spacetimeMeridionalVelocity_timeSpaceCons Ψ t x

/-- The fixed-time slice of the spacetime swirl field is exactly the spatial
swirl reconstruction. -/
theorem velocitySlice_spacetimeSwirlVelocity
    (U : SpaceTime 2 → ℝ) (t : ℝ) :
    velocitySlice (spacetimeSwirlVelocity U) t =
      swirlVelocity (profileSlice U t) := by
  funext x
  exact spacetimeSwirlVelocity_timeSpaceCons U t x

/-- The fixed-time slice of the spacetime velocity is exactly the spatial
axisymmetric reconstruction. -/
theorem velocitySlice_spacetimeAxisymmetricVelocity
    (U Ψ : SpaceTime 2 → ℝ) (t : ℝ) :
    velocitySlice (spacetimeAxisymmetricVelocity U Ψ) t =
      axisymmetricVelocity (profileSlice U t) (profileSlice Ψ t) := by
  funext x
  exact spacetimeAxisymmetricVelocity_timeSpaceCons U Ψ t x

/-- The spacetime reconstruction is the sum of its meridional and swirl
parts. -/
theorem spacetimeAxisymmetricVelocity_eq_add
    (U Ψ : SpaceTime 2 → ℝ) :
    spacetimeAxisymmetricVelocity U Ψ =
      fun xt ↦ spacetimeMeridionalVelocity Ψ xt +
        spacetimeSwirlVelocity U xt := by
  funext xt
  rfl

/-- First Cartesian component of the reconstructed velocity at `(t,x)`. -/
theorem spacetimeAxisymmetricVelocity_timeSpaceCons_apply_zero
    (U Ψ : SpaceTime 2 → ℝ) (t : ℝ) (x : ℝ^3) :
    spacetimeAxisymmetricVelocity U Ψ (timeSpaceCons t x) 0 =
      -x 0 * squaredCylindricalLift
          (fun q ↦ (∂[(1 : Fin 2)] (profileSlice Ψ t)) q) x -
        x 1 * squaredCylindricalLift (profileSlice U t) x := by
  rw [spacetimeAxisymmetricVelocity_timeSpaceCons]
  exact axisymmetricVelocity_apply_zero _ _ _

/-- Second Cartesian component of the reconstructed velocity at `(t,x)`. -/
theorem spacetimeAxisymmetricVelocity_timeSpaceCons_apply_one
    (U Ψ : SpaceTime 2 → ℝ) (t : ℝ) (x : ℝ^3) :
    spacetimeAxisymmetricVelocity U Ψ (timeSpaceCons t x) 1 =
      -x 1 * squaredCylindricalLift
          (fun q ↦ (∂[(1 : Fin 2)] (profileSlice Ψ t)) q) x +
        x 0 * squaredCylindricalLift (profileSlice U t) x := by
  rw [spacetimeAxisymmetricVelocity_timeSpaceCons]
  exact axisymmetricVelocity_apply_one _ _ _

/-- Axial Cartesian component of the reconstructed velocity at `(t,x)`. -/
theorem spacetimeAxisymmetricVelocity_timeSpaceCons_apply_two
    (U Ψ : SpaceTime 2 → ℝ) (t : ℝ) (x : ℝ^3) :
    spacetimeAxisymmetricVelocity U Ψ (timeSpaceCons t x) 2 =
      2 * squaredCylindricalLift (profileSlice Ψ t) x +
        2 * cylindricalRadiusSq x * squaredCylindricalLift
          (fun q ↦ (∂[(0 : Fin 2)] (profileSlice Ψ t)) q) x := by
  rw [spacetimeAxisymmetricVelocity_timeSpaceCons]
  exact axisymmetricVelocity_apply_two _ _ _

/-- Division-free joint-spacetime formula for the reconstructed velocity. -/
theorem spacetimeAxisymmetricVelocity_timeSpaceCons_eq_cartesianVector
    {U Ψ : SpaceTime 2 → ℝ} (hΨ : Differentiable ℝ Ψ)
    (t : ℝ) (x : ℝ^3) :
    spacetimeAxisymmetricVelocity U Ψ (timeSpaceCons t x) =
      cartesianVector
        (-x 0 * spacetimeSquaredCylindricalLift
            (∂[(2 : Fin 3)] Ψ) (timeSpaceCons t x) -
          x 1 * spacetimeSquaredCylindricalLift U (timeSpaceCons t x))
        (-x 1 * spacetimeSquaredCylindricalLift
            (∂[(2 : Fin 3)] Ψ) (timeSpaceCons t x) +
          x 0 * spacetimeSquaredCylindricalLift U (timeSpaceCons t x))
        (2 * spacetimeSquaredCylindricalLift Ψ (timeSpaceCons t x) +
          2 * cylindricalRadiusSq x *
            spacetimeSquaredCylindricalLift
              (∂[(1 : Fin 3)] Ψ) (timeSpaceCons t x)) := by
  rw [spacetimeAxisymmetricVelocity_timeSpaceCons]
  simp only [axisymmetricVelocity, meridionalVelocity, swirlVelocity]
  rw [partialDeriv_profileSlice_eq hΨ (1 : Fin 2) t]
  rw [partialDeriv_profileSlice_eq hΨ (0 : Fin 2) t]
  ext i
  fin_cases i <;>
    (simp [spacetimeSquaredCylindricalLift_timeSpaceCons,
      cartesianVector]; try ring)

/-- A `C^n` swirl profile and a `C^(n+1)` streamfunction reconstruct a jointly `C^n`
Cartesian velocity. The extra streamfunction derivative comes from the meridional velocity. -/
theorem contDiff_spacetimeAxisymmetricVelocity {n : ℕ∞}
    {U Ψ : SpaceTime 2 → ℝ}
    (hU : ContDiff ℝ n U)
    (hΨ : ContDiff ℝ (n + 1) Ψ) :
    ContDiff ℝ n (spacetimeAxisymmetricVelocity U Ψ) := by
  have hΨDeriv : ContDiff ℝ n (fderiv ℝ Ψ) :=
    hΨ.fderiv_right (by simp)
  have hΨS : ContDiff ℝ n
      (∂[(1 : Fin 3)] Ψ) :=
    hΨDeriv.clm_apply contDiff_const
  have hΨZ : ContDiff ℝ n
      (∂[(2 : Fin 3)] Ψ) :=
    hΨDeriv.clm_apply contDiff_const
  have hULift : ContDiff ℝ n
      (spacetimeSquaredCylindricalLift U) :=
    contDiff_spacetimeSquaredCylindricalLift hU
  have hΨLift : ContDiff ℝ n
      (spacetimeSquaredCylindricalLift Ψ) :=
    contDiff_spacetimeSquaredCylindricalLift (hΨ.of_le (by simp))
  have hΨSLift : ContDiff ℝ n
      (spacetimeSquaredCylindricalLift (∂[(1 : Fin 3)] Ψ)) :=
    contDiff_spacetimeSquaredCylindricalLift hΨS
  have hΨZLift : ContDiff ℝ n
      (spacetimeSquaredCylindricalLift (∂[(2 : Fin 3)] Ψ)) :=
    contDiff_spacetimeSquaredCylindricalLift hΨZ
  have hspatial : ContDiff ℝ n
      (fun xt : SpaceTime 3 ↦ spatialPart xt) :=
    (spatialPartCLM 3).contDiff
  have hx0 : ContDiff ℝ n
      (fun xt : SpaceTime 3 ↦ spatialPart xt 0) := by
    cas
  have hx1 : ContDiff ℝ n
      (fun xt : SpaceTime 3 ↦ spatialPart xt 1) := by
    cas
  have hrsq : ContDiff ℝ n
      (fun xt : SpaceTime 3 ↦ cylindricalRadiusSq (spatialPart xt)) := by
    change ContDiff ℝ n (fun xt : SpaceTime 3 ↦
      spatialPart xt 0 ^ 2 + spatialPart xt 1 ^ 2)
    fun_prop
  rw [show
    spacetimeAxisymmetricVelocity U Ψ =
      fun xt ↦ cartesianVector
        (-(spatialPart xt 0) * spacetimeSquaredCylindricalLift
            (∂[(2 : Fin 3)] Ψ) xt -
          spatialPart xt 1 * spacetimeSquaredCylindricalLift U xt)
        (-(spatialPart xt 1) * spacetimeSquaredCylindricalLift
            (∂[(2 : Fin 3)] Ψ) xt +
          spatialPart xt 0 * spacetimeSquaredCylindricalLift U xt)
        (2 * spacetimeSquaredCylindricalLift Ψ xt +
          2 * cylindricalRadiusSq (spatialPart xt) *
            spacetimeSquaredCylindricalLift
              (∂[(1 : Fin 3)] Ψ) xt) by
      funext xt
      simpa [time] using
        spacetimeAxisymmetricVelocity_timeSpaceCons_eq_cartesianVector
          (hΨ.differentiable (by simp)) (time xt) (spatialPart xt)]
  apply (contDiff_piLp (2 : ENNReal)).2
  intro i
  fin_cases i
  · change ContDiff ℝ n (fun xt : SpaceTime 3 ↦
      -(spatialPart xt 0) *
          spacetimeSquaredCylindricalLift
            (∂[(2 : Fin 3)] Ψ) xt -
        spatialPart xt 1 * spacetimeSquaredCylindricalLift U xt)
    exact (hx0.neg.mul hΨZLift).sub (hx1.mul hULift)
  · change ContDiff ℝ n (fun xt : SpaceTime 3 ↦
      -(spatialPart xt 1) *
          spacetimeSquaredCylindricalLift
            (∂[(2 : Fin 3)] Ψ) xt +
        spatialPart xt 0 * spacetimeSquaredCylindricalLift U xt)
    exact (hx1.neg.mul hΨZLift).add (hx0.mul hULift)
  · change ContDiff ℝ n (fun xt : SpaceTime 3 ↦
      2 * spacetimeSquaredCylindricalLift Ψ xt +
        2 * cylindricalRadiusSq (spatialPart xt) *
          spacetimeSquaredCylindricalLift
            (∂[(1 : Fin 3)] Ψ) xt)
    exact (contDiff_const.mul hΨLift).add
      ((contDiff_const.mul hrsq).mul hΨSLift)

/-- Reconstructed velocities have the same germ when their profiles agree near the corresponding
squared-radius spacetime point. No regularity is required away from that neighborhood. -/
theorem spacetimeAxisymmetricVelocity_eventuallyEq
    {U U' Ψ Ψ' : SpaceTime 2 → ℝ} {xt : SpaceTime 3}
    (hU : U =ᶠ[nhds (spacetimeSquaredCylindricalMap xt)] U')
    (hΨ : Ψ =ᶠ[nhds (spacetimeSquaredCylindricalMap xt)] Ψ') :
    spacetimeAxisymmetricVelocity U Ψ =ᶠ[nhds xt]
      spacetimeAxisymmetricVelocity U' Ψ' := by
  have hmap : ContinuousAt spacetimeSquaredCylindricalMap xt :=
    (contDiff_spacetimeSquaredCylindricalMap (n := 0)).continuous.continuousAt
  filter_upwards [hU.comp_tendsto hmap,
    hmap.eventually hΨ.eventuallyEq_nhds] with y hyU hyΨ
  have hslice : profileSlice Ψ (time y) =ᶠ[nhds (squaredCylindricalMap (spatialPart y))]
      profileSlice Ψ' (time y) :=
    hyΨ.comp_tendsto
      (contDiff_timeSpaceCons_spatial 2 (time y) (m := 0)).continuous.continuousAt
  have hzero := (hslice.partialDeriv (0 : Fin 2)).eq_of_nhds
  have hone := (hslice.partialDeriv (1 : Fin 2)).eq_of_nhds
  have hvalue := hslice.eq_of_nhds
  change profileSlice U (time y) (squaredCylindricalMap (spatialPart y)) =
    profileSlice U' (time y) (squaredCylindricalMap (spatialPart y)) at hyU
  simp only [spacetimeAxisymmetricVelocity, axisymmetricVelocity, meridionalVelocity,
    swirlVelocity, squaredCylindricalLift, hzero, hone, hvalue, hyU]

/-- Local finite-order profile regularity suffices for local joint velocity regularity,
including on the symmetry axis. No condition is imposed at an excluded terminal time. -/
theorem contDiffAt_spacetimeAxisymmetricVelocity {m : ℕ}
    {U Ψ : SpaceTime 2 → ℝ} {xt : SpaceTime 3}
    (hU : ContDiffAt ℝ m U (spacetimeSquaredCylindricalMap xt))
    (hΨ : ContDiffAt ℝ (m + 1) Ψ (spacetimeSquaredCylindricalMap xt)) :
    ContDiffAt ℝ m (spacetimeAxisymmetricVelocity U Ψ) xt := by
  obtain ⟨U', hU', _hUcompact, hUeq⟩ := hU.exists_contDiff_compactSupport_eventuallyEq
  obtain ⟨Ψ', hΨ', _hΨcompact, hΨeq⟩ := hΨ.exists_contDiff_compactSupport_eventuallyEq
  exact (contDiff_spacetimeAxisymmetricVelocity (n := m) hU' hΨ').contDiffAt
    |>.congr_of_eventuallyEq (spacetimeAxisymmetricVelocity_eventuallyEq hUeq hΨeq)

/-- Profiles smooth at a squared-radius spacetime point give a velocity smooth at the
corresponding Cartesian point, without a global smooth extension of the profiles. -/
theorem contDiffAt_top_spacetimeAxisymmetricVelocity
    {U Ψ : SpaceTime 2 → ℝ} {xt : SpaceTime 3}
    (hU : ContDiffAt ℝ (⊤ : ℕ∞) U (spacetimeSquaredCylindricalMap xt))
    (hΨ : ContDiffAt ℝ (⊤ : ℕ∞) Ψ (spacetimeSquaredCylindricalMap xt)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (spacetimeAxisymmetricVelocity U Ψ) xt := by
  apply contDiffAt_infty.mpr
  intro m
  exact contDiffAt_spacetimeAxisymmetricVelocity
    (contDiffAt_infty.mp hU m) (contDiffAt_infty.mp hΨ (m + 1))

/-- A smooth spacetime streamfunction gives a smooth meridional velocity on
every fixed-time spatial slice. -/
theorem contDiff_velocitySlice_spacetimeMeridionalVelocity
    {Ψ : SpaceTime 2 → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (velocitySlice (spacetimeMeridionalVelocity Ψ) t) := by
  rw [velocitySlice_spacetimeMeridionalVelocity]
  exact contDiff_meridionalVelocity (contDiff_profileSlice hΨ t)

/-- A smooth spacetime swirl profile gives a smooth swirl velocity on every
fixed-time spatial slice. -/
theorem contDiff_velocitySlice_spacetimeSwirlVelocity
    {U : SpaceTime 2 → ℝ} (hU : ContDiff ℝ (⊤ : ℕ∞) U) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (velocitySlice (spacetimeSwirlVelocity U) t) := by
  rw [velocitySlice_spacetimeSwirlVelocity]
  exact contDiff_swirlVelocity (contDiff_profileSlice hU t)

/-- Smooth spacetime profiles give a smooth axisymmetric velocity on every
fixed-time spatial slice, including at the symmetry axis. -/
theorem contDiff_velocitySlice_spacetimeAxisymmetricVelocity
    {U Ψ : SpaceTime 2 → ℝ} (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (velocitySlice (spacetimeAxisymmetricVelocity U Ψ) t) := by
  rw [velocitySlice_spacetimeAxisymmetricVelocity]
  exact contDiff_axisymmetricVelocity
    (contDiff_profileSlice hU t) (contDiff_profileSlice hΨ t)

/-- The finite regularity needed for the divergence and curl identities is
inherited by every fixed-time velocity slice. -/
theorem contDiff_one_velocitySlice_spacetimeAxisymmetricVelocity
    {U Ψ : SpaceTime 2 → ℝ} (hU : ContDiff ℝ 1 U)
    (hΨ : ContDiff ℝ 2 Ψ) (t : ℝ) :
    ContDiff ℝ 1
      (velocitySlice (spacetimeAxisymmetricVelocity U Ψ) t) := by
  rw [velocitySlice_spacetimeAxisymmetricVelocity]
  exact (contDiff_one_meridionalVelocity (contDiff_profileSlice hΨ t)).add
    (contDiff_one_swirlVelocity (contDiff_profileSlice hU t))

/-- Every fixed-time meridional slice is divergence free. -/
theorem spatialFieldDivergence_velocitySlice_spacetimeMeridionalVelocity_eq_zero
    {Ψ : SpaceTime 2 → ℝ} (hΨ : ContDiff ℝ 2 Ψ)
    (t : ℝ) (x : ℝ^3) :
    ∇· (velocitySlice (spacetimeMeridionalVelocity Ψ) t) x = 0 := by
  rw [velocitySlice_spacetimeMeridionalVelocity]
  exact spatialFieldDivergence_meridionalVelocity_eq_zero
    (contDiff_profileSlice hΨ t) x

/-- Every fixed-time swirl slice is divergence free. -/
theorem spatialFieldDivergence_velocitySlice_spacetimeSwirlVelocity_eq_zero
    {U : SpaceTime 2 → ℝ} (hU : ContDiff ℝ 1 U)
    (t : ℝ) (x : ℝ^3) :
    ∇· (velocitySlice (spacetimeSwirlVelocity U) t) x = 0 := by
  rw [velocitySlice_spacetimeSwirlVelocity]
  exact spatialFieldDivergence_swirlVelocity_eq_zero
    (contDiff_profileSlice hU t) x

/-- Every fixed-time reconstructed velocity slice is divergence free on all
of Cartesian space. -/
theorem spatialFieldDivergence_velocitySlice_spacetimeAxisymmetricVelocity_eq_zero
    {U Ψ : SpaceTime 2 → ℝ} (hU : ContDiff ℝ 1 U)
    (hΨ : ContDiff ℝ 2 Ψ) (t : ℝ) (x : ℝ^3) :
    ∇· (velocitySlice (spacetimeAxisymmetricVelocity U Ψ) t) x = 0 := by
  rw [velocitySlice_spacetimeAxisymmetricVelocity]
  exact spatialFieldDivergence_axisymmetricVelocity_eq_zero
    (contDiff_profileSlice hU t) (contDiff_profileSlice hΨ t) x

/-- The complete fixed-time spatial velocity field is divergence free. -/
theorem spatialFieldDivergenceFree_velocitySlice_spacetimeAxisymmetricVelocity
    {U Ψ : SpaceTime 2 → ℝ} (hU : ContDiff ℝ 1 U)
    (hΨ : ContDiff ℝ 2 Ψ) (t : ℝ) :
    SpatialFieldDivergenceFree
      (velocitySlice (spacetimeAxisymmetricVelocity U Ψ) t) :=
  fun x ↦
    spatialFieldDivergence_velocitySlice_spacetimeAxisymmetricVelocity_eq_zero
      hU hΨ t x

/-- Time-dependent vorticity, defined as the spatial curl of the reconstructed
velocity at each fixed time. -/
def spacetimeAxisymmetricVorticity (U Ψ : SpaceTime 2 → ℝ) :
    SpaceTime 3 → ℝ^3 :=
  fun xt ↦ spatialCurl
    (axisymmetricVelocity
      (profileSlice U (time xt)) (profileSlice Ψ (time xt)))
    (spatialPart xt)

/-- At a fixed time the spacetime vorticity is the spatial curl of the reconstructed velocity
slice. -/
@[simp]
theorem spacetimeAxisymmetricVorticity_timeSpaceCons
    (U Ψ : SpaceTime 2 → ℝ) (t : ℝ) (x : ℝ^3) :
    spacetimeAxisymmetricVorticity U Ψ (timeSpaceCons t x) =
      spatialCurl
        (axisymmetricVelocity (profileSlice U t) (profileSlice Ψ t)) x := by
  simp [spacetimeAxisymmetricVorticity]

/-- The fixed-time curl can be written using the spatial coordinate
derivatives of the joint spacetime velocity. -/
theorem spacetimeAxisymmetricVorticity_timeSpaceCons_eq_spacetimeDerivatives
    {U Ψ : SpaceTime 2 → ℝ}
    (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (t : ℝ) (x : ℝ^3) :
    spacetimeAxisymmetricVorticity U Ψ (timeSpaceCons t x) =
      cartesianVector
        ((∂[(2 : Fin 4)]
            (fun xt ↦ spacetimeAxisymmetricVelocity U Ψ xt 2))
            (timeSpaceCons t x) -
          (∂[(3 : Fin 4)]
            (fun xt ↦ spacetimeAxisymmetricVelocity U Ψ xt 1))
            (timeSpaceCons t x))
        ((∂[(3 : Fin 4)]
            (fun xt ↦ spacetimeAxisymmetricVelocity U Ψ xt 0))
            (timeSpaceCons t x) -
          (∂[(1 : Fin 4)]
            (fun xt ↦ spacetimeAxisymmetricVelocity U Ψ xt 2))
            (timeSpaceCons t x))
        ((∂[(1 : Fin 4)]
            (fun xt ↦ spacetimeAxisymmetricVelocity U Ψ xt 1))
            (timeSpaceCons t x) -
          (∂[(2 : Fin 4)]
            (fun xt ↦ spacetimeAxisymmetricVelocity U Ψ xt 0))
            (timeSpaceCons t x)) := by
  let u := spacetimeAxisymmetricVelocity U Ψ
  have hu : ContDiff ℝ (⊤ : ℕ∞) u :=
    contDiff_spacetimeAxisymmetricVelocity hU hΨ
  have huComponent (j : Fin 3) :
      Differentiable ℝ (fun xt ↦ u xt j) := by
    have h :=
      (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hu
    exact h.differentiable (by simp)
  have hslice (i : Fin 3) (j : Fin 3) :
      (∂[i] (fun y ↦ velocitySlice u t y j)) x =
        (∂[i.succ] (fun xt ↦ u xt j))
          (timeSpaceCons t x) :=
    PDE.partialDeriv_timeSpaceCons_spatial i (fun xt ↦ u xt j) t x
      (huComponent j).differentiableAt
  rw [spacetimeAxisymmetricVorticity_timeSpaceCons]
  rw [← velocitySlice_spacetimeAxisymmetricVelocity U Ψ t]
  change spatialCurl (velocitySlice u t) x = _
  ext i
  fin_cases i <;>
    simp [spatialCurl, cartesianVector, hslice, u]

/-- Smooth profile data reconstruct a jointly smooth Cartesian spacetime
vorticity, defined by the spatial curl of the reconstructed velocity. -/
theorem contDiff_spacetimeAxisymmetricVorticity
    {U Ψ : SpaceTime 2 → ℝ}
    (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (spacetimeAxisymmetricVorticity U Ψ) := by
  let u := spacetimeAxisymmetricVelocity U Ψ
  have hu : ContDiff ℝ (⊤ : ℕ∞) u :=
    contDiff_spacetimeAxisymmetricVelocity hU hΨ
  have huComponent (j : Fin 3) :
      ContDiff ℝ (⊤ : ℕ∞) (fun xt ↦ u xt j) := by
    have h :=
      (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hu
    change ContDiff ℝ (⊤ : ℕ∞) (fun xt ↦ u xt j) at h
    exact h
  have huDerivative (i : Fin 4) (j : Fin 3) :
      ContDiff ℝ (⊤ : ℕ∞)
        (∂[i] (fun xt ↦ u xt j)) :=
    PDE.contDiff_top_partialDeriv (huComponent j)
  rw [show
    spacetimeAxisymmetricVorticity U Ψ =
      fun xt ↦ cartesianVector
        ((∂[(2 : Fin 4)] (fun yt ↦ u yt 2)) xt -
          (∂[(3 : Fin 4)] (fun yt ↦ u yt 1)) xt)
        ((∂[(3 : Fin 4)] (fun yt ↦ u yt 0)) xt -
          (∂[(1 : Fin 4)] (fun yt ↦ u yt 2)) xt)
        ((∂[(1 : Fin 4)] (fun yt ↦ u yt 1)) xt -
          (∂[(2 : Fin 4)] (fun yt ↦ u yt 0)) xt) by
      funext xt
      simpa [time, u] using
        spacetimeAxisymmetricVorticity_timeSpaceCons_eq_spacetimeDerivatives
          hU hΨ (time xt) (spatialPart xt)]
  apply (contDiff_piLp (2 : ENNReal)).2
  intro i
  fin_cases i
  · change ContDiff ℝ (⊤ : ℕ∞) (fun xt ↦
      (∂[(2 : Fin 4)] (fun yt ↦ u yt 2)) xt -
        (∂[(3 : Fin 4)] (fun yt ↦ u yt 1)) xt)
    exact (huDerivative 2 2).sub (huDerivative 3 1)
  · change ContDiff ℝ (⊤ : ℕ∞) (fun xt ↦
      (∂[(3 : Fin 4)] (fun yt ↦ u yt 0)) xt -
        (∂[(1 : Fin 4)] (fun yt ↦ u yt 2)) xt)
    exact (huDerivative 3 0).sub (huDerivative 1 2)
  · change ContDiff ℝ (⊤ : ℕ∞) (fun xt ↦
      (∂[(1 : Fin 4)] (fun yt ↦ u yt 1)) xt -
        (∂[(2 : Fin 4)] (fun yt ↦ u yt 0)) xt)
    exact (huDerivative 1 1).sub (huDerivative 2 0)

/-- The reconstructed spacetime vorticity is exactly the spatial curl of each
velocity slice. -/
theorem spatialCurl_velocitySlice_spacetimeAxisymmetricVelocity
    (U Ψ : SpaceTime 2 → ℝ) (t : ℝ) (x : ℝ^3) :
    spatialCurl (velocitySlice (spacetimeAxisymmetricVelocity U Ψ) t) x =
      spacetimeAxisymmetricVorticity U Ψ (timeSpaceCons t x) := by
  rw [velocitySlice_spacetimeAxisymmetricVelocity]
  exact (spacetimeAxisymmetricVorticity_timeSpaceCons U Ψ t x).symm

/-- Exact Cartesian formula for the time-dependent vorticity. -/
theorem spacetimeAxisymmetricVorticity_timeSpaceCons_eq_cartesianVector
    {U Ψ : SpaceTime 2 → ℝ} (hU : ContDiff ℝ 1 U)
    (hΨ : ContDiff ℝ 2 Ψ) (t : ℝ) (x : ℝ^3) :
    spacetimeAxisymmetricVorticity U Ψ (timeSpaceCons t x) =
      cartesianVector
        (x 1 * squaredCylindricalLift
            (meridionalVorticityCoefficient (profileSlice Ψ t)) x -
          x 0 * squaredCylindricalLift
            (fun q ↦ (∂[(1 : Fin 2)] (profileSlice U t)) q) x)
        (-x 0 * squaredCylindricalLift
            (meridionalVorticityCoefficient (profileSlice Ψ t)) x -
          x 1 * squaredCylindricalLift
            (fun q ↦ (∂[(1 : Fin 2)] (profileSlice U t)) q) x)
        (2 * squaredCylindricalLift (profileSlice U t) x +
          2 * cylindricalRadiusSq x * squaredCylindricalLift
            (fun q ↦ (∂[(0 : Fin 2)] (profileSlice U t)) q) x) := by
  rw [spacetimeAxisymmetricVorticity_timeSpaceCons]
  exact spatialCurl_axisymmetricVelocity
    (contDiff_profileSlice hU t) (contDiff_profileSlice hΨ t) x

/-- The azimuthal-vorticity coefficient of a smooth streamfunction profile is
smooth. -/
theorem contDiff_meridionalVorticityCoefficient
    {Ψ : ℝ^2 → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (meridionalVorticityCoefficient Ψ) := by
  have hΨS : ContDiff ℝ (⊤ : ℕ∞)
      (fun q ↦ (∂[(0 : Fin 2)] Ψ) q) :=
    PDE.contDiff_top_partialDeriv hΨ
  have hΨSS : ContDiff ℝ (⊤ : ℕ∞)
      (fun q ↦ (∂[(0 : Fin 2)]
        (fun p ↦ (∂[(0 : Fin 2)] Ψ) p)) q) :=
    PDE.contDiff_top_partialDeriv hΨS
  have hΨZ : ContDiff ℝ (⊤ : ℕ∞)
      (fun q ↦ (∂[(1 : Fin 2)] Ψ) q) :=
    PDE.contDiff_top_partialDeriv hΨ
  have hΨZZ : ContDiff ℝ (⊤ : ℕ∞)
      (fun q ↦ (∂[(1 : Fin 2)]
        (fun p ↦ (∂[(1 : Fin 2)] Ψ) p)) q) :=
    PDE.contDiff_top_partialDeriv hΨZ
  have hq : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ^2 ↦ q 0) := by
    fun_prop
  have hEight : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ^2 ↦ (8 : ℝ)) :=
    contDiff_const
  have hFour : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ^2 ↦ (4 : ℝ)) :=
    contDiff_const
  change ContDiff ℝ (⊤ : ℕ∞) (fun q ↦
    (∂[(1 : Fin 2)]
        (fun p ↦ (∂[(1 : Fin 2)] Ψ) p)) q +
      8 * (∂[(0 : Fin 2)] Ψ) q +
      4 * q 0 * (∂[(0 : Fin 2)]
        (fun p ↦ (∂[(0 : Fin 2)] Ψ) p)) q)
  exact (hΨZZ.add (hEight.mul hΨS)).add ((hFour.mul hq).mul hΨSS)

/-- Smooth spacetime profiles give a smooth vorticity on every fixed-time
spatial slice. -/
theorem contDiff_spacetimeAxisymmetricVorticity_timeSlice
    {U Ψ : SpaceTime 2 → ℝ} (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x ↦ spacetimeAxisymmetricVorticity U Ψ (timeSpaceCons t x)) := by
  have hUt : ContDiff ℝ (⊤ : ℕ∞) (profileSlice U t) :=
    contDiff_profileSlice hU t
  have hΨt : ContDiff ℝ (⊤ : ℕ∞) (profileSlice Ψ t) :=
    contDiff_profileSlice hΨ t
  have hUtS : ContDiff ℝ (⊤ : ℕ∞)
      (fun q ↦ (∂[(0 : Fin 2)] (profileSlice U t)) q) :=
    PDE.contDiff_top_partialDeriv hUt
  have hUtZ : ContDiff ℝ (⊤ : ℕ∞)
      (fun q ↦ (∂[(1 : Fin 2)] (profileSlice U t)) q) :=
    PDE.contDiff_top_partialDeriv hUt
  have hK := contDiff_squaredCylindricalLift
    (contDiff_meridionalVorticityCoefficient hΨt)
  have hUlift := contDiff_squaredCylindricalLift hUt
  have hUSlift := contDiff_squaredCylindricalLift hUtS
  have hUZlift := contDiff_squaredCylindricalLift hUtZ
  have hx0 : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ^3 ↦ x 0) := by
    fun_prop
  have hx1 : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ^3 ↦ x 1) := by
    fun_prop
  have hs : ContDiff ℝ (⊤ : ℕ∞) cylindricalRadiusSq := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ^3 ↦ x 0 ^ 2 + x 1 ^ 2)
    fun_prop
  rw [show
    (fun x ↦ spacetimeAxisymmetricVorticity U Ψ (timeSpaceCons t x)) =
      fun x ↦ cartesianVector
        (x 1 * squaredCylindricalLift
            (meridionalVorticityCoefficient (profileSlice Ψ t)) x -
          x 0 * squaredCylindricalLift
            (fun q ↦ (∂[(1 : Fin 2)] (profileSlice U t)) q) x)
        (-x 0 * squaredCylindricalLift
            (meridionalVorticityCoefficient (profileSlice Ψ t)) x -
          x 1 * squaredCylindricalLift
            (fun q ↦ (∂[(1 : Fin 2)] (profileSlice U t)) q) x)
        (2 * squaredCylindricalLift (profileSlice U t) x +
          2 * cylindricalRadiusSq x * squaredCylindricalLift
            (fun q ↦ (∂[(0 : Fin 2)] (profileSlice U t)) q) x) by
      funext x
      exact spacetimeAxisymmetricVorticity_timeSpaceCons_eq_cartesianVector
        (hU.of_le (WithTop.coe_le_coe.mpr le_top))
        (hΨ.of_le (WithTop.coe_le_coe.mpr le_top)) t x]
  apply (contDiff_piLp (2 : ENNReal)).2
  intro i
  fin_cases i
  · change ContDiff ℝ (⊤ : ℕ∞) (fun x ↦
      x 1 * squaredCylindricalLift
          (meridionalVorticityCoefficient (profileSlice Ψ t)) x -
        x 0 * squaredCylindricalLift
          (fun q ↦ (∂[(1 : Fin 2)] (profileSlice U t)) q) x)
    exact (hx1.mul hK).sub (hx0.mul hUZlift)
  · change ContDiff ℝ (⊤ : ℕ∞) (fun x ↦
      -x 0 * squaredCylindricalLift
          (meridionalVorticityCoefficient (profileSlice Ψ t)) x -
        x 1 * squaredCylindricalLift
          (fun q ↦ (∂[(1 : Fin 2)] (profileSlice U t)) q) x)
    exact (hx0.neg.mul hK).sub (hx1.mul hUZlift)
  · change ContDiff ℝ (⊤ : ℕ∞) (fun x ↦
      2 * squaredCylindricalLift (profileSlice U t) x +
        2 * cylindricalRadiusSq x * squaredCylindricalLift
          (fun q ↦ (∂[(0 : Fin 2)] (profileSlice U t)) q) x)
    exact (contDiff_const.mul hUlift).add
      ((contDiff_const.mul hs).mul hUSlift)

/-- On the symmetry axis, both transverse components of the time-dependent
velocity vanish. -/
theorem spacetimeAxisymmetricVelocity_transverse_eq_zero_of_mem_symmetryAxis
    (U Ψ : SpaceTime 2 → ℝ) (t : ℝ) {x : ℝ^3}
    (hx : x ∈ symmetryAxis) :
    spacetimeAxisymmetricVelocity U Ψ (timeSpaceCons t x) 0 = 0 ∧
      spacetimeAxisymmetricVelocity U Ψ (timeSpaceCons t x) 1 = 0 := by
  rw [spacetimeAxisymmetricVelocity_timeSpaceCons]
  exact axisymmetricVelocity_transverse_eq_zero_of_mem_symmetryAxis
    (profileSlice U t) (profileSlice Ψ t) hx

/-- On the symmetry axis, the axial velocity is the regular value
`2 Ψ(t,0,z)`. -/
theorem spacetimeAxisymmetricVelocity_apply_two_of_mem_symmetryAxis
    (U Ψ : SpaceTime 2 → ℝ) (t : ℝ) {x : ℝ^3}
    (hx : x ∈ symmetryAxis) :
    spacetimeAxisymmetricVelocity U Ψ (timeSpaceCons t x) 2 =
      2 * squaredCylindricalLift (profileSlice Ψ t) x := by
  rw [spacetimeAxisymmetricVelocity_timeSpaceCons]
  exact axisymmetricVelocity_apply_two_of_mem_symmetryAxis
    (profileSlice U t) (profileSlice Ψ t) hx

/-- On the symmetry axis, both transverse components of the time-dependent
vorticity vanish. -/
theorem spacetimeAxisymmetricVorticity_transverse_eq_zero_of_mem_symmetryAxis
    {U Ψ : SpaceTime 2 → ℝ} (hU : ContDiff ℝ 1 U)
    (hΨ : ContDiff ℝ 2 Ψ) (t : ℝ) {x : ℝ^3}
    (hx : x ∈ symmetryAxis) :
    spacetimeAxisymmetricVorticity U Ψ (timeSpaceCons t x) 0 = 0 ∧
      spacetimeAxisymmetricVorticity U Ψ (timeSpaceCons t x) 1 = 0 := by
  rw [spacetimeAxisymmetricVorticity_timeSpaceCons]
  exact
    spatialCurl_axisymmetricVelocity_transverse_eq_zero_of_mem_symmetryAxis
      (contDiff_profileSlice hU t) (contDiff_profileSlice hΨ t) hx

/-- On the symmetry axis, the axial vorticity is the regular value
`2 U(t,0,z)`. -/
theorem spacetimeAxisymmetricVorticity_apply_two_of_mem_symmetryAxis
    {U Ψ : SpaceTime 2 → ℝ} (hU : ContDiff ℝ 1 U)
    (hΨ : ContDiff ℝ 2 Ψ) (t : ℝ) {x : ℝ^3}
    (hx : x ∈ symmetryAxis) :
    spacetimeAxisymmetricVorticity U Ψ (timeSpaceCons t x) 2 =
      2 * squaredCylindricalLift (profileSlice U t) x := by
  rw [spacetimeAxisymmetricVorticity_timeSpaceCons]
  exact spatialCurl_axisymmetricVelocity_apply_two_of_mem_symmetryAxis
    (contDiff_profileSlice hU t) (contDiff_profileSlice hΨ t) hx

end

end AxisymmetricFlow
