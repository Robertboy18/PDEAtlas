/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Axisymmetric.Profile

/-!
# Classical derivatives of time-dependent meridian profiles

A time-dependent meridian profile has two spatial variables and one time
variable. Spatial derivatives act on fixed-time slices; the time derivative
acts at a fixed spatial point. We define these operators and the
regularized radial quotient used in the axisymmetric elliptic equation.

These are total expressions. Product and commutation rules require a regular
domain of profiles, provided separately by `ClassicalTimeProfile` and
`JointTimeProfile`.
-/

@[expose] public section

noncomputable section

open PDE.CoordinateSystems (meridianR meridianZ)

namespace PDE.FDeriv

/-- A scalar profile depending only on `(r,z,t)` after axisymmetry removes `theta`. -/
abbrev TimeProfile := (ℝ^2) → ℝ → ℝ

/-- Axisymmetric time-dependent differential operators in `(r,z,t)`. -/
structure AxisymmetricTimeDifferential where
  /-- Time-derivative operator. -/
  dt : TimeProfile → TimeProfile
  /-- Radial first-derivative operator. -/
  dr : TimeProfile → TimeProfile
  /-- Axial first-derivative operator. -/
  dz : TimeProfile → TimeProfile
  /-- Radial second-derivative operator. -/
  drr : TimeProfile → TimeProfile
  /-- Axial second-derivative operator. -/
  dzz : TimeProfile → TimeProfile
  /-- Operator representing `(∂r f)/r`, with its axis value supplied by the realization. -/
  drOverR : TimeProfile → TimeProfile

/-- The classical derivative operators on the `(r,z,t)` profile
half-plane. At the axis, the quotient slot `(∂r f)/r` is assigned `∂rr f`.
This is the removable limit when the profile is sufficiently regular and its
first radial derivative vanishes there. Smooth physical reconstruction still
requires the stronger evenness encoded later by squared-radius factorization.
-/
def classicalAxisymmetricTimeDifferential : AxisymmetricTimeDifferential where
  dt := fun f x t ↦ deriv (fun s ↦ f x s) t
  dr := fun f x t ↦
    (∂[0] (fun y : (ℝ^2) ↦ f y t)) x
  dz := fun f x t ↦
    (∂[1] (fun y : (ℝ^2) ↦ f y t)) x
  drr := fun f x t ↦
    (∂[0] (fun y : (ℝ^2) ↦ (∂[0] (fun w : (ℝ^2) ↦ f w t)) y)) x
  dzz := fun f x t ↦
    (∂[1] (fun y : (ℝ^2) ↦ (∂[1] (fun w : (ℝ^2) ↦ f w t)) y)) x
  drOverR := fun f x t ↦
    if meridianR x = 0 then
      (∂[0] (fun y : (ℝ^2) ↦ (∂[0] (fun w : (ℝ^2) ↦ f w t)) y)) x
    else
      (meridianR x)⁻¹ *
        (∂[0] (fun y : (ℝ^2) ↦ f y t)) x

/-- An operator family has classical semantics when every field agrees with
`classicalAxisymmetricTimeDifferential`, including the value chosen on the axis.
-/
def HasClassicalAxisymmetricTimeSemantics
    (D : AxisymmetricTimeDifferential) : Prop :=
  D = classicalAxisymmetricTimeDifferential

/-- `classicalAxisymmetricTimeDifferential` has classical semantics, by definition. -/
theorem classicalAxisymmetricTimeDifferential_hasSemantics :
    HasClassicalAxisymmetricTimeSemantics classicalAxisymmetricTimeDifferential :=
  rfl

/-- Off the axis, the classical quotient field is `r⁻¹ ∂r`. -/
theorem classical_drOverR_of_ne_zero
    (f : TimeProfile) (x : (ℝ^2)) (t : ℝ) (hx : meridianR x ≠ 0) :
    classicalAxisymmetricTimeDifferential.drOverR f x t =
      (meridianR x)⁻¹ * classicalAxisymmetricTimeDifferential.dr f x t := by
  simp [classicalAxisymmetricTimeDifferential, hx]

/-- On the axis, the classical quotient field selects the `∂rr` value.

Identifying this selected value with the limit of `(∂r f)/r` requires
regularity and a vanishing first radial trace.
-/
theorem classical_drOverR_of_eq_zero
    (f : TimeProfile) (x : (ℝ^2)) (t : ℝ) (hx : meridianR x = 0) :
    classicalAxisymmetricTimeDifferential.drOverR f x t =
      classicalAxisymmetricTimeDifferential.drr f x t := by
  simp [classicalAxisymmetricTimeDifferential, hx]

/--
Axisymmetric time-dependent differential operators, each an `ℝ`-linear map.

`AxisymmetricTimeDifferential` is more convenient for writing the PDE formulas
pointwise. We use this linear version when the stream/Poisson equation enters
coefficient-space algebra or perturbation decompositions, so additivity comes
with the type instead of as separate hypotheses.
-/
structure LinearAxisymmetricTimeDifferential where
  /-- Linear time-derivative operator. -/
  dt : TimeProfile →ₗ[ℝ] TimeProfile
  /-- Linear radial first-derivative operator. -/
  dr : TimeProfile →ₗ[ℝ] TimeProfile
  /-- Linear axial first-derivative operator. -/
  dz : TimeProfile →ₗ[ℝ] TimeProfile
  /-- Linear radial second-derivative operator. -/
  drr : TimeProfile →ₗ[ℝ] TimeProfile
  /-- Linear axial second-derivative operator. -/
  dzz : TimeProfile →ₗ[ℝ] TimeProfile
  /-- Linear realization of `(∂r f)/r`, including its chosen value at the axis. -/
  drOverR : TimeProfile →ₗ[ℝ] TimeProfile

/-- The underlying pointwise operators of a linear time-dependent family. -/
def LinearAxisymmetricTimeDifferential.toAxisymmetricTimeDifferential
    (D : LinearAxisymmetricTimeDifferential) : AxisymmetricTimeDifferential where
  dt := fun f ↦ D.dt f
  dr := fun f ↦ D.dr f
  dz := fun f ↦ D.dz f
  drr := fun f ↦ D.drr f
  dzz := fun f ↦ D.dzz f
  drOverR := fun f ↦ D.drOverR f

/-- Unsigned axisymmetric operator `∂rr + (3/r)∂r + ∂zz` on time profiles.

The separate `drOverR` field matters on the symmetry axis: writing
`(meridianR x)⁻¹ * Dr f` directly would evaluate to zero at `r = 0` in Lean and would not
represent the removable axis limit.
-/
def axisymmetricTimeLaplacian (D : AxisymmetricTimeDifferential)
    (f : TimeProfile) : TimeProfile :=
  fun x t ↦ D.drr f x t + 3 * D.drOverR f x t + D.dzz f x t

/-- Signed elliptic operator `-(∂rr + (3/r)∂r + ∂zz)`. -/
def signedAxisymmetricTimeElliptic (D : AxisymmetricTimeDifferential)
    (f : TimeProfile) : TimeProfile :=
  fun x t ↦ -axisymmetricTimeLaplacian D f x t

/-- The time-dependent unsigned axisymmetric elliptic operator as a linear map. -/
def axisymmetricTimeLaplacianLinearMap
    (D : LinearAxisymmetricTimeDifferential) : TimeProfile →ₗ[ℝ] TimeProfile where
  toFun := fun f ↦ fun x t ↦ D.drr f x t + 3 * D.drOverR f x t + D.dzz f x t
  map_add' := by
    intro f g
    ext x t
    simp [map_add]
    ring
  map_smul' := by
    intro c f
    ext x t
    simp [map_smul]
    ring

/-- The signed time-dependent stream elliptic operator as a linear map. -/
def signedAxisymmetricTimeEllipticLinearMap
    (D : LinearAxisymmetricTimeDifferential) : TimeProfile →ₗ[ℝ] TimeProfile :=
  -axisymmetricTimeLaplacianLinearMap D

/-- The linear-map time elliptic operator agrees with the pointwise PDE definition. -/
theorem signedAxisymmetricTimeEllipticLinearMap_apply
    (D : LinearAxisymmetricTimeDifferential) (f : TimeProfile) :
    signedAxisymmetricTimeEllipticLinearMap D f =
      signedAxisymmetricTimeElliptic D.toAxisymmetricTimeDifferential f := by
  ext x t
  simp [signedAxisymmetricTimeEllipticLinearMap, axisymmetricTimeLaplacianLinearMap,
    signedAxisymmetricTimeElliptic, axisymmetricTimeLaplacian,
    LinearAxisymmetricTimeDifferential.toAxisymmetricTimeDifferential]

end PDE.FDeriv
