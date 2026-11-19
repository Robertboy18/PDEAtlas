/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Axisymmetric.TimeProfile
public import Mathlib.RingTheory.Derivation.Basic
public import PDE.FDeriv.Calculus

/-!
# Classical spatial calculus for time-dependent profiles

Differentiated axisymmetric evolution equations need product and commutation rules for
spatial derivatives. Those rules are false when asserted for every function:
Mathlib's total `fderiv` is zero at a nondifferentiability point, so an
unrestricted Leibniz rule is inconsistent with the derivative of a coordinate.

We therefore work on spatially smooth profiles. A `SmoothTimeProfile` is a
time-dependent profile whose spatial slice is smooth for every fixed time; these
form a subalgebra of `TimeProfile`, and on it the classical radial and axial partial
derivatives are Mathlib `Derivation`s. The Leibniz rule, linearity, vanishing
on constants and on time-only scalars, and the commutation `∂_r ∂_z = ∂_z ∂_r` are
then available as algebra, and the `_apply` lemmas transfer each identity back to the
fields of `classicalAxisymmetricTimeDifferential` used by the PDE definitions.

## Main results

* `smoothTimeProfileSubalgebra`, `SmoothTimeProfile`: the subalgebra of spatially
  smooth profiles, with `ofTimeScalar`, `radialCoordinate`, `axialCoordinate` as
  elements.
* `smoothTimeProfileDerivation`, `smoothTimeProfileDr`, `smoothTimeProfileDz`:
  coordinate differentiation as derivations.
* `smoothTimeProfileDr_radialCoordinate`, `smoothTimeProfileDz_axialCoordinate` and the
  companion simp lemmas: derivatives of the coordinate functions and of constants.
* `smoothTimeProfileDr_Dz_comm`: mixed partial derivatives commute on smooth profiles
  (Schwarz's theorem, via `partialDeriv_partialDeriv_comm_of_contDiff`).

## Implementation notes

No time regularity is imposed: `SmoothTimeProfile` is smooth in `(r, z)` for each fixed
`t`, and the derivations only differentiate in space. Joint space-time smoothness is
the subject of `PDE.FDeriv.Axisymmetric.JointTimeProfile`.
-/

@[expose] public section

noncomputable section

open PDE.CoordinateSystems (meridianR meridianZ)

namespace PDE.FDeriv

/-- Time profiles that are smooth in the spatial variables at every fixed
time. No time regularity is imposed by this subalgebra. -/
def smoothTimeProfileSubalgebra : Subalgebra ℝ TimeProfile where
  carrier := {f | ∀ t, ContDiff ℝ (⊤ : ℕ∞) (fun x : (ℝ^2) ↦ f x t)}
  zero_mem' := by
    intro t
    exact contDiff_const
  one_mem' := by
    intro t
    exact contDiff_const
  add_mem' := by
    intro f g hf hg t
    exact (hf t).add (hg t)
  mul_mem' := by
    intro f g hf hg t
    exact (hf t).mul (hg t)
  algebraMap_mem' := by
    intro c t
    simpa [Pi.algebraMap_apply] using
      (contDiff_const :
        ContDiff ℝ (⊤ : ℕ∞) (fun _ : (ℝ^2) ↦ c))

/-- The type of time profiles that are smooth in the spatial variables. -/
abbrev SmoothTimeProfile := smoothTimeProfileSubalgebra

namespace SmoothTimeProfile

/-- Spatial smoothness of a fixed-time slice. -/
theorem contDiff (f : SmoothTimeProfile) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : (ℝ^2) ↦ (f : TimeProfile) x t) :=
  f.property t

/-- Spatial differentiability of a fixed-time slice. -/
theorem differentiable (f : SmoothTimeProfile) (t : ℝ) :
    Differentiable ℝ (fun x : (ℝ^2) ↦ (f : TimeProfile) x t) :=
  (contDiff f t).differentiable (by simp)

/-- A time-only scalar, regarded as a spatially constant smooth profile. -/
def ofTimeScalar (a : ℝ → ℝ) : SmoothTimeProfile :=
  ⟨fun _ t ↦ a t, fun _ ↦ contDiff_const⟩

/-- The radial coordinate as a smooth time profile. -/
def radialCoordinate : SmoothTimeProfile :=
  ⟨fun x _ ↦ meridianR x, by
    intro t
    simpa [meridianR, EuclideanSpace.proj] using
      (EuclideanSpace.proj (0 : Fin 2) : (ℝ^2) →L[ℝ] ℝ).contDiff⟩

/-- The axial coordinate as a smooth time profile. -/
def axialCoordinate : SmoothTimeProfile :=
  ⟨fun x _ ↦ meridianZ x, by
    intro t
    simpa [meridianZ, EuclideanSpace.proj] using
      (EuclideanSpace.proj (1 : Fin 2) : (ℝ^2) →L[ℝ] ℝ).contDiff⟩

/-- A time-only scalar evaluates to `a t` at every spatial point. -/
@[simp]
theorem ofTimeScalar_apply (a : ℝ → ℝ) (x : (ℝ^2)) (t : ℝ) :
    (ofTimeScalar a : TimeProfile) x t = a t :=
  rfl

/-- The radial coordinate profile evaluates to `meridianR x`. -/
@[simp]
theorem radialCoordinate_apply (x : (ℝ^2)) (t : ℝ) :
    (radialCoordinate : TimeProfile) x t = meridianR x :=
  rfl

/-- The axial coordinate profile evaluates to `meridianZ x`. -/
@[simp]
theorem axialCoordinate_apply (x : (ℝ^2)) (t : ℝ) :
    (axialCoordinate : TimeProfile) x t = meridianZ x :=
  rfl

/-- A natural number, viewed as a constant smooth profile, evaluates to itself. -/
@[simp]
theorem natCast_apply (n : ℕ) (x : (ℝ^2)) (t : ℝ) :
    ((n : SmoothTimeProfile) : TimeProfile) x t = n :=
  rfl

/-- The constant profile `2` evaluates to `2`. -/
@[simp]
theorem two_apply (x : (ℝ^2)) (t : ℝ) :
    ((2 : SmoothTimeProfile) : TimeProfile) x t = 2 :=
  rfl

/-- The constant profile `3` evaluates to `3`. -/
@[simp]
theorem three_apply (x : (ℝ^2)) (t : ℝ) :
    ((3 : SmoothTimeProfile) : TimeProfile) x t = 3 :=
  rfl

end SmoothTimeProfile

/-- Coordinate differentiation preserves spatial smoothness. -/
def smoothTimeProfilePartial (i : Fin 2) (f : SmoothTimeProfile) :
    SmoothTimeProfile :=
  ⟨fun x t ↦
      (∂[i] (fun y : (ℝ^2) ↦ (f : TimeProfile) y t)) x,
    by
      intro t
      simpa only using
        contDiff_top_partialDeriv (i := i)
          (SmoothTimeProfile.contDiff f t)⟩

/-- Coordinate differentiation as a derivation of the smooth-profile
subalgebra. -/
def smoothTimeProfileDerivation (i : Fin 2) :
    Derivation ℝ SmoothTimeProfile SmoothTimeProfile where
  toLinearMap :=
    { toFun := smoothTimeProfilePartial i
      map_add' := by
        intro f g
        apply Subtype.ext
        funext x t
        change
          (∂[i] (fun y : (ℝ^2) ↦
                (f : TimeProfile) y t + (g : TimeProfile) y t)) x =
            (∂[i] (fun y : (ℝ^2) ↦ (f : TimeProfile) y t)) x +
              (∂[i] (fun y : (ℝ^2) ↦ (g : TimeProfile) y t)) x
        simpa only using
          partialDeriv_add
            (SmoothTimeProfile.differentiable f t).differentiableAt
            (SmoothTimeProfile.differentiable g t).differentiableAt
      map_smul' := by
        intro c f
        apply Subtype.ext
        funext x t
        change
          (∂[i] (fun y : (ℝ^2) ↦ c * (f : TimeProfile) y t)) x =
            c * (∂[i] (fun y : (ℝ^2) ↦ (f : TimeProfile) y t)) x
        simpa only [RingHom.id_apply, smul_eq_mul] using
          partialDeriv_const_smul (n := 2) (i := i) c
            (f := fun y : (ℝ^2) ↦ (f : TimeProfile) y t) (x := x) }
  map_one_eq_zero' := by
    apply Subtype.ext
    funext x t
    change
      (∂[i] (fun _ : (ℝ^2) ↦ (1 : ℝ))) x = 0
    exact partialDeriv_const 1
  leibniz' := by
    intro f g
    apply Subtype.ext
    funext x t
    change
      (∂[i] (fun y : (ℝ^2) ↦
            (f : TimeProfile) y t * (g : TimeProfile) y t)) x =
        (f : TimeProfile) x t *
            (∂[i] (fun y : (ℝ^2) ↦ (g : TimeProfile) y t)) x +
          (g : TimeProfile) x t *
            (∂[i] (fun y : (ℝ^2) ↦ (f : TimeProfile) y t)) x
    rw [partialDeriv_mul (i := i)
      (SmoothTimeProfile.differentiable f t).differentiableAt
      (SmoothTimeProfile.differentiable g t).differentiableAt]
    ring

/-- Classical radial differentiation on smooth time profiles. -/
abbrev smoothTimeProfileDr :
    Derivation ℝ SmoothTimeProfile SmoothTimeProfile :=
  smoothTimeProfileDerivation 0

/-- Classical axial differentiation on smooth time profiles. -/
abbrev smoothTimeProfileDz :
    Derivation ℝ SmoothTimeProfile SmoothTimeProfile :=
  smoothTimeProfileDerivation 1

/-- The coordinate derivative of a smooth profile is `partialDeriv` of its time
slice, which on this subalgebra is the classical derivative. -/
@[simp]
theorem smoothTimeProfilePartial_apply
    (i : Fin 2) (f : SmoothTimeProfile) (x : (ℝ^2)) (t : ℝ) :
    (smoothTimeProfilePartial i f : TimeProfile) x t =
      (∂[i] (fun y : (ℝ^2) ↦ (f : TimeProfile) y t)) x :=
  rfl

/-- The radial derivation agrees pointwise with the `dr` field of
`classicalAxisymmetricTimeDifferential`. -/
@[simp]
theorem smoothTimeProfileDr_apply
    (f : SmoothTimeProfile) (x : (ℝ^2)) (t : ℝ) :
    (smoothTimeProfileDr f : TimeProfile) x t =
      classicalAxisymmetricTimeDifferential.dr (f : TimeProfile) x t :=
  rfl

/-- The axial derivation agrees pointwise with the `dz` field of
`classicalAxisymmetricTimeDifferential`. -/
@[simp]
theorem smoothTimeProfileDz_apply
    (f : SmoothTimeProfile) (x : (ℝ^2)) (t : ℝ) :
    (smoothTimeProfileDz f : TimeProfile) x t =
      classicalAxisymmetricTimeDifferential.dz (f : TimeProfile) x t :=
  rfl

/-- Spatial derivatives of a time-only scalar vanish. -/
@[simp]
theorem smoothTimeProfilePartial_timeScalar
    (i : Fin 2) (a : ℝ → ℝ) :
    smoothTimeProfilePartial i (SmoothTimeProfile.ofTimeScalar a) = 0 := by
  apply Subtype.ext
  funext x t
  change
    (∂[i] (fun _ : (ℝ^2) ↦ a t)) x = 0
  exact partialDeriv_const (a t)

/-- Spatial derivatives of a natural-number constant vanish. -/
@[simp]
theorem smoothTimeProfilePartial_natCast (i : Fin 2) (n : ℕ) :
    smoothTimeProfilePartial i (n : SmoothTimeProfile) = 0 :=
  (smoothTimeProfileDerivation i).map_natCast n

/-- The radial derivative of a time-only scalar vanishes. -/
@[simp]
theorem smoothTimeProfileDr_timeScalar (a : ℝ → ℝ) :
    smoothTimeProfileDr (SmoothTimeProfile.ofTimeScalar a) = 0 :=
  smoothTimeProfilePartial_timeScalar 0 a

/-- The axial derivative of a time-only scalar vanishes. -/
@[simp]
theorem smoothTimeProfileDz_timeScalar (a : ℝ → ℝ) :
    smoothTimeProfileDz (SmoothTimeProfile.ofTimeScalar a) = 0 :=
  smoothTimeProfilePartial_timeScalar 1 a

/-- `∂_r 2 = 0`. -/
@[simp]
theorem smoothTimeProfileDr_two :
    smoothTimeProfileDr (2 : SmoothTimeProfile) = 0 :=
  smoothTimeProfileDr.map_natCast 2

/-- `∂_z 2 = 0`. -/
@[simp]
theorem smoothTimeProfileDz_two :
    smoothTimeProfileDz (2 : SmoothTimeProfile) = 0 :=
  smoothTimeProfileDz.map_natCast 2

/-- `∂_r r = 1`. -/
@[simp]
theorem smoothTimeProfileDr_radialCoordinate :
    smoothTimeProfileDr SmoothTimeProfile.radialCoordinate = 1 := by
  apply Subtype.ext
  funext x t
  change
    (∂[0] (fun y : (ℝ^2) ↦ meridianR y)) x = 1
  simp [meridianR]

/-- `∂_r z = 0`. -/
@[simp]
theorem smoothTimeProfileDr_axialCoordinate :
    smoothTimeProfileDr SmoothTimeProfile.axialCoordinate = 0 := by
  apply Subtype.ext
  funext x t
  change
    (∂[0] (fun y : (ℝ^2) ↦ meridianZ y)) x = 0
  simp [meridianZ]

/-- `∂_z r = 0`. -/
@[simp]
theorem smoothTimeProfileDz_radialCoordinate :
    smoothTimeProfileDz SmoothTimeProfile.radialCoordinate = 0 := by
  apply Subtype.ext
  funext x t
  change
    (∂[1] (fun y : (ℝ^2) ↦ meridianR y)) x = 0
  simp [meridianR]

/-- `∂_z z = 1`. -/
@[simp]
theorem smoothTimeProfileDz_axialCoordinate :
    smoothTimeProfileDz SmoothTimeProfile.axialCoordinate = 1 := by
  apply Subtype.ext
  funext x t
  change
    (∂[1] (fun y : (ℝ^2) ↦ meridianZ y)) x = 1
  simp [meridianZ]

/-- Radial and axial derivatives commute on smooth time profiles. -/
theorem smoothTimeProfileDr_Dz_comm (f : SmoothTimeProfile) :
    smoothTimeProfileDr (smoothTimeProfileDz f) =
      smoothTimeProfileDz (smoothTimeProfileDr f) := by
  apply Subtype.ext
  funext x t
  change
    (∂[0] (fun y : (ℝ^2) ↦
          (∂[1] (fun w : (ℝ^2) ↦ (f : TimeProfile) w t)) y)) x =
      (∂[1] (fun y : (ℝ^2) ↦
          (∂[0] (fun w : (ℝ^2) ↦ (f : TimeProfile) w t)) y)) x
  have hC2 : ContDiff ℝ 2 (fun w : (ℝ^2) ↦ (f : TimeProfile) w t) :=
    (SmoothTimeProfile.contDiff f t).of_le (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  simpa only using
    congrFun
      (partialDeriv_partialDeriv_comm_of_contDiff
        (n := 2) (0 : Fin 2) (1 : Fin 2) hC2) x

end PDE.FDeriv
