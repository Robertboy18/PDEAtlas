/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Euler.Axisymmetric.Cylinder
public import PDE.Common.Euclidean.CoordinateReflection
import PDE.Analysis.Calculus.Periodic
import PDE.FDeriv.Calculus
import PDE.FDeriv.Reflection.Coordinate
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Axisymmetric Euler flow in the cylinder: the meridian system

An axisymmetric velocity `u = u^r e_r + u^θ e_θ + u^z e_z` in the cylinder is described in the
meridian half-plane by the swirl `u^θ`, the azimuthal vorticity `ω^θ = ∂_z u^r - ∂_r u^z` and the
angular stream function `φ̃` (the angular component of the vector potential, so that the Stokes
stream function is `r φ̃`). Meridian points are `(r, z)` with `r` in coordinate `0`. The system
of Chen and Hou, Part I (6.2)-(6.4), is

```text
∂_t (r u^θ) + u^r ∂_r (r u^θ) + u^z ∂_z (r u^θ) = 0,
∂_t (ω^θ/r) + u^r ∂_r (ω^θ/r) + u^z ∂_z (ω^θ/r) = r⁻⁴ ∂_z ((r u^θ)²),
-(∂_rr + r⁻¹ ∂_r + ∂_zz) φ̃ + r⁻² φ̃ = ω^θ,   u^r = -∂_z φ̃,   u^z = ∂_r φ̃ + r⁻¹ φ̃,
φ̃(1, z) = 0,
```

imposed on the open meridian strip `0 < r < 1`. The first equation is the azimuthal momentum
equation `D_t u^θ + u^r u^θ / r = 0`, the second is the curl of the meridional momentum
equations, and the third is the definition of `ω^θ` through `φ̃`. For stream functions that are
`C¹` up to the wall (`HasWallRegularityOn`) the boundary condition `φ̃(1, z) = 0` is a trace and
gives `u^r = 0` on the wall (`radialVelocity_eq_zero_of_wall`). Impermeability alone only makes
`φ̃(1, ·)` constant; for an axis-regular stream function the value `0` selects zero axial flux,
since `∫₀¹ u^z r dr = [r φ̃]₀¹ = φ̃(1, z)` (a uniform axial flow has `φ̃ = a r / 2`). Periodicity
in `z` is a separate predicate.

The reflection class of Chen and Hou has `u^θ` even and `ω^θ`, `φ̃` odd in `z`. Then `u^r` is
even and `u^z` odd, and the reflected fields of a solution are again a solution
(`SatisfiesMeridianSystemOn.reflect`); this is the sense in which the class is preserved by the
equations. For an odd `L`-periodic stream function, `φ̃(r, L/2 + kL) = 0` (Part I (6.5) for
`L = 2`).

## Main definitions

* `MeridianFields`: swirl, azimuthal vorticity and angular stream function.
* `radialVelocity`, `axialVelocity`, `meridianVelocity`, `circulation`, `reducedVorticity`,
  `streamOperator`: the derived quantities `u^r`, `u^z`, `(u^r, u^z)`, `r u^θ`, `ω^θ / r` and the
  operator of (6.3).
* `SatisfiesMeridianSystemOn`: the equations (6.2)-(6.4) on the open meridian strip.
* `IsAxiallyPeriodic`, `HasReflectionSymmetry`, `reflect`: periodicity, the reflection class and
  the reflected fields.

## Main results

* `streamFunction_eq_zero_of_odd_of_periodic`: Part I (6.5).
* `HasReflectionSymmetry.radialVelocity_reflect`, `HasReflectionSymmetry.axialVelocity_reflect`:
  parity of the meridian velocity.
* `SatisfiesMeridianSystemOn.reflect`: reflection invariance of the system.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 6, (6.2)-(6.5).
  <https://arxiv.org/abs/2210.07191v4>
* A. J. Majda and A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge Texts in Applied
  Mathematics 27, Cambridge University Press, 2001, Chapter 2, for the cylindrical form of
  axisymmetric Euler flow.
  <https://doi.org/10.1017/CBO9780511613203>
-/

@[expose] public section

open PDE (laplacian advectiveDerivative coordinateLine)

namespace Euler.Cylinder

open EuclideanSpace
open PDE.Common

set_option linter.missingDocs true

noncomputable section

/-- Swirl, azimuthal vorticity and angular stream function of an axisymmetric flow, as
functions of the meridian point `(r, z)` and time. -/
structure MeridianFields where
  /-- Swirl `u^θ`. -/
  swirl : ℝ^2 → ℝ → ℝ
  /-- Azimuthal vorticity `ω^θ = ∂_z u^r - ∂_r u^z`. -/
  vorticity : ℝ^2 → ℝ → ℝ
  /-- Angular stream function `φ̃`, with Stokes stream function `r φ̃`. -/
  streamFunction : ℝ^2 → ℝ → ℝ

/-- The meridian point `(r, z)`. -/
def meridianPoint (r z : ℝ) : ℝ^2 :=
  WithLp.toLp 2 ![r, z]

/-- The radial coordinate of `meridianPoint r z` is `r`. -/
@[simp]
theorem meridianPoint_apply_zero (r z : ℝ) : meridianPoint r z 0 = r := by
  simp [meridianPoint]

/-- The axial coordinate of `meridianPoint r z` is `z`. -/
@[simp]
theorem meridianPoint_apply_one (r z : ℝ) : meridianPoint r z 1 = z := by
  simp [meridianPoint]

/-- The open meridian strip `{(r, z) | 0 < r < 1}`, the meridian section of the open cylinder
with the axis removed. -/
def meridianDomain : Set (ℝ^2) :=
  {x | 0 < x 0 ∧ x 0 < 1}

/-- Radial velocity `u^r = -∂_z φ̃`. -/
def radialVelocity (f : MeridianFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  -(∂[(1 : Fin 2)] (fun y ↦ f.streamFunction y t)) x

/-- Axial velocity `u^z = ∂_r φ̃ + r⁻¹ φ̃`. The formula is meant off the axis: at `r = 0` the
total division gives `∂_r φ̃`, not the axial velocity of an axis-regular flow (which is `2Ψ` for
`φ̃ = r Ψ(r², z)`). -/
def axialVelocity (f : MeridianFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  (∂[(0 : Fin 2)] (fun y ↦ f.streamFunction y t)) x + f.streamFunction x t / x 0

/-- The meridian velocity `(u^r, u^z)`. -/
def meridianVelocity (f : MeridianFields) (x : ℝ^2) (t : ℝ) : ℝ^2 :=
  WithLp.toLp 2 ![radialVelocity f x t, axialVelocity f x t]

/-- The radial component of the meridian velocity. -/
@[simp]
theorem meridianVelocity_apply_zero (f : MeridianFields) (x : ℝ^2) (t : ℝ) :
    meridianVelocity f x t 0 = radialVelocity f x t := by
  simp [meridianVelocity]

/-- The axial component of the meridian velocity. -/
@[simp]
theorem meridianVelocity_apply_one (f : MeridianFields) (x : ℝ^2) (t : ℝ) :
    meridianVelocity f x t 1 = axialVelocity f x t := by
  simp [meridianVelocity]

/-- Circulation `r u^θ`. -/
def circulation (f : MeridianFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  x 0 * f.swirl x t

/-- Reduced vorticity `ω^θ / r`, meant off the axis: at `r = 0` the total division gives `0`. -/
def reducedVorticity (f : MeridianFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  f.vorticity x t / x 0

/-- The operator `-(∂_rr + r⁻¹ ∂_r + ∂_zz) φ + r⁻² φ` of (6.3), the azimuthal component of
`-Δ (φ e_θ)` written in the meridian plane. -/
def streamOperator (φ : ℝ^2 → ℝ) (x : ℝ^2) : ℝ :=
  -laplacian φ x - (∂[(0 : Fin 2)] φ) x / x 0 + φ x / x 0 ^ 2

/-- Transport of the circulation `r u^θ`, the first equation of (6.2). -/
def SatisfiesSwirlEquationOn (f : MeridianFields) (times : Set ℝ) : Prop :=
  ∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ meridianDomain → t ∈ times →
    deriv (fun s ↦ circulation f x s) t +
        advectiveDerivative (fun y ↦ meridianVelocity f y t) (fun y ↦ circulation f y t) x =
      0

/-- The reduced vorticity equation, the second equation of (6.2). -/
def SatisfiesVorticityEquationOn (f : MeridianFields) (times : Set ℝ) : Prop :=
  ∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ meridianDomain → t ∈ times →
    deriv (fun s ↦ reducedVorticity f x s) t +
        advectiveDerivative (fun y ↦ meridianVelocity f y t)
          (fun y ↦ reducedVorticity f y t) x =
      (∂[(1 : Fin 2)] (fun y ↦ circulation f y t ^ 2)) x / x 0 ^ 4

/-- The stream function equation (6.3). -/
def SatisfiesStreamFunctionEquationOn (f : MeridianFields) (times : Set ℝ) : Prop :=
  ∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ meridianDomain → t ∈ times →
    streamOperator (fun y ↦ f.streamFunction y t) x = f.vorticity x t

/-- The wall condition (6.4): the angular stream function vanishes on `r = 1`. -/
def HasZeroWallStreamFunctionOn (f : MeridianFields) (times : Set ℝ) : Prop :=
  ∀ (z : ℝ) ⦃t : ℝ⦄, t ∈ times → f.streamFunction (meridianPoint 1 z) t = 0

/-- The axisymmetric Euler system (6.2)-(6.4) in the cylinder on a set of times. -/
structure SatisfiesMeridianSystemOn (f : MeridianFields) (times : Set ℝ) : Prop where
  /-- Transport of `r u^θ`. -/
  swirl_equation : SatisfiesSwirlEquationOn f times
  /-- The reduced vorticity equation. -/
  vorticity_equation : SatisfiesVorticityEquationOn f times
  /-- The stream function equation. -/
  streamFunction_equation : SatisfiesStreamFunctionEquationOn f times
  /-- The wall condition. -/
  wall : HasZeroWallStreamFunctionOn f times

/-- The meridian translation by `L` in `z`. -/
def axialTranslate (L : ℝ) (x : ℝ^2) : ℝ^2 :=
  x + EuclideanSpace.single (1 : Fin 2) L

/-- The three fields are `L`-periodic in `z` at every time. -/
structure IsAxiallyPeriodic (L : ℝ) (f : MeridianFields) : Prop where
  /-- Periodic swirl. -/
  swirl : ∀ x t, f.swirl (axialTranslate L x) t = f.swirl x t
  /-- Periodic vorticity. -/
  vorticity : ∀ x t, f.vorticity (axialTranslate L x) t = f.vorticity x t
  /-- Periodic stream function. -/
  streamFunction : ∀ x t, f.streamFunction (axialTranslate L x) t = f.streamFunction x t

/-- The reflection `z ↦ -z` of the meridian plane. -/
def axialReflection (x : ℝ^2) : ℝ^2 :=
  coordinateReflection (1 : Fin 2) x

/-- The axial reflection keeps `r`. -/
@[simp]
theorem axialReflection_apply_zero (x : ℝ^2) : axialReflection x 0 = x 0 := by
  simp [axialReflection]

/-- The axial reflection negates `z`. -/
@[simp]
theorem axialReflection_apply_one (x : ℝ^2) : axialReflection x 1 = -x 1 := by
  simp [axialReflection, coordinateReflection_apply_same]

/-- The axial reflection is an involution. -/
@[simp]
theorem axialReflection_axialReflection (x : ℝ^2) :
    axialReflection (axialReflection x) = x :=
  coordinateReflection_involutive (1 : Fin 2) x

/-- The axial reflection preserves the open meridian strip. -/
theorem axialReflection_mem_meridianDomain_iff {x : ℝ^2} :
    axialReflection x ∈ meridianDomain ↔ x ∈ meridianDomain := by
  simp [meridianDomain]

/-- The reflection of `meridianPoint r z` is `meridianPoint r (-z)`. -/
@[simp]
theorem axialReflection_meridianPoint (r z : ℝ) :
    axialReflection (meridianPoint r z) = meridianPoint r (-z) := by
  ext i
  fin_cases i <;> simp

/-- The reflection class of Chen and Hou at every time: `u^θ` even and `ω^θ`, `φ̃` odd
in `z`. -/
structure HasReflectionSymmetry (f : MeridianFields) : Prop where
  /-- Even swirl. -/
  swirl : ∀ t, IsEvenUnderCoordinateReflection (1 : Fin 2) (fun y ↦ f.swirl y t)
  /-- Odd azimuthal vorticity. -/
  vorticity : ∀ t, IsOddUnderCoordinateReflection (1 : Fin 2) (fun y ↦ f.vorticity y t)
  /-- Odd angular stream function. -/
  streamFunction :
    ∀ t, IsOddUnderCoordinateReflection (1 : Fin 2) (fun y ↦ f.streamFunction y t)

/-- The reflected fields `(u^θ ∘ R, -ω^θ ∘ R, -φ̃ ∘ R)` for the axial reflection `R`. They
describe the reflected velocity `R u(R x)`; the azimuthal vorticity, a pseudovector component,
changes sign. -/
def reflect (f : MeridianFields) : MeridianFields where
  swirl := fun y t ↦ f.swirl (axialReflection y) t
  vorticity := fun y t ↦ -f.vorticity (axialReflection y) t
  streamFunction := fun y t ↦ -f.streamFunction (axialReflection y) t

/-- Fields in the reflection class equal their reflection. -/
theorem HasReflectionSymmetry.reflect_eq {f : MeridianFields} (h : HasReflectionSymmetry f) :
    reflect f = f := by
  cases f with
  | mk swirl vorticity streamFunction =>
    simp only [reflect, MeridianFields.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · funext y t
      exact h.swirl t y
    · funext y t
      simpa [axialReflection] using congrArg Neg.neg (h.vorticity t y)
    · funext y t
      simpa [axialReflection] using congrArg Neg.neg (h.streamFunction t y)

/-- The meridian translation of `meridianPoint r z` by `L` is `meridianPoint r (z + L)`. -/
@[simp]
theorem axialTranslate_meridianPoint (L r z : ℝ) :
    axialTranslate L (meridianPoint r z) = meridianPoint r (z + L) := by
  ext i
  fin_cases i <;> simp [axialTranslate]

/-- Part I (6.5): an odd, `L`-periodic angular stream function vanishes on the lines
`z = L/2 + kL`. For `L = 2` these are the lines `z = 2k - 1`. -/
theorem streamFunction_eq_zero_of_odd_of_periodic {f : MeridianFields} {L : ℝ}
    (hsym : HasReflectionSymmetry f) (hper : IsAxiallyPeriodic L f) (r t : ℝ) (k : ℤ) :
    f.streamFunction (meridianPoint r (L / 2 + k * L)) t = 0 := by
  refine PDE.Analysis.eq_zero_of_odd_of_periodic
    (g := fun z ↦ f.streamFunction (meridianPoint r z) t) ?_ ?_ k
  · intro z
    have h := hsym.streamFunction t (meridianPoint r z)
    simpa [← axialReflection_meridianPoint, axialReflection] using h
  · intro z
    simpa using hper.streamFunction (meridianPoint r z) t

/-- Classical regularity of the meridian fields on the open meridian strip: jointly
differentiable swirl and vorticity and `C²` stream function slices. -/
structure HasMeridianRegularityOn (f : MeridianFields) (times : Set ℝ) : Prop where
  /-- Joint differentiability of the swirl. -/
  swirl_differentiableAt : ∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ meridianDomain → t ∈ times →
    DifferentiableAt ℝ (Function.uncurry f.swirl) (x, t)
  /-- Joint differentiability of the vorticity. -/
  vorticity_differentiableAt : ∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ meridianDomain → t ∈ times →
    DifferentiableAt ℝ (Function.uncurry f.vorticity) (x, t)
  /-- `C²` stream function slices. -/
  streamFunction_contDiffAt : ∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ meridianDomain → t ∈ times →
    ContDiffAt ℝ 2 (fun y ↦ f.streamFunction y t) x

/-- A jointly differentiable field has differentiable space slices. -/
theorem differentiableAt_slice {g : ℝ^2 → ℝ → ℝ} {x : ℝ^2} {t : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry g) (x, t)) :
    DifferentiableAt ℝ (fun y ↦ g y t) x := by
  have hs : DifferentiableAt ℝ (fun y : ℝ^2 ↦ (y, t)) x := by fun_prop
  exact h.comp x hs

/-- A jointly differentiable field has differentiable time slices. -/
theorem differentiableAt_timeSlice {g : ℝ^2 → ℝ → ℝ} {x : ℝ^2} {t : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry g) (x, t)) :
    DifferentiableAt ℝ (fun s ↦ g x s) t := by
  have hs : DifferentiableAt ℝ (fun s : ℝ ↦ (x, s)) t := by fun_prop
  exact h.comp t hs

/-- Swirl slices are differentiable on the strip. -/
theorem HasMeridianRegularityOn.swirl_slice {f : MeridianFields} {times : Set ℝ}
    (h : HasMeridianRegularityOn f times) {x : ℝ^2} {t : ℝ} (hx : x ∈ meridianDomain)
    (ht : t ∈ times) : DifferentiableAt ℝ (fun y ↦ f.swirl y t) x :=
  differentiableAt_slice (h.swirl_differentiableAt hx ht)

/-- Vorticity slices are differentiable on the strip. -/
theorem HasMeridianRegularityOn.vorticity_slice {f : MeridianFields} {times : Set ℝ}
    (h : HasMeridianRegularityOn f times) {x : ℝ^2} {t : ℝ} (hx : x ∈ meridianDomain)
    (ht : t ∈ times) : DifferentiableAt ℝ (fun y ↦ f.vorticity y t) x :=
  differentiableAt_slice (h.vorticity_differentiableAt hx ht)

/-- Regularity of the stream function at the wall: its slices are `C¹` at every wall point. With
it the wall condition (6.4) is a boundary trace rather than a prescribed value, and it gives
impermeability (`radialVelocity_eq_zero_of_wall`, `tendsto_radialVelocity_wall`). -/
def HasWallRegularityOn (f : MeridianFields) (times : Set ℝ) : Prop :=
  ∀ (z : ℝ) ⦃t : ℝ⦄, t ∈ times →
    ContDiffAt ℝ 1 (fun y ↦ f.streamFunction y t) (meridianPoint 1 z)

/-- Impermeability: the wall condition (6.4) with `C¹` stream function slices at the wall gives
`u^r = -∂_z φ̃ = 0` on the wall. -/
theorem radialVelocity_eq_zero_of_wall {f : MeridianFields} {times : Set ℝ}
    (hwall : HasZeroWallStreamFunctionOn f times) (hreg : HasWallRegularityOn f times) (z : ℝ)
    {t : ℝ} (ht : t ∈ times) : radialVelocity f (meridianPoint 1 z) t = 0 := by
  have hd := (hreg z ht).differentiableAt (by norm_num)
  rw [radialVelocity, PDE.partialDeriv_eq_deriv_coordinateLine 1 _ hd]
  have hline : (fun y ↦ f.streamFunction y t) ∘ coordinateLine 1 (meridianPoint 1 z) =
      fun _ ↦ 0 := by
    funext σ
    have hpt : coordinateLine 1 (meridianPoint 1 z) σ = meridianPoint 1 σ := by
      ext i
      fin_cases i <;> simp [coordinateLine, meridianPoint]
    simp only [Function.comp_apply, hpt]
    exact hwall σ ht
  rw [hline, deriv_const, neg_zero]

/-- Impermeability as a limit: near the wall the radial velocity tends to zero. -/
theorem tendsto_radialVelocity_wall {f : MeridianFields} {times : Set ℝ}
    (hwall : HasZeroWallStreamFunctionOn f times) (hreg : HasWallRegularityOn f times) (z : ℝ)
    {t : ℝ} (ht : t ∈ times) :
    Filter.Tendsto (fun y ↦ radialVelocity f y t) (nhds (meridianPoint 1 z)) (nhds 0) := by
  have hc : ContinuousAt (fun y ↦ radialVelocity f y t) (meridianPoint 1 z) := by
    have h := (hreg z ht).partialDeriv (1 : Fin 2) (k := 0) (by norm_num)
    exact h.continuousAt.neg
  rw [← radialVelocity_eq_zero_of_wall hwall hreg z ht]
  exact hc

/-- The radial derivative of `g ∘ R`, `R` the axial reflection `z ↦ -z`, is `(∂₀ g) ∘ R` at points
where `g` is differentiable. -/
private theorem partialDeriv_zero_comp_axialReflection {g : ℝ^2 → ℝ} {x : ℝ^2}
    (hg : DifferentiableAt ℝ g (axialReflection x)) :
    (∂[(0 : Fin 2)] (fun y ↦ g (axialReflection y))) x = (∂[(0 : Fin 2)] g) (axialReflection x) :=
  partialDeriv_comp_coordinateReflection_of_ne (1 : Fin 2) 0 (by decide) g x hg

/-- The axial derivative of `g ∘ R`, `R` the axial reflection `z ↦ -z`, is `-(∂₁ g) ∘ R` at points
where `g` is differentiable. -/
private theorem partialDeriv_one_comp_axialReflection {g : ℝ^2 → ℝ} {x : ℝ^2}
    (hg : DifferentiableAt ℝ g (axialReflection x)) :
    (∂[(1 : Fin 2)] (fun y ↦ g (axialReflection y))) x =
      -(∂[(1 : Fin 2)] g) (axialReflection x) :=
  partialDeriv_comp_coordinateReflection_same (1 : Fin 2) g x hg

/-- The radial velocity of the reflected fields is the reflected radial velocity. -/
theorem radialVelocity_reflect (f : MeridianFields) {x : ℝ^2} {t : ℝ}
    (hφ : DifferentiableAt ℝ (fun y ↦ f.streamFunction y t) (axialReflection x)) :
    radialVelocity (reflect f) x t = radialVelocity f (axialReflection x) t := by
  simp only [radialVelocity, reflect]
  rw [PDE.partialDeriv_fun_neg, partialDeriv_one_comp_axialReflection hφ]
  ring

/-- The axial velocity of the reflected fields is minus the reflected axial velocity. -/
theorem axialVelocity_reflect (f : MeridianFields) {x : ℝ^2} {t : ℝ}
    (hφ : DifferentiableAt ℝ (fun y ↦ f.streamFunction y t) (axialReflection x)) :
    axialVelocity (reflect f) x t = -axialVelocity f (axialReflection x) t := by
  simp only [axialVelocity, reflect]
  rw [PDE.partialDeriv_fun_neg, partialDeriv_zero_comp_axialReflection hφ,
      axialReflection_apply_zero]
  ring

/-- In the reflection class the radial velocity is even in `z`. -/
theorem HasReflectionSymmetry.radialVelocity_reflect {f : MeridianFields}
    (h : HasReflectionSymmetry f) {x : ℝ^2} {t : ℝ}
    (hφ : DifferentiableAt ℝ (fun y ↦ f.streamFunction y t) (axialReflection x)) :
    radialVelocity f (axialReflection x) t = radialVelocity f x t := by
  have := Euler.Cylinder.radialVelocity_reflect f hφ
  rw [h.reflect_eq] at this
  exact this.symm

/-- In the reflection class the axial velocity is odd in `z`. -/
theorem HasReflectionSymmetry.axialVelocity_reflect {f : MeridianFields}
    (h : HasReflectionSymmetry f) {x : ℝ^2} {t : ℝ}
    (hφ : DifferentiableAt ℝ (fun y ↦ f.streamFunction y t) (axialReflection x)) :
    axialVelocity f (axialReflection x) t = -axialVelocity f x t := by
  have := Euler.Cylinder.axialVelocity_reflect f hφ
  rw [h.reflect_eq] at this
  linarith

/-- The circulation of the reflected fields is the reflected circulation. -/
theorem circulation_reflect (f : MeridianFields) (x : ℝ^2) (t : ℝ) :
    circulation (reflect f) x t = circulation f (axialReflection x) t := by
  simp [circulation, reflect]

/-- The reduced vorticity of the reflected fields is minus the reflected reduced vorticity. -/
theorem reducedVorticity_reflect (f : MeridianFields) (x : ℝ^2) (t : ℝ) :
    reducedVorticity (reflect f) x t = -reducedVorticity f (axialReflection x) t := by
  simp [reducedVorticity, reflect, neg_div]

/-- Advection by the reflected meridian velocity of a reflected scalar. -/
private theorem advectiveDerivative_reflect (f : MeridianFields) {g : ℝ^2 → ℝ} {x : ℝ^2}
    {t : ℝ} (hφ : DifferentiableAt ℝ (fun y ↦ f.streamFunction y t) (axialReflection x))
    (hg : DifferentiableAt ℝ g (axialReflection x)) :
    advectiveDerivative (fun y ↦ meridianVelocity (reflect f) y t)
        (fun y ↦ g (axialReflection y)) x =
      advectiveDerivative (fun y ↦ meridianVelocity f y t) g (axialReflection x) := by
  rw [PDE.advectiveDerivative_eq_sum_mul_partialDeriv,
    PDE.advectiveDerivative_eq_sum_mul_partialDeriv, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [meridianVelocity_apply_zero, meridianVelocity_apply_one]
  rw [radialVelocity_reflect f hφ, axialVelocity_reflect f hφ,
    partialDeriv_zero_comp_axialReflection hg, partialDeriv_one_comp_axialReflection hg]
  ring

/-- The circulation `r u^θ` is differentiable where the swirl is. -/
theorem differentiableAt_circulation {f : MeridianFields} {x : ℝ^2} {t : ℝ}
    (h : DifferentiableAt ℝ (fun y ↦ f.swirl y t) x) :
    DifferentiableAt ℝ (fun y ↦ circulation f y t) x := by
  have h0 : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y 0) x :=
    (EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).differentiableAt
  exact h0.mul h

/-- The reduced vorticity `ω^θ / r` is differentiable off the axis where `ω^θ` is. -/
theorem differentiableAt_reducedVorticity {f : MeridianFields} {x : ℝ^2} {t : ℝ}
    (h : DifferentiableAt ℝ (fun y ↦ f.vorticity y t) x) (hx : x 0 ≠ 0) :
    DifferentiableAt ℝ (fun y ↦ reducedVorticity f y t) x := by
  have h0 : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y 0) x :=
    (EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).differentiableAt
  have hfun : (fun y ↦ reducedVorticity f y t) =
      (fun y ↦ f.vorticity y t) * (fun y : ℝ^2 ↦ y 0)⁻¹ := by
    funext y
    simp [reducedVorticity, div_eq_mul_inv]
  rw [hfun]
  exact h.mul (h0.inv hx)

/-- Reflection invariance of the axisymmetric Euler system: if the fields solve (6.2)-(6.4) on a
set of times, so do the reflected fields. -/
theorem SatisfiesMeridianSystemOn.reflect {f : MeridianFields} {times : Set ℝ}
    (h : SatisfiesMeridianSystemOn f times) (hreg : HasMeridianRegularityOn f times) :
    SatisfiesMeridianSystemOn (reflect f) times := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x t hx ht
    have hRx : axialReflection x ∈ meridianDomain := axialReflection_mem_meridianDomain_iff.2 hx
    have hφ := (hreg.streamFunction_contDiffAt hRx ht).differentiableAt (by norm_num)
    have hc := differentiableAt_circulation (hreg.swirl_slice hRx ht)
    have hfun : (fun y ↦ circulation (Euler.Cylinder.reflect f) y t) =
        fun y ↦ circulation f (axialReflection y) t := by
      funext y
      exact circulation_reflect f y t
    have htime : (fun s ↦ circulation (Euler.Cylinder.reflect f) x s) =
        fun s ↦ circulation f (axialReflection x) s := by
      funext s
      exact circulation_reflect f x s
    rw [hfun, htime, advectiveDerivative_reflect f hφ hc]
    exact h.swirl_equation hRx ht
  · intro x t hx ht
    have hRx : axialReflection x ∈ meridianDomain := axialReflection_mem_meridianDomain_iff.2 hx
    have hx0 : (axialReflection x) 0 ≠ 0 := ne_of_gt hRx.1
    have hφ := (hreg.streamFunction_contDiffAt hRx ht).differentiableAt (by norm_num)
    have hω := differentiableAt_reducedVorticity (hreg.vorticity_slice hRx ht) hx0
    have hc := differentiableAt_circulation (hreg.swirl_slice hRx ht)
    have hfun : (fun y ↦ reducedVorticity (Euler.Cylinder.reflect f) y t) =
        fun y ↦ -reducedVorticity f (axialReflection y) t := by
      funext y
      exact reducedVorticity_reflect f y t
    have htime : (fun s ↦ reducedVorticity (Euler.Cylinder.reflect f) x s) =
        fun s ↦ -reducedVorticity f (axialReflection x) s := by
      funext s
      exact reducedVorticity_reflect f x s
    have hsq : (fun y ↦ circulation (Euler.Cylinder.reflect f) y t ^ 2) =
        fun y ↦ (fun z ↦ circulation f z t ^ 2) (axialReflection y) := by
      funext y
      rw [circulation_reflect]
    have hneg : (fun y ↦ -reducedVorticity f (axialReflection y) t) =
        -(fun y ↦ reducedVorticity f (axialReflection y) t) := rfl
    have hadv : advectiveDerivative (fun y ↦ meridianVelocity (Euler.Cylinder.reflect f) y t)
        (fun y ↦ -reducedVorticity f (axialReflection y) t) x =
        -advectiveDerivative (fun y ↦ meridianVelocity f y t)
          (fun y ↦ reducedVorticity f y t) (axialReflection x) := by
      rw [hneg, show advectiveDerivative (fun y ↦ meridianVelocity (Euler.Cylinder.reflect f) y t)
          (-(fun y ↦ reducedVorticity f (axialReflection y) t)) x =
          -advectiveDerivative (fun y ↦ meridianVelocity (Euler.Cylinder.reflect f) y t)
          (fun y ↦ reducedVorticity f (axialReflection y) t) x by
        simp [advectiveDerivative, fderiv_neg]]
      rw [advectiveDerivative_reflect f hφ hω]
    rw [hfun, htime, hsq, hadv, show (fun s ↦ -reducedVorticity f (axialReflection x) s) =
      -(fun s ↦ reducedVorticity f (axialReflection x) s) from rfl, deriv.neg,
      partialDeriv_one_comp_axialReflection (g := fun z ↦ circulation f z t ^ 2) (hc.pow 2)]
    have := h.vorticity_equation hRx ht
    rw [axialReflection_apply_zero] at this
    rw [neg_div, ← this]
    ring
  · intro x t hx ht
    have hRx : axialReflection x ∈ meridianDomain := axialReflection_mem_meridianDomain_iff.2 hx
    have hφ2 := hreg.streamFunction_contDiffAt hRx ht
    have hφ := hφ2.differentiableAt (by norm_num)
    have hneg : (fun y ↦ (Euler.Cylinder.reflect f).streamFunction y t) =
        -(fun y ↦ f.streamFunction (axialReflection y) t) := rfl
    simp only [streamOperator]
    rw [hneg, PDE.laplacian_neg, PDE.partialDeriv_neg]
    rw [show laplacian (fun y ↦ f.streamFunction (axialReflection y) t) x =
        laplacian (fun y ↦ f.streamFunction y t) (axialReflection x) from
      laplacian_comp_coordinateReflection_at (1 : Fin 2) (fun y ↦ f.streamFunction y t) x hφ2,
      partialDeriv_zero_comp_axialReflection hφ]
    have := h.streamFunction_equation hRx ht
    simp only [streamOperator, axialReflection_apply_zero] at this
    simp only [Euler.Cylinder.reflect]
    rw [← this]
    ring
  · intro z t ht
    simp [Euler.Cylinder.reflect, h.wall (-z) ht]

/-- The axial reflection as a continuous linear map. -/
private theorem axialReflection_eq_clm (x : ℝ^2) :
    axialReflection x =
      ((coordinateReflectionLinearIsometryEquiv
        (1 : Fin 2)).toContinuousLinearEquiv.toContinuousLinearMap) x :=
  rfl

/-- Regularity is preserved by the reflection. -/
theorem HasMeridianRegularityOn.reflect {f : MeridianFields} {times : Set ℝ}
    (h : HasMeridianRegularityOn f times) :
    HasMeridianRegularityOn (Euler.Cylinder.reflect f) times := by
  set R : ℝ^2 →L[ℝ] ℝ^2 :=
    (coordinateReflectionLinearIsometryEquiv
      (1 : Fin 2)).toContinuousLinearEquiv.toContinuousLinearMap
  have hmap (x : ℝ^2) (t : ℝ) :
      DifferentiableAt ℝ (fun q : ℝ^2 × ℝ ↦ (axialReflection q.1, q.2)) (x, t) := by
    simp only [axialReflection_eq_clm]
    exact ((R.comp (ContinuousLinearMap.fst ℝ (ℝ^2) ℝ)).differentiableAt).prodMk
      differentiableAt_snd
  refine ⟨?_, ?_, ?_⟩
  · intro x t hx ht
    have hRx := axialReflection_mem_meridianDomain_iff.2 hx
    exact (h.swirl_differentiableAt hRx ht).comp (x, t) (hmap x t)
  · intro x t hx ht
    have hRx := axialReflection_mem_meridianDomain_iff.2 hx
    exact ((h.vorticity_differentiableAt hRx ht).comp (x, t) (hmap x t)).neg
  · intro x t hx ht
    have hRx := axialReflection_mem_meridianDomain_iff.2 hx
    have hR : ContDiffAt ℝ 2 axialReflection x := by
      simp only [funext axialReflection_eq_clm]
      exact R.contDiff.contDiffAt
    exact ((h.streamFunction_contDiffAt hRx ht).comp x hR).neg

end

end Euler.Cylinder
