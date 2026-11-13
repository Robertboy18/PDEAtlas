/-
Copyright (c) 2026 LeanPDE Team.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Axisymmetric.StreamFunction
public import PDE.Common.Euclidean.CoordinateReflection
import PDE.FDeriv.Reflection.Coordinate
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# Reduced axisymmetric Euler and Navier–Stokes equations with swirl

An axisymmetric flow with swirl is described by the standard nonsingular variables

```text
u₁ = u_θ / r,    ω₁ = ω_θ / r,    ψ = r² ψ₁.
```

With meridian coordinates ordered as `(r,z)`, the reconstructed velocity is

```text
u_r = -r ∂_z ψ₁,    u_z = 2ψ₁ + r ∂_r ψ₁,
```

and the reduced viscous equations away from the symmetry axis are

```text
∂_t u₁ + u_r ∂_r u₁ + u_z ∂_z u₁
  = 2u₁ ∂_z ψ₁ + ν (∂_{rr} + 3r⁻¹∂_r + ∂_{zz})u₁,

∂_t ω₁ + u_r ∂_r ω₁ + u_z ∂_z ω₁
  = 2u₁ ∂_z u₁ + ν (∂_{rr} + 3r⁻¹∂_r + ∂_{zz})ω₁,

-(∂_{rr} + 3r⁻¹∂_r + ∂_{zz})ψ₁ = ω₁.
```

The equations and the change of variables are standard, and the inviscid case is obtained by setting
`ν = 0`.

## Main definitions

* `ReducedFields`: the reduced swirl `u₁`, vorticity `ω₁` and streamfunction `ψ₁`, with the
  physical fields `azimuthalVelocity`, `physicalAzimuthalVorticity`, `physicalStreamFunction`
  and the meridian velocity `reducedMeridianVelocity`.
* `reducedSwirlResidual`, `reducedVorticityResidual`, `reducedStreamFunctionResidual` and their
  axis-extended versions `axisExtendedReduced*Residual`.
* `HasClassicalReducedRegularityOn`, `SatisfiesReducedSystemOn`,
  `SatisfiesAxisExtendedResidualSystemOn`, `HasRadiallyEvenReducedFieldsOn`: regularity, the
  off-axis and axis-extended systems on a domain, and radial parity.

## Main results

* `satisfiesAxisExtendedResidualSystemOn_iff_of_radius_ne_zero`: away from the axis the two
  systems agree.
* `streamfunctionVelocityReconstruction_physicalStreamFunction`,
  `physicalStreamFunction_isStreamfunctionForAzimuthalVorticity`: the reduced velocity and the
  reduced elliptic equation agree off the axis with the physical streamfunction description
  (`streamfunctionVelocityReconstruction`, `IsStreamfunctionForAzimuthalVorticity`).

## How it works

The axis-extended residuals are defined piecewise, so off the axis they are the open-half-plane
residuals (`axisExtendedReducedSwirlResidual_of_ne` and its two companions), which gives
`satisfiesAxisExtendedResidualSystemOn_iff_of_radius_ne_zero`. For the physical description we
differentiate `ψ = r² ψ₁` by the product rule (`partialDeriv_streamfunctionRadialLift_radial`,
`partialDeriv_streamfunctionRadialLift_axial`) and divide by `r ≠ 0`, which gives the reduced
velocity. The stream operator of `r² ψ₁` is `r² (∂_{rr} + 3r⁻¹∂_r + ∂_{zz})ψ₁`
(`axisymmetricStreamOperator_radialLift`), so the reduced elliptic equation gives the physical one
for `ω_θ = r ω₁` (`isStreamfunctionForAzimuthalVorticity_of_reduced`). Radial evenness of a
differentiable field makes its radial derivative vanish on the axis
(`swirl_radialDerivative_axis_eq_zero` and its two companions).

## Implementation notes

The open-half-plane formulation and the assigned value at `r = 0` are kept separate. Lean's field
division is total, so evaluating `3r⁻¹∂_r f` at `r = 0` would not produce the limit for a smooth
radial profile. For a sufficiently smooth even radial profile that limit is `4∂_{rr}f + ∂_{zz}f`,
and the piecewise operator with this axis value is `axisExtendedRadialFourAxialLaplacian`. Radial
parity and regularity are separate hypotheses rather than consequences of that definition.

## References

* M. R. Ukhovskii and V. I. Yudovich, "Axially symmetric flows of ideal and viscous fluids filling
  the whole space", J. Appl. Math. Mech. 32 (1968), no. 1, 52-62.
  <https://doi.org/10.1016/0021-8928(68)90147-0>
* T. Y. Hou and C. Li, "Dynamic stability of the three-dimensional axisymmetric Navier-Stokes
  equations with swirl", Comm. Pure Appl. Math. 61 (2008), no. 5, 661-697, for the reduced variables
  and equations.
  <https://doi.org/10.1002/cpa.20212>
-/

@[expose] public section

open PDE (advectiveDerivative)

namespace AxisymmetricFlow

open EuclideanSpace
open PDE.Common

set_option linter.missingDocs true

noncomputable section


/-- Open meridian half-plane `{(r,z) | 0 < r}`. -/
def positiveRadiusMeridian : Set (ℝ^2) :=
  coordinateUpperHalfSpace (0 : Fin 2)

/-- Closed meridian half-plane `{(r,z) | 0 ≤ r}`. -/
def nonnegativeRadiusMeridian : Set (ℝ^2) :=
  {x | 0 ≤ x (0 : Fin 2)}

/-- The positive-radius meridian is open. -/
theorem isOpen_positiveRadiusMeridian :
    IsOpen positiveRadiusMeridian :=
  isOpen_coordinateUpperHalfSpace (0 : Fin 2)

/-- The closure of the positive-radius meridian is the closed meridian
half-plane. -/
theorem closure_positiveRadiusMeridian :
    closure positiveRadiusMeridian = nonnegativeRadiusMeridian := by
  exact closure_coordinateUpperHalfSpace (0 : Fin 2)

/-- Membership in the positive-radius meridian is exactly positivity of the
radial coordinate. -/
theorem mem_positiveRadiusMeridian_iff (x : ℝ^2) :
    x ∈ positiveRadiusMeridian ↔ 0 < x (0 : Fin 2) :=
  Iff.rfl

/-- Membership in the closed meridian is exactly nonnegativity of the radial
coordinate. -/
theorem mem_nonnegativeRadiusMeridian_iff (x : ℝ^2) :
    x ∈ nonnegativeRadiusMeridian ↔ 0 ≤ x (0 : Fin 2) :=
  Iff.rfl

/-- Reduced swirl, azimuthal vorticity, and streamfunction variables. -/
structure ReducedFields where
  /-- Desingularized swirl `u₁ = u_θ/r`. -/
  swirl : ℝ^2 → ℝ → ℝ
  /-- Desingularized azimuthal vorticity `ω₁ = ω_θ/r`. -/
  vorticity : ℝ^2 → ℝ → ℝ
  /-- Desingularized streamfunction `ψ₁`, with scalar Stokes streamfunction
  `ψ = r²ψ₁`. -/
  streamFunction : ℝ^2 → ℝ → ℝ

/-- The zero reduced axisymmetric fields. -/
def zeroReducedFields : ReducedFields where
  swirl := fun _ _ ↦ 0
  vorticity := fun _ _ ↦ 0
  streamFunction := fun _ _ ↦ 0

/-- Physical azimuthal velocity `u_θ = r u₁`. -/
def azimuthalVelocity
    (fields : ReducedFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  x (0 : Fin 2) * fields.swirl x t

/-- Physical azimuthal vorticity `ω_θ = r ω₁`. -/
def physicalAzimuthalVorticity
    (fields : ReducedFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  x (0 : Fin 2) * fields.vorticity x t

/-- Scalar Stokes streamfunction `ψ = r²ψ₁`. -/
def physicalStreamFunction
    (fields : ReducedFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  streamfunctionRadialLift (fun y ↦ fields.streamFunction y t) x

/-- Radial velocity `u_r = -r∂_zψ₁`. -/
def reducedRadialVelocity
    (fields : ReducedFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  -x (0 : Fin 2) *
    (∂[(1 : Fin 2)] (fun y ↦ fields.streamFunction y t)) x

/-- Axial velocity `u_z = 2ψ₁ + r∂_rψ₁`. -/
def reducedAxialVelocity
    (fields : ReducedFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  2 * fields.streamFunction x t +
    x (0 : Fin 2) *
      (∂[(0 : Fin 2)] (fun y ↦ fields.streamFunction y t)) x

/-- Meridian velocity `(u_r,u_z)` reconstructed from `ψ₁`. -/
def reducedMeridianVelocity
    (fields : ReducedFields) (x : ℝ^2) (t : ℝ) : ℝ^2 :=
  meridianFlux
    (fun y ↦ reducedRadialVelocity fields y t)
    (fun y ↦ reducedAxialVelocity fields y t) x

/-- Radial component of the reconstructed meridian velocity. -/
@[simp]
theorem reducedMeridianVelocity_radial
    (fields : ReducedFields) (x : ℝ^2) (t : ℝ) :
    reducedMeridianVelocity fields x t (0 : Fin 2) =
      reducedRadialVelocity fields x t := by
  simp [reducedMeridianVelocity, meridianFlux]

/-- Axial component of the reconstructed meridian velocity. -/
@[simp]
theorem reducedMeridianVelocity_axial
    (fields : ReducedFields) (x : ℝ^2) (t : ℝ) :
    reducedMeridianVelocity fields x t (1 : Fin 2) =
      reducedAxialVelocity fields x t := by
  simp [reducedMeridianVelocity, meridianFlux]

/-- The radial velocity vanishes on the symmetry axis. -/
@[simp]
theorem reducedRadialVelocity_axisPoint
    (fields : ReducedFields) (z t : ℝ) :
    reducedRadialVelocity fields (!₂[0, z]) t = 0 := by
  simp [reducedRadialVelocity]

/-- The axis value of the axial velocity is `2ψ₁`. -/
@[simp]
theorem reducedAxialVelocity_axisPoint
    (fields : ReducedFields) (z t : ℝ) :
    reducedAxialVelocity fields (!₂[0, z]) t =
      2 * fields.streamFunction (!₂[0, z]) t := by
  simp [reducedAxialVelocity]

/-- Axis-value extension of the radial-four-plus-axial Laplacian.

Away from the axis this is `∂_{rr} + 3r⁻¹∂_r + ∂_{zz}`. At the axis it
assigns `4∂_{rr} + ∂_{zz}`, the limiting value for a sufficiently smooth
radially even profile. Continuity of the piecewise expression at the axis needs
radial parity and regularity hypotheses (see `AxisRegularDiffusion`). -/
def axisExtendedRadialFourAxialLaplacian
    (f : ℝ^2 → ℝ) (x : ℝ^2) : ℝ :=
  if x (0 : Fin 2) = 0 then
    4 * (∂[(0 : Fin 2)]
          (fun y ↦ (∂[(0 : Fin 2)] f) y)) x +
      (∂[(1 : Fin 2)]
          (fun y ↦ (∂[(1 : Fin 2)] f) y)) x
  else
    radialFourAxialLaplacian f x

/-- Off the axis, the axis-extended operator is the ordinary reduced
Laplacian. -/
theorem axisExtendedRadialFourAxialLaplacian_of_ne
    (f : ℝ^2 → ℝ) (x : ℝ^2)
    (hr : x (0 : Fin 2) ≠ 0) :
    axisExtendedRadialFourAxialLaplacian f x =
      radialFourAxialLaplacian f x := by
  simp [axisExtendedRadialFourAxialLaplacian, hr]

/-- On the axis, the axis-extended operator has coefficient four on the radial
second derivative. -/
theorem axisExtendedRadialFourAxialLaplacian_of_eq_zero
    (f : ℝ^2 → ℝ) (x : ℝ^2)
    (hr : x (0 : Fin 2) = 0) :
    axisExtendedRadialFourAxialLaplacian f x =
      4 * (∂[(0 : Fin 2)]
          (fun y ↦ (∂[(0 : Fin 2)] f) y)) x +
        (∂[(1 : Fin 2)]
          (fun y ↦ (∂[(1 : Fin 2)] f) y)) x := by
  simp [axisExtendedRadialFourAxialLaplacian, hr]

/-- Axis formula for the axis-extended operator. -/
@[simp]
theorem axisExtendedRadialFourAxialLaplacian_axisPoint
    (f : ℝ^2 → ℝ) (z : ℝ) :
    axisExtendedRadialFourAxialLaplacian f (!₂[0, z]) =
      4 * (∂[(0 : Fin 2)]
          (fun y ↦ (∂[(0 : Fin 2)] f) y)) (!₂[0, z]) +
        (∂[(1 : Fin 2)]
          (fun y ↦ (∂[(1 : Fin 2)] f) y)) (!₂[0, z]) := by
  exact axisExtendedRadialFourAxialLaplacian_of_eq_zero f (!₂[0, z]) (by simp)

/-- Pointwise transport of a scalar by the reduced meridian velocity. -/
def reducedAdvection
    (fields : ReducedFields) (f : ℝ^2 → ℝ)
    (x : ℝ^2) (t : ℝ) : ℝ :=
  advectiveDerivative
    (fun y ↦ reducedMeridianVelocity fields y t) f x

/-- Coordinate expansion of reduced meridian advection. -/
theorem reducedAdvection_eq
    (fields : ReducedFields) (f : ℝ^2 → ℝ)
    (x : ℝ^2) (t : ℝ) :
    reducedAdvection fields f x t =
      reducedRadialVelocity fields x t *
          (∂[(0 : Fin 2)] f) x +
        reducedAxialVelocity fields x t *
          (∂[(1 : Fin 2)] f) x := by
  rw [reducedAdvection, PDE.advectiveDerivative_eq_sum_mul_partialDeriv]
  simp [Fin.sum_univ_two]

/-- Stretching source `2u₁∂_zψ₁` in the reduced swirl equation. -/
def reducedSwirlSource
    (fields : ReducedFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  2 * fields.swirl x t *
    (∂[(1 : Fin 2)] (fun y ↦ fields.streamFunction y t)) x

/-- Quadratic source `2u₁∂_z u₁` in the reduced vorticity equation. -/
def reducedVorticitySource
    (fields : ReducedFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  2 * fields.swirl x t *
    (∂[(1 : Fin 2)] (fun y ↦ fields.swirl y t)) x

/-- Conservative form `∂_z(u₁²)` of the reduced vorticity source. -/
def conservativeReducedVorticitySource
    (fields : ReducedFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  (∂[(1 : Fin 2)]
    (fun y ↦ (fields.swirl y t) ^ 2)) x

/-- For differentiable swirl, the conservative and product forms of the
quadratic vorticity source agree. -/
theorem conservativeReducedVorticitySource_eq
    (fields : ReducedFields) (x : ℝ^2) (t : ℝ)
    (hswirl : DifferentiableAt ℝ (fun y ↦ fields.swirl y t) x) :
    conservativeReducedVorticitySource fields x t =
      reducedVorticitySource fields x t := by
  unfold conservativeReducedVorticitySource
  rw [show (fun y ↦ (fields.swirl y t) ^ 2) =
      fun y ↦ fields.swirl y t * fields.swirl y t by
    funext y
    ring]
  rw [PDE.partialDeriv_mul hswirl hswirl]
  simp [reducedVorticitySource]
  ring

/-- Pointwise defect in the off-axis reduced swirl equation. -/
def reducedSwirlResidual
    (ν : ℝ) (fields : ReducedFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  deriv (fun s ↦ fields.swirl x s) t +
      reducedAdvection fields (fun y ↦ fields.swirl y t) x t -
    (reducedSwirlSource fields x t +
      ν * radialFourAxialLaplacian (fun y ↦ fields.swirl y t) x)

/-- Pointwise defect in the off-axis reduced vorticity equation. -/
def reducedVorticityResidual
    (ν : ℝ) (fields : ReducedFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  deriv (fun s ↦ fields.vorticity x s) t +
      reducedAdvection fields (fun y ↦ fields.vorticity y t) x t -
    (reducedVorticitySource fields x t +
      ν * radialFourAxialLaplacian (fun y ↦ fields.vorticity y t) x)

/-- Pointwise defect in the reduced streamfunction equation. -/
def reducedStreamFunctionResidual
    (fields : ReducedFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  -radialFourAxialLaplacian
      (fun y ↦ fields.streamFunction y t) x -
    fields.vorticity x t

/-- Pointwise defect in the axis-value-extended reduced swirl equation. -/
def axisExtendedReducedSwirlResidual
    (ν : ℝ) (fields : ReducedFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  deriv (fun s ↦ fields.swirl x s) t +
      reducedAdvection fields (fun y ↦ fields.swirl y t) x t -
    (reducedSwirlSource fields x t +
      ν * axisExtendedRadialFourAxialLaplacian
        (fun y ↦ fields.swirl y t) x)

/-- Pointwise defect in the axis-value-extended reduced vorticity equation. -/
def axisExtendedReducedVorticityResidual
    (ν : ℝ) (fields : ReducedFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  deriv (fun s ↦ fields.vorticity x s) t +
      reducedAdvection fields (fun y ↦ fields.vorticity y t) x t -
    (reducedVorticitySource fields x t +
      ν * axisExtendedRadialFourAxialLaplacian
        (fun y ↦ fields.vorticity y t) x)

/-- Pointwise defect in the axis-value-extended streamfunction equation. -/
def axisExtendedReducedStreamFunctionResidual
    (fields : ReducedFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  -axisExtendedRadialFourAxialLaplacian
      (fun y ↦ fields.streamFunction y t) x -
    fields.vorticity x t

/-- At zero viscosity, the diffusion value on the axis does not affect swirl evolution. -/
theorem axisExtendedReducedSwirlResidual_zero
    (fields : ReducedFields) (x : ℝ^2) (t : ℝ) :
    axisExtendedReducedSwirlResidual 0 fields x t = reducedSwirlResidual 0 fields x t := by
  simp [axisExtendedReducedSwirlResidual, reducedSwirlResidual]

/-- At zero viscosity, the diffusion value on the axis does not affect vorticity evolution. -/
theorem axisExtendedReducedVorticityResidual_zero
    (fields : ReducedFields) (x : ℝ^2) (t : ℝ) :
    axisExtendedReducedVorticityResidual 0 fields x t =
      reducedVorticityResidual 0 fields x t := by
  simp [axisExtendedReducedVorticityResidual, reducedVorticityResidual]

/-- Off the axis, the axis-extended and ordinary swirl residuals agree. -/
theorem axisExtendedReducedSwirlResidual_of_ne
    (ν : ℝ) (fields : ReducedFields) (x : ℝ^2) (t : ℝ)
    (hr : x (0 : Fin 2) ≠ 0) :
    axisExtendedReducedSwirlResidual ν fields x t =
      reducedSwirlResidual ν fields x t := by
  simp [axisExtendedReducedSwirlResidual, reducedSwirlResidual,
    axisExtendedRadialFourAxialLaplacian_of_ne _ _ hr]

/-- Off the axis, the axis-extended and ordinary vorticity residuals agree. -/
theorem axisExtendedReducedVorticityResidual_of_ne
    (ν : ℝ) (fields : ReducedFields) (x : ℝ^2) (t : ℝ)
    (hr : x (0 : Fin 2) ≠ 0) :
    axisExtendedReducedVorticityResidual ν fields x t =
      reducedVorticityResidual ν fields x t := by
  simp [axisExtendedReducedVorticityResidual, reducedVorticityResidual,
    axisExtendedRadialFourAxialLaplacian_of_ne _ _ hr]

/-- Off the axis, the axis-extended and ordinary streamfunction residuals
agree. -/
theorem axisExtendedReducedStreamFunctionResidual_of_ne
    (fields : ReducedFields) (x : ℝ^2) (t : ℝ)
    (hr : x (0 : Fin 2) ≠ 0) :
    axisExtendedReducedStreamFunctionResidual fields x t =
      reducedStreamFunctionResidual fields x t := by
  simp [axisExtendedReducedStreamFunctionResidual,
    reducedStreamFunctionResidual,
    axisExtendedRadialFourAxialLaplacian_of_ne _ _ hr]

/-- Classical regularity for reduced axisymmetric fields on a set of times.

The swirl and vorticity evolution equations use joint `C¹` regularity, while
all three fields require spatial `C²` slices. The streamfunction needs no
separate time derivative in the elliptic equation or velocity reconstruction. -/
structure HasClassicalReducedRegularityOn
    (fields : ReducedFields) (times : Set ℝ) : Prop where
  /-- Joint first-order regularity of reduced swirl. -/
  swirl_contDiffOn :
    ContDiffOn ℝ 1
      (fun xt : ℝ^2 × ℝ ↦ fields.swirl xt.1 xt.2)
      (Set.univ ×ˢ times)
  /-- Joint first-order regularity of reduced vorticity. -/
  vorticity_contDiffOn :
    ContDiffOn ℝ 1
      (fun xt : ℝ^2 × ℝ ↦ fields.vorticity xt.1 xt.2)
      (Set.univ ×ˢ times)
  /-- Every admitted swirl time slice is differentiable in time. -/
  swirl_differentiableAt_time
      {x : ℝ^2} {t : ℝ} (ht : t ∈ times) :
    DifferentiableAt ℝ (fun s ↦ fields.swirl x s) t
  /-- Every admitted vorticity time slice is differentiable in time. -/
  vorticity_differentiableAt_time
      {x : ℝ^2} {t : ℝ} (ht : t ∈ times) :
    DifferentiableAt ℝ (fun s ↦ fields.vorticity x s) t
  /-- Every admitted swirl slice is globally `C²` in meridian space. -/
  swirl_spatial_contDiff {t : ℝ} (ht : t ∈ times) :
    ContDiff ℝ 2 (fun x ↦ fields.swirl x t)
  /-- Every admitted vorticity slice is globally `C²` in meridian space. -/
  vorticity_spatial_contDiff {t : ℝ} (ht : t ∈ times) :
    ContDiff ℝ 2 (fun x ↦ fields.vorticity x t)
  /-- Every admitted streamfunction slice is globally `C²` in meridian
  space. -/
  streamFunction_spatial_contDiff {t : ℝ} (ht : t ∈ times) :
    ContDiff ℝ 2 (fun x ↦ fields.streamFunction x t)

/-- The off-axis reduced swirl equation on a spatial domain and time set. -/
def SatisfiesReducedSwirlEquationOn
    (ν : ℝ) (fields : ReducedFields)
    (domain : Set (ℝ^2)) (times : Set ℝ) : Prop :=
  ∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ domain → t ∈ times →
    reducedSwirlResidual ν fields x t = 0

/-- The off-axis reduced vorticity equation on a spatial domain and time
set. -/
def SatisfiesReducedVorticityEquationOn
    (ν : ℝ) (fields : ReducedFields)
    (domain : Set (ℝ^2)) (times : Set ℝ) : Prop :=
  ∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ domain → t ∈ times →
    reducedVorticityResidual ν fields x t = 0

/-- The off-axis reduced streamfunction equation on a spatial domain and
time set. -/
def SatisfiesReducedStreamFunctionEquationOn
    (fields : ReducedFields)
    (domain : Set (ℝ^2)) (times : Set ℝ) : Prop :=
  ∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ domain → t ∈ times →
    reducedStreamFunctionResidual fields x t = 0

/-- All three off-axis reduced equations. -/
def SatisfiesReducedSystemOn
    (ν : ℝ) (fields : ReducedFields)
    (domain : Set (ℝ^2)) (times : Set ℝ) : Prop :=
  SatisfiesReducedSwirlEquationOn ν fields domain times ∧
    SatisfiesReducedVorticityEquationOn ν fields domain times ∧
    SatisfiesReducedStreamFunctionEquationOn fields domain times

/-- All three algebraically axis-extended residual equations on a spatial domain and time set.

Radial parity is not part of the predicate. For the smooth-axis
interpretation, combine it with `HasRadiallyEvenReducedFieldsOn` and suitable
regularity assumptions. -/
def SatisfiesAxisExtendedResidualSystemOn
    (ν : ℝ) (fields : ReducedFields)
    (domain : Set (ℝ^2)) (times : Set ℝ) : Prop :=
  (∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ domain → t ∈ times →
      axisExtendedReducedSwirlResidual ν fields x t = 0) ∧
    (∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ domain → t ∈ times →
      axisExtendedReducedVorticityResidual ν fields x t = 0) ∧
    (∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ domain → t ∈ times →
      axisExtendedReducedStreamFunctionResidual fields x t = 0)

/-- A reduced solution restricts to smaller spatial and temporal domains. -/
theorem SatisfiesReducedSystemOn.mono
    {ν : ℝ} {fields : ReducedFields} {domain domain' : Set (ℝ^2)} {times times' : Set ℝ}
    (h : SatisfiesReducedSystemOn ν fields domain times)
    (hdomain : domain' ⊆ domain) (htimes : times' ⊆ times) :
    SatisfiesReducedSystemOn ν fields domain' times' :=
  ⟨fun _ _ hx ht ↦ h.1 (hdomain hx) (htimes ht),
    fun _ _ hx ht ↦ h.2.1 (hdomain hx) (htimes ht),
    fun _ _ hx ht ↦ h.2.2 (hdomain hx) (htimes ht)⟩

/-- An axis-extended solution restricts to smaller spatial and temporal domains. -/
theorem SatisfiesAxisExtendedResidualSystemOn.mono
    {ν : ℝ} {fields : ReducedFields} {domain domain' : Set (ℝ^2)} {times times' : Set ℝ}
    (h : SatisfiesAxisExtendedResidualSystemOn ν fields domain times)
    (hdomain : domain' ⊆ domain) (htimes : times' ⊆ times) :
    SatisfiesAxisExtendedResidualSystemOn ν fields domain' times' :=
  ⟨fun _ _ hx ht ↦ h.1 (hdomain hx) (htimes ht),
    fun _ _ hx ht ↦ h.2.1 (hdomain hx) (htimes ht),
    fun _ _ hx ht ↦ h.2.2 (hdomain hx) (htimes ht)⟩

/-- Away from the axis, the complete ordinary and axis-extended systems agree.
The radius hypothesis remains necessary for the stream equation even at zero viscosity. -/
theorem satisfiesAxisExtendedResidualSystemOn_iff_of_radius_ne_zero
    (ν : ℝ) (fields : ReducedFields) (domain : Set (ℝ^2)) (times : Set ℝ)
    (hr : ∀ x ∈ domain, x (0 : Fin 2) ≠ 0) :
    SatisfiesAxisExtendedResidualSystemOn ν fields domain times ↔
      SatisfiesReducedSystemOn ν fields domain times := by
  have hs := fun x hx t ↦ axisExtendedReducedSwirlResidual_of_ne ν fields x t (hr x hx)
  have hv := fun x hx t ↦ axisExtendedReducedVorticityResidual_of_ne ν fields x t (hr x hx)
  have hp := fun x hx t ↦ axisExtendedReducedStreamFunctionResidual_of_ne fields x t (hr x hx)
  constructor
  · rintro ⟨hu, hω, hψ⟩
    exact ⟨fun x t hx ht ↦ (hs x hx t).symm.trans (hu hx ht),
      fun x t hx ht ↦ (hv x hx t).symm.trans (hω hx ht),
      fun x t hx ht ↦ (hp x hx t).symm.trans (hψ hx ht)⟩
  · rintro ⟨hu, hω, hψ⟩
    exact ⟨fun x t hx ht ↦ (hs x hx t).trans (hu hx ht),
      fun x t hx ht ↦ (hv x hx t).trans (hω hx ht),
      fun x t hx ht ↦ (hp x hx t).trans (hψ hx ht)⟩

/-- Radial-even parity of all three reduced scalar fields at admitted
times. -/
def HasRadiallyEvenReducedFieldsOn
    (fields : ReducedFields) (times : Set ℝ) : Prop :=
  (∀ ⦃t : ℝ⦄, t ∈ times →
      IsEvenUnderCoordinateReflection (0 : Fin 2)
        (fun x ↦ fields.swirl x t)) ∧
    (∀ ⦃t : ℝ⦄, t ∈ times →
      IsEvenUnderCoordinateReflection (0 : Fin 2)
        (fun x ↦ fields.vorticity x t)) ∧
    (∀ ⦃t : ℝ⦄, t ∈ times →
      IsEvenUnderCoordinateReflection (0 : Fin 2)
        (fun x ↦ fields.streamFunction x t))

/-- Radial-even swirl has zero radial derivative on the axis. -/
theorem swirl_radialDerivative_axis_eq_zero
    (fields : ReducedFields) (times : Set ℝ)
    (heven : HasRadiallyEvenReducedFieldsOn fields times)
    (hregularity : HasClassicalReducedRegularityOn fields times)
    (z : ℝ) {t : ℝ} (ht : t ∈ times) :
    (∂[(0 : Fin 2)] (fun x ↦ fields.swirl x t))
      (!₂[0, z]) = 0 := by
  exact (heven.1 ht).partialDeriv_eq_zero
    (by simp [coordinateHyperplane])
    ((hregularity.swirl_spatial_contDiff ht).differentiable
      (by norm_num)).differentiableAt

/-- Radial-even vorticity has zero radial derivative on the axis. -/
theorem vorticity_radialDerivative_axis_eq_zero
    (fields : ReducedFields) (times : Set ℝ)
    (heven : HasRadiallyEvenReducedFieldsOn fields times)
    (hregularity : HasClassicalReducedRegularityOn fields times)
    (z : ℝ) {t : ℝ} (ht : t ∈ times) :
    (∂[(0 : Fin 2)] (fun x ↦ fields.vorticity x t))
      (!₂[0, z]) = 0 := by
  exact (heven.2.1 ht).partialDeriv_eq_zero
    (by simp [coordinateHyperplane])
    ((hregularity.vorticity_spatial_contDiff ht).differentiable
      (by norm_num)).differentiableAt

/-- Radial-even streamfunction has zero radial derivative on the axis. -/
theorem streamFunction_radialDerivative_axis_eq_zero
    (fields : ReducedFields) (times : Set ℝ)
    (heven : HasRadiallyEvenReducedFieldsOn fields times)
    (hregularity : HasClassicalReducedRegularityOn fields times)
    (z : ℝ) {t : ℝ} (ht : t ∈ times) :
    (∂[(0 : Fin 2)] (fun x ↦ fields.streamFunction x t))
      (!₂[0, z]) = 0 := by
  exact (heven.2.2 ht).partialDeriv_eq_zero
    (by simp [coordinateHyperplane])
    ((hregularity.streamFunction_spatial_contDiff ht).differentiable
      (by norm_num)).differentiableAt

/-- Derivative of the radial lift in the axial direction. -/
theorem partialDeriv_streamfunctionRadialLift_axial
    (φ : ℝ^2 → ℝ) (hφ : Differentiable ℝ φ) (x : ℝ^2) :
    (∂[(1 : Fin 2)] (streamfunctionRadialLift φ)) x =
      (x (0 : Fin 2)) ^ 2 * (∂[(1 : Fin 2)] φ) x := by
  have hcoordDiff (i : Fin 2) :
      Differentiable ℝ (fun y : ℝ^2 ↦ y i) := by
    simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj i : ℝ^2 →L[ℝ] ℝ).differentiable
  have hcoord :
      Differentiable ℝ (fun y : ℝ^2 ↦ (y (0 : Fin 2)) ^ 2) := by
    cas
  have hsq :
      (∂[(1 : Fin 2)]
          (fun y : ℝ^2 ↦ (y (0 : Fin 2)) ^ 2)) x = 0 := by
    cas
  rw [show streamfunctionRadialLift φ =
      fun y ↦ (y (0 : Fin 2)) ^ 2 * φ y by rfl]
  rw [PDE.partialDeriv_mul hcoord.differentiableAt hφ.differentiableAt]
  rw [hsq]
  ring

/-- Derivative of the radial lift in the radial direction. -/
theorem partialDeriv_streamfunctionRadialLift_radial
    (φ : ℝ^2 → ℝ) (hφ : Differentiable ℝ φ) (x : ℝ^2) :
    (∂[(0 : Fin 2)] (streamfunctionRadialLift φ)) x =
      2 * x (0 : Fin 2) * φ x +
        (x (0 : Fin 2)) ^ 2 * (∂[(0 : Fin 2)] φ) x := by
  have hcoordDiff (i : Fin 2) :
      Differentiable ℝ (fun y : ℝ^2 ↦ y i) := by
    simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj i : ℝ^2 →L[ℝ] ℝ).differentiable
  have hcoord :
      Differentiable ℝ (fun y : ℝ^2 ↦ (y (0 : Fin 2)) ^ 2) := by
    cas
  rw [show streamfunctionRadialLift φ =
      fun y ↦ (y (0 : Fin 2)) ^ 2 * φ y by rfl]
  rw [PDE.partialDeriv_mul hcoord.differentiableAt hφ.differentiableAt]
  rw [show (∂[(0 : Fin 2)]
      (fun y : ℝ^2 ↦ (y (0 : Fin 2)) ^ 2)) x =
        2 * x (0 : Fin 2) by
    cas]

/-- Off the axis, radial-lift streamfunction reconstruction gives
`u_r = -r∂_zψ₁`. -/
theorem reconstructedRadialVelocity_radialLift
    (φ : ℝ^2 → ℝ) (hφ : Differentiable ℝ φ)
    (x : ℝ^2) (hr : x (0 : Fin 2) ≠ 0) :
    reconstructedRadialVelocity (streamfunctionRadialLift φ) x =
      -x (0 : Fin 2) * (∂[(1 : Fin 2)] φ) x := by
  rw [reconstructedRadialVelocity,
    partialDeriv_streamfunctionRadialLift_axial φ hφ x]
  field_simp

/-- Off the axis, radial-lift streamfunction reconstruction gives
`u_z = 2ψ₁ + r∂_rψ₁`. -/
theorem reconstructedAxialVelocity_radialLift
    (φ : ℝ^2 → ℝ) (hφ : Differentiable ℝ φ)
    (x : ℝ^2) (hr : x (0 : Fin 2) ≠ 0) :
    reconstructedAxialVelocity (streamfunctionRadialLift φ) x =
      2 * φ x + x (0 : Fin 2) * (∂[(0 : Fin 2)] φ) x := by
  rw [reconstructedAxialVelocity,
    partialDeriv_streamfunctionRadialLift_radial φ hφ x]
  field_simp

/-- The reduced velocity agrees off-axis with reconstruction from the
physical scalar streamfunction `r²ψ₁`. -/
theorem streamfunctionVelocityReconstruction_physicalStreamFunction
    (fields : ReducedFields) (x : ℝ^2) (t : ℝ)
    (hstream : Differentiable ℝ (fun y ↦ fields.streamFunction y t))
    (hr : x (0 : Fin 2) ≠ 0) :
    streamfunctionVelocityReconstruction
        (fun y ↦ physicalStreamFunction fields y t) x =
      reducedMeridianVelocity fields x t := by
  ext i
  fin_cases i
  · change
      streamfunctionVelocityReconstruction
          (fun y ↦ physicalStreamFunction fields y t) x (0 : Fin 2) =
        reducedMeridianVelocity fields x t (0 : Fin 2)
    rw [streamfunctionVelocityReconstruction_radial,
      reducedMeridianVelocity_radial]
    exact reconstructedRadialVelocity_radialLift
      (fun y ↦ fields.streamFunction y t) hstream x hr
  · change
      streamfunctionVelocityReconstruction
          (fun y ↦ physicalStreamFunction fields y t) x (1 : Fin 2) =
        reducedMeridianVelocity fields x t (1 : Fin 2)
    rw [streamfunctionVelocityReconstruction_axial,
      reducedMeridianVelocity_axial]
    exact reconstructedAxialVelocity_radialLift
      (fun y ↦ fields.streamFunction y t) hstream x hr

/-- The reduced elliptic equation implies the physical
streamfunction equation for `ω_θ = rω₁`. -/
theorem isStreamfunctionForAzimuthalVorticity_of_reduced
    (ω₁ ψ₁ : ℝ^2 → ℝ) (hψ : ContDiff ℝ 2 ψ₁)
    (helliptic :
      ∀ x, x (0 : Fin 2) ≠ 0 →
        -radialFourAxialLaplacian ψ₁ x = ω₁ x) :
    IsStreamfunctionForAzimuthalVorticity
      (fun x ↦ x (0 : Fin 2) * ω₁ x)
      (streamfunctionRadialLift ψ₁) := by
  intro x hr
  rw [axisymmetricStreamOperator_radialLift ψ₁ hψ x hr]
  have h := helliptic x hr
  rw [show radialFourAxialLaplacian ψ₁ x = -ω₁ x by linarith]
  ring

/-- A reduced streamfunction solution gives the physical streamfunction
equation at every admitted time. -/
theorem physicalStreamFunction_isStreamfunctionForAzimuthalVorticity
    (fields : ReducedFields) (times : Set ℝ)
    (hregularity : HasClassicalReducedRegularityOn fields times)
    (hstream :
      SatisfiesReducedStreamFunctionEquationOn fields
        {x : ℝ^2 | x (0 : Fin 2) ≠ 0} times)
    {t : ℝ} (ht : t ∈ times) :
    IsStreamfunctionForAzimuthalVorticity
      (fun x ↦ physicalAzimuthalVorticity fields x t)
      (fun x ↦ physicalStreamFunction fields x t) := by
  apply isStreamfunctionForAzimuthalVorticity_of_reduced
    (fun x ↦ fields.vorticity x t)
    (fun x ↦ fields.streamFunction x t)
    (hregularity.streamFunction_spatial_contDiff ht)
  intro x hr
  have hzero := hstream hr ht
  unfold reducedStreamFunctionResidual at hzero
  linarith

/-- The zero reduced fields have classical regularity on every time set. -/
theorem zeroReducedFields_hasClassicalRegularityOn (times : Set ℝ) :
    HasClassicalReducedRegularityOn zeroReducedFields times := by
  refine
    { swirl_contDiffOn := by fun_prop
      vorticity_contDiffOn := by fun_prop
      swirl_differentiableAt_time := by
        intro x t ht
        fun_prop
      vorticity_differentiableAt_time := by
        intro x t ht
        fun_prop
      swirl_spatial_contDiff := by
        intro t ht
        fun_prop
      vorticity_spatial_contDiff := by
        intro t ht
        fun_prop
      streamFunction_spatial_contDiff := by
        intro t ht
        fun_prop }

/-- The zero reduced fields solve the off-axis reduced system for every
viscosity and every time set. -/
theorem zeroReducedFields_satisfiesReducedSystemOn
    (ν : ℝ) (times : Set ℝ) :
    SatisfiesReducedSystemOn
      ν zeroReducedFields positiveRadiusMeridian times := by
  refine ⟨?_, ?_, ?_⟩
  · intro x t hx ht
    simp [reducedSwirlResidual, reducedAdvection, reducedSwirlSource,
      zeroReducedFields, reducedMeridianVelocity, reducedRadialVelocity,
      reducedAxialVelocity, meridianFlux, advectiveDerivative,
      radialFourAxialLaplacian]
  · intro x t hx ht
    simp [reducedVorticityResidual, reducedAdvection,
      reducedVorticitySource, zeroReducedFields, reducedMeridianVelocity,
      reducedRadialVelocity, reducedAxialVelocity, meridianFlux,
      advectiveDerivative, radialFourAxialLaplacian]
  · intro x t hx ht
    simp [reducedStreamFunctionResidual, zeroReducedFields,
      radialFourAxialLaplacian]

/-- The zero fields satisfy radial-even parity. -/
theorem zeroReducedFields_hasRadiallyEvenOn (times : Set ℝ) :
    HasRadiallyEvenReducedFieldsOn zeroReducedFields times := by
  refine ⟨?_, ?_, ?_⟩ <;> intro t ht <;>
    simp [zeroReducedFields, IsEvenUnderCoordinateReflection]

end

end AxisymmetricFlow
