/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Axisymmetric.ReducedNavierStokes
import PDE.FDeriv.Calculus

/-!
# Modulated reduced axisymmetric equations

In dynamically rescaled meridian coordinates the reduced axisymmetric
Euler/Navier–Stokes equations acquire modulation terms. For logarithmic spatial rate
`λ(t)`, axial drift `C(t)`, amplitude rates `cᵤ(t), cω(t)`, and rescaled
viscosity `ν̃(t)`, the transport field is

```text
(λr + u_r, λz + C + u_z).
```

The scalar equations are

```text
∂_t u₁ + (λx + Ce_z + u)·∇u₁
  = 2u₁∂_zψ₁ + cᵤu₁ + ν̃ E u₁,

∂_t ω₁ + (λx + Ce_z + u)·∇ω₁
  = 2u₁∂_z u₁ + cωω₁ + ν̃ E ω₁,

-Eψ₁ = ω₁,
```

where `E = ∂_{rr} + 3r⁻¹∂_r + ∂_{zz}` away from the axis. As in
`ReducedNavierStokes`, ordinary off-axis residuals and their smooth axis
continuations are kept separate.

The definitions are independent of a particular change of variables.
`DynamicRescaling` proves how the coefficients arise from physical scales.

## Main definitions

* `rescaledReducedSwirlResidual`, `rescaledReducedVorticityResidual` and their axis-extended
  versions: the residuals of the two rescaled evolution equations.
* `SatisfiesRescaledReducedSystemOn`, `SatisfiesAxisExtendedRescaledResidualSystemOn`: the
  rescaled system on a space–time domain.
* `ReducedProfile`, `reducedSwirlProfileResidual`, `reducedVorticityProfileResidual`,
  `IsSteadyRescaledReducedProfileOn`: time-independent profiles and the steady profile
  equations.

## References

* V. Duruisseaux, A. Ganeshram, R. J. George and A. Anandkumar, "Stability Framework for the
  Singularity of the Euler Equations on ℝ³", arXiv:2609.10860v1, Section 3.1.2, Proposition 2,
  (38)-(42), p. 13, for the inviscid case.
  <https://arxiv.org/abs/2609.10860v1>
-/

@[expose] public section

open PDE (advectiveDerivative)

namespace AxisymmetricFlow

open EuclideanSpace
open PDE.Common

set_option linter.missingDocs true

noncomputable section

/-- Unit vector in the axial meridian direction. -/
def axialUnit : ℝ^2 :=
  WithLp.toLp 2 ![0, 1]

/-- The radial component of the axial unit vector is zero. -/
@[simp]
theorem axialUnit_apply_zero :
    axialUnit (0 : Fin 2) = 0 := by
  simp [axialUnit]

/-- The axial component of the axial unit vector is one. -/
@[simp]
theorem axialUnit_apply_one :
    axialUnit (1 : Fin 2) = 1 := by
  simp [axialUnit]

/-- Modulated meridian transport velocity `λ(t)x + C(t)e_z + u(x,t)`. -/
def rescaledReducedTransportVelocity
    (fields : ReducedFields)
    (spatialRate axialDrift : ℝ → ℝ)
    (x : ℝ^2) (t : ℝ) : ℝ^2 :=
  spatialRate t • x + axialDrift t • axialUnit +
    reducedMeridianVelocity fields x t

/-- Radial component of the modulated transport velocity. -/
@[simp]
theorem rescaledReducedTransportVelocity_radial
    (fields : ReducedFields)
    (spatialRate axialDrift : ℝ → ℝ)
    (x : ℝ^2) (t : ℝ) :
    rescaledReducedTransportVelocity fields spatialRate axialDrift x t
        (0 : Fin 2) =
      spatialRate t * x (0 : Fin 2) +
        reducedRadialVelocity fields x t := by
  simp [rescaledReducedTransportVelocity, smul_eq_mul]

/-- Axial component of the modulated transport velocity. -/
@[simp]
theorem rescaledReducedTransportVelocity_axial
    (fields : ReducedFields)
    (spatialRate axialDrift : ℝ → ℝ)
    (x : ℝ^2) (t : ℝ) :
    rescaledReducedTransportVelocity fields spatialRate axialDrift x t
        (1 : Fin 2) =
      spatialRate t * x (1 : Fin 2) + axialDrift t +
        reducedAxialVelocity fields x t := by
  simp [rescaledReducedTransportVelocity, smul_eq_mul]

/-- Pointwise advection by the modulated reduced transport velocity. -/
def rescaledReducedAdvection
    (fields : ReducedFields)
    (spatialRate axialDrift : ℝ → ℝ)
    (f : ℝ^2 → ℝ) (x : ℝ^2) (t : ℝ) : ℝ :=
  advectiveDerivative
    (fun y ↦
      rescaledReducedTransportVelocity fields spatialRate axialDrift y t)
    f x

/-- Coordinate expansion of modulated reduced advection. -/
theorem rescaledReducedAdvection_eq
    (fields : ReducedFields)
    (spatialRate axialDrift : ℝ → ℝ)
    (f : ℝ^2 → ℝ) (x : ℝ^2) (t : ℝ) :
    rescaledReducedAdvection fields spatialRate axialDrift f x t =
      (spatialRate t * x (0 : Fin 2) +
          reducedRadialVelocity fields x t) *
          (∂[(0 : Fin 2)] f) x +
        (spatialRate t * x (1 : Fin 2) + axialDrift t +
          reducedAxialVelocity fields x t) *
          (∂[(1 : Fin 2)] f) x := by
  rw [rescaledReducedAdvection,
    PDE.advectiveDerivative_eq_sum_mul_partialDeriv]
  simp [Fin.sum_univ_two]

/-- Pointwise defect in the off-axis dynamically rescaled swirl equation. -/
def rescaledReducedSwirlResidual
    (fields : ReducedFields)
    (viscosity spatialRate axialDrift swirlRate : ℝ → ℝ)
    (x : ℝ^2) (t : ℝ) : ℝ :=
  deriv (fun s ↦ fields.swirl x s) t +
      rescaledReducedAdvection fields spatialRate axialDrift
        (fun y ↦ fields.swirl y t) x t -
    (reducedSwirlSource fields x t +
      swirlRate t * fields.swirl x t +
      viscosity t *
        radialFourAxialLaplacian (fun y ↦ fields.swirl y t) x)

/-- Pointwise defect in the off-axis dynamically rescaled vorticity
equation. -/
def rescaledReducedVorticityResidual
    (fields : ReducedFields)
    (viscosity spatialRate axialDrift vorticityRate : ℝ → ℝ)
    (x : ℝ^2) (t : ℝ) : ℝ :=
  deriv (fun s ↦ fields.vorticity x s) t +
      rescaledReducedAdvection fields spatialRate axialDrift
        (fun y ↦ fields.vorticity y t) x t -
    (reducedVorticitySource fields x t +
      vorticityRate t * fields.vorticity x t +
      viscosity t *
        radialFourAxialLaplacian (fun y ↦ fields.vorticity y t) x)

/-- Pointwise defect in the axis-value-extended dynamically rescaled swirl
equation. -/
def axisExtendedRescaledReducedSwirlResidual
    (fields : ReducedFields)
    (viscosity spatialRate axialDrift swirlRate : ℝ → ℝ)
    (x : ℝ^2) (t : ℝ) : ℝ :=
  deriv (fun s ↦ fields.swirl x s) t +
      rescaledReducedAdvection fields spatialRate axialDrift
        (fun y ↦ fields.swirl y t) x t -
    (reducedSwirlSource fields x t +
      swirlRate t * fields.swirl x t +
      viscosity t *
        axisExtendedRadialFourAxialLaplacian
          (fun y ↦ fields.swirl y t) x)

/-- Pointwise defect in the axis-value-extended dynamically rescaled vorticity
equation. -/
def axisExtendedRescaledReducedVorticityResidual
    (fields : ReducedFields)
    (viscosity spatialRate axialDrift vorticityRate : ℝ → ℝ)
    (x : ℝ^2) (t : ℝ) : ℝ :=
  deriv (fun s ↦ fields.vorticity x s) t +
      rescaledReducedAdvection fields spatialRate axialDrift
        (fun y ↦ fields.vorticity y t) x t -
    (reducedVorticitySource fields x t +
      vorticityRate t * fields.vorticity x t +
      viscosity t *
        axisExtendedRadialFourAxialLaplacian
          (fun y ↦ fields.vorticity y t) x)

/-- Off the axis, the axis-extended and ordinary rescaled swirl residuals
agree. -/
theorem axisExtendedRescaledReducedSwirlResidual_of_ne
    (fields : ReducedFields)
    (viscosity spatialRate axialDrift swirlRate : ℝ → ℝ)
    (x : ℝ^2) (t : ℝ) (hr : x (0 : Fin 2) ≠ 0) :
    axisExtendedRescaledReducedSwirlResidual fields viscosity spatialRate
        axialDrift swirlRate x t =
      rescaledReducedSwirlResidual fields viscosity spatialRate axialDrift
        swirlRate x t := by
  simp [axisExtendedRescaledReducedSwirlResidual,
    rescaledReducedSwirlResidual,
    axisExtendedRadialFourAxialLaplacian_of_ne _ _ hr]

/-- Off the axis, the axis-extended and ordinary rescaled vorticity residuals
agree. -/
theorem axisExtendedRescaledReducedVorticityResidual_of_ne
    (fields : ReducedFields)
    (viscosity spatialRate axialDrift vorticityRate : ℝ → ℝ)
    (x : ℝ^2) (t : ℝ) (hr : x (0 : Fin 2) ≠ 0) :
    axisExtendedRescaledReducedVorticityResidual fields viscosity spatialRate
        axialDrift vorticityRate x t =
      rescaledReducedVorticityResidual fields viscosity spatialRate
        axialDrift vorticityRate x t := by
  simp [axisExtendedRescaledReducedVorticityResidual,
    rescaledReducedVorticityResidual,
    axisExtendedRadialFourAxialLaplacian_of_ne _ _ hr]

/-- The dynamically rescaled swirl equation on a space–time domain. -/
def SatisfiesRescaledReducedSwirlEquationOn
    (fields : ReducedFields)
    (viscosity spatialRate axialDrift swirlRate : ℝ → ℝ)
    (domain : Set (ℝ^2)) (times : Set ℝ) : Prop :=
  ∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ domain → t ∈ times →
    rescaledReducedSwirlResidual fields viscosity spatialRate axialDrift
      swirlRate x t = 0

/-- The dynamically rescaled vorticity equation on a space–time domain. -/
def SatisfiesRescaledReducedVorticityEquationOn
    (fields : ReducedFields)
    (viscosity spatialRate axialDrift vorticityRate : ℝ → ℝ)
    (domain : Set (ℝ^2)) (times : Set ℝ) : Prop :=
  ∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ domain → t ∈ times →
    rescaledReducedVorticityResidual fields viscosity spatialRate axialDrift
      vorticityRate x t = 0

/-- All three off-axis dynamically rescaled reduced equations. -/
def SatisfiesRescaledReducedSystemOn
    (fields : ReducedFields)
    (viscosity spatialRate axialDrift swirlRate vorticityRate : ℝ → ℝ)
    (domain : Set (ℝ^2)) (times : Set ℝ) : Prop :=
  SatisfiesRescaledReducedSwirlEquationOn fields viscosity spatialRate
      axialDrift swirlRate domain times ∧
    SatisfiesRescaledReducedVorticityEquationOn fields viscosity spatialRate
      axialDrift vorticityRate domain times ∧
    SatisfiesReducedStreamFunctionEquationOn fields domain times

/-- All three algebraically axis-extended dynamically rescaled residual equations.

The radial parity and regularity needed to lift the meridian fields to smooth
three-dimensional axisymmetric fields are not part of the predicate. -/
def SatisfiesAxisExtendedRescaledResidualSystemOn
    (fields : ReducedFields)
    (viscosity spatialRate axialDrift swirlRate vorticityRate : ℝ → ℝ)
    (domain : Set (ℝ^2)) (times : Set ℝ) : Prop :=
  (∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ domain → t ∈ times →
      axisExtendedRescaledReducedSwirlResidual fields viscosity spatialRate
        axialDrift swirlRate x t = 0) ∧
    (∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ domain → t ∈ times →
      axisExtendedRescaledReducedVorticityResidual fields viscosity spatialRate
        axialDrift vorticityRate x t = 0) ∧
    (∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ domain → t ∈ times →
      axisExtendedReducedStreamFunctionResidual fields x t = 0)

/-- A time-independent triple of reduced axisymmetric profiles. -/
structure ReducedProfile where
  /-- Desingularized swirl profile. -/
  swirl : ℝ^2 → ℝ
  /-- Desingularized azimuthal-vorticity profile. -/
  vorticity : ℝ^2 → ℝ
  /-- Desingularized streamfunction profile. -/
  streamFunction : ℝ^2 → ℝ

/-- Regard a reduced profile as a stationary time-dependent field. -/
def ReducedProfile.stationaryFields
    (profile : ReducedProfile) : ReducedFields where
  swirl := fun x _ ↦ profile.swirl x
  vorticity := fun x _ ↦ profile.vorticity x
  streamFunction := fun x _ ↦ profile.streamFunction x

/-- Meridian velocity reconstructed from a time-independent reduced profile. -/
def ReducedProfile.meridianVelocity
    (profile : ReducedProfile) (x : ℝ^2) : ℝ^2 :=
  reducedMeridianVelocity profile.stationaryFields x 0

/-- Pointwise steady rescaled swirl-profile defect. -/
def reducedSwirlProfileResidual
    (profile : ReducedProfile)
    (viscosity spatialRate axialDrift swirlRate : ℝ)
    (x : ℝ^2) : ℝ :=
  rescaledReducedAdvection profile.stationaryFields
      (fun _ ↦ spatialRate) (fun _ ↦ axialDrift) profile.swirl x 0 -
    (reducedSwirlSource profile.stationaryFields x 0 +
      swirlRate * profile.swirl x +
      viscosity * radialFourAxialLaplacian profile.swirl x)

/-- Pointwise steady rescaled vorticity-profile defect. -/
def reducedVorticityProfileResidual
    (profile : ReducedProfile)
    (viscosity spatialRate axialDrift vorticityRate : ℝ)
    (x : ℝ^2) : ℝ :=
  rescaledReducedAdvection profile.stationaryFields
      (fun _ ↦ spatialRate) (fun _ ↦ axialDrift) profile.vorticity x 0 -
    (reducedVorticitySource profile.stationaryFields x 0 +
      vorticityRate * profile.vorticity x +
      viscosity * radialFourAxialLaplacian profile.vorticity x)

/-- Pointwise steady reduced streamfunction-profile defect. -/
def reducedStreamFunctionProfileResidual
    (profile : ReducedProfile) (x : ℝ^2) : ℝ :=
  -radialFourAxialLaplacian profile.streamFunction x -
    profile.vorticity x

/-- Pointwise steady axis-value-extended swirl-profile defect. -/
def axisExtendedReducedSwirlProfileResidual
    (profile : ReducedProfile)
    (viscosity spatialRate axialDrift swirlRate : ℝ)
    (x : ℝ^2) : ℝ :=
  rescaledReducedAdvection profile.stationaryFields
      (fun _ ↦ spatialRate) (fun _ ↦ axialDrift) profile.swirl x 0 -
    (reducedSwirlSource profile.stationaryFields x 0 +
      swirlRate * profile.swirl x +
      viscosity * axisExtendedRadialFourAxialLaplacian profile.swirl x)

/-- Pointwise steady axis-value-extended vorticity-profile defect. -/
def axisExtendedReducedVorticityProfileResidual
    (profile : ReducedProfile)
    (viscosity spatialRate axialDrift vorticityRate : ℝ)
    (x : ℝ^2) : ℝ :=
  rescaledReducedAdvection profile.stationaryFields
      (fun _ ↦ spatialRate) (fun _ ↦ axialDrift) profile.vorticity x 0 -
    (reducedVorticitySource profile.stationaryFields x 0 +
      vorticityRate * profile.vorticity x +
      viscosity *
        axisExtendedRadialFourAxialLaplacian profile.vorticity x)

/-- Pointwise steady axis-value-extended streamfunction-profile defect. -/
def axisExtendedReducedStreamFunctionProfileResidual
    (profile : ReducedProfile) (x : ℝ^2) : ℝ :=
  -axisExtendedRadialFourAxialLaplacian profile.streamFunction x -
    profile.vorticity x

/-- The dynamic swirl residual of a stationary field equals its steady
profile residual. -/
theorem rescaledReducedSwirlResidual_stationaryFields
    (profile : ReducedProfile)
    (viscosity spatialRate axialDrift swirlRate : ℝ)
    (x : ℝ^2) (t : ℝ) :
    rescaledReducedSwirlResidual profile.stationaryFields
        (fun _ ↦ viscosity) (fun _ ↦ spatialRate)
        (fun _ ↦ axialDrift) (fun _ ↦ swirlRate) x t =
      reducedSwirlProfileResidual profile viscosity spatialRate axialDrift
        swirlRate x := by
  simp [rescaledReducedSwirlResidual, reducedSwirlProfileResidual,
    ReducedProfile.stationaryFields, rescaledReducedAdvection,
    rescaledReducedTransportVelocity, reducedMeridianVelocity,
    reducedRadialVelocity, reducedAxialVelocity, reducedSwirlSource,
    meridianFlux, advectiveDerivative]

/-- The dynamic vorticity residual of a stationary field equals its steady
profile residual. -/
theorem rescaledReducedVorticityResidual_stationaryFields
    (profile : ReducedProfile)
    (viscosity spatialRate axialDrift vorticityRate : ℝ)
    (x : ℝ^2) (t : ℝ) :
    rescaledReducedVorticityResidual profile.stationaryFields
        (fun _ ↦ viscosity) (fun _ ↦ spatialRate)
        (fun _ ↦ axialDrift) (fun _ ↦ vorticityRate) x t =
      reducedVorticityProfileResidual profile viscosity spatialRate axialDrift
        vorticityRate x := by
  simp [rescaledReducedVorticityResidual,
    reducedVorticityProfileResidual, ReducedProfile.stationaryFields,
    rescaledReducedAdvection, rescaledReducedTransportVelocity,
    reducedMeridianVelocity, reducedRadialVelocity, reducedAxialVelocity,
    reducedVorticitySource, meridianFlux, advectiveDerivative]

/-- The dynamic streamfunction residual of a stationary field equals its
steady profile residual. -/
theorem reducedStreamFunctionResidual_stationaryFields
    (profile : ReducedProfile) (x : ℝ^2) (t : ℝ) :
    reducedStreamFunctionResidual profile.stationaryFields x t =
      reducedStreamFunctionProfileResidual profile x := by
  rfl

/-- The dynamic axis-value-extended swirl residual of a stationary field equals its
steady profile residual. -/
theorem axisExtendedRescaledReducedSwirlResidual_stationaryFields
    (profile : ReducedProfile)
    (viscosity spatialRate axialDrift swirlRate : ℝ)
    (x : ℝ^2) (t : ℝ) :
    axisExtendedRescaledReducedSwirlResidual profile.stationaryFields
        (fun _ ↦ viscosity) (fun _ ↦ spatialRate)
        (fun _ ↦ axialDrift) (fun _ ↦ swirlRate) x t =
      axisExtendedReducedSwirlProfileResidual profile viscosity spatialRate
        axialDrift swirlRate x := by
  simp [axisExtendedRescaledReducedSwirlResidual,
    axisExtendedReducedSwirlProfileResidual,
    ReducedProfile.stationaryFields, rescaledReducedAdvection,
    rescaledReducedTransportVelocity, reducedMeridianVelocity,
    reducedRadialVelocity, reducedAxialVelocity, reducedSwirlSource,
    meridianFlux, advectiveDerivative]

/-- The dynamic axis-value-extended vorticity residual of a stationary field equals
its steady profile residual. -/
theorem axisExtendedRescaledReducedVorticityResidual_stationaryFields
    (profile : ReducedProfile)
    (viscosity spatialRate axialDrift vorticityRate : ℝ)
    (x : ℝ^2) (t : ℝ) :
    axisExtendedRescaledReducedVorticityResidual profile.stationaryFields
        (fun _ ↦ viscosity) (fun _ ↦ spatialRate)
        (fun _ ↦ axialDrift) (fun _ ↦ vorticityRate) x t =
      axisExtendedReducedVorticityProfileResidual profile viscosity spatialRate
        axialDrift vorticityRate x := by
  simp [axisExtendedRescaledReducedVorticityResidual,
    axisExtendedReducedVorticityProfileResidual,
    ReducedProfile.stationaryFields, rescaledReducedAdvection,
    rescaledReducedTransportVelocity, reducedMeridianVelocity,
    reducedRadialVelocity, reducedAxialVelocity, reducedVorticitySource,
    meridianFlux, advectiveDerivative]

/-- The dynamic axis-value-extended streamfunction residual of a stationary field
equals its steady profile residual. -/
theorem axisExtendedReducedStreamFunctionResidual_stationaryFields
    (profile : ReducedProfile) (x : ℝ^2) (t : ℝ) :
    axisExtendedReducedStreamFunctionResidual profile.stationaryFields x t =
      axisExtendedReducedStreamFunctionProfileResidual profile x := by
  rfl

/-- A steady rescaled profile solves all three profile equations on a domain. -/
def IsSteadyRescaledReducedProfileOn
    (profile : ReducedProfile)
    (viscosity spatialRate axialDrift swirlRate vorticityRate : ℝ)
    (domain : Set (ℝ^2)) : Prop :=
  (∀ ⦃x : ℝ^2⦄, x ∈ domain →
      reducedSwirlProfileResidual profile viscosity spatialRate axialDrift
        swirlRate x = 0) ∧
    (∀ ⦃x : ℝ^2⦄, x ∈ domain →
      reducedVorticityProfileResidual profile viscosity spatialRate axialDrift
        vorticityRate x = 0) ∧
    (∀ ⦃x : ℝ^2⦄, x ∈ domain →
      reducedStreamFunctionProfileResidual profile x = 0)

/-- A steady profile satisfies all three algebraically axis-extended rescaled residual equations
on a domain. A smooth three-dimensional axisymmetric lift is a separate condition. -/
def IsSteadyAxisExtendedRescaledResidualProfileOn
    (profile : ReducedProfile)
    (viscosity spatialRate axialDrift swirlRate vorticityRate : ℝ)
    (domain : Set (ℝ^2)) : Prop :=
  (∀ ⦃x : ℝ^2⦄, x ∈ domain →
      axisExtendedReducedSwirlProfileResidual profile viscosity spatialRate
        axialDrift swirlRate x = 0) ∧
    (∀ ⦃x : ℝ^2⦄, x ∈ domain →
      axisExtendedReducedVorticityProfileResidual profile viscosity spatialRate
        axialDrift vorticityRate x = 0) ∧
    (∀ ⦃x : ℝ^2⦄, x ∈ domain →
      axisExtendedReducedStreamFunctionProfileResidual profile x = 0)

/-- The zero reduced profile. -/
def zeroReducedProfile : ReducedProfile where
  swirl := fun _ ↦ 0
  vorticity := fun _ ↦ 0
  streamFunction := fun _ ↦ 0

/-- The zero profile solves every steady rescaled reduced system. -/
theorem zeroReducedProfile_isSteadyRescaledReducedProfileOn
    (viscosity spatialRate axialDrift swirlRate vorticityRate : ℝ)
    (domain : Set (ℝ^2)) :
    IsSteadyRescaledReducedProfileOn zeroReducedProfile viscosity spatialRate
      axialDrift swirlRate vorticityRate domain := by
  refine ⟨?_, ?_, ?_⟩ <;> intro x hx
  · simp [reducedSwirlProfileResidual, zeroReducedProfile,
      ReducedProfile.stationaryFields, rescaledReducedAdvection,
      rescaledReducedTransportVelocity, reducedMeridianVelocity,
      reducedRadialVelocity, reducedAxialVelocity, meridianFlux,
      advectiveDerivative, reducedSwirlSource,
      radialFourAxialLaplacian]
  · simp [reducedVorticityProfileResidual, zeroReducedProfile,
      ReducedProfile.stationaryFields, rescaledReducedAdvection,
      rescaledReducedTransportVelocity, reducedMeridianVelocity,
      reducedRadialVelocity, reducedAxialVelocity, meridianFlux,
      advectiveDerivative, reducedVorticitySource,
      radialFourAxialLaplacian]
  · simp [reducedStreamFunctionProfileResidual, zeroReducedProfile,
      radialFourAxialLaplacian]

/-- The zero profile solves every steady axis-value-extended rescaled reduced
system. -/
theorem zeroReducedProfile_isSteadyAxisExtendedRescaledResidualProfileOn
    (viscosity spatialRate axialDrift swirlRate vorticityRate : ℝ)
    (domain : Set (ℝ^2)) :
    IsSteadyAxisExtendedRescaledResidualProfileOn zeroReducedProfile viscosity
      spatialRate axialDrift swirlRate vorticityRate domain := by
  refine ⟨?_, ?_, ?_⟩ <;> intro x hx
  · simp [axisExtendedReducedSwirlProfileResidual, zeroReducedProfile,
      ReducedProfile.stationaryFields, rescaledReducedAdvection,
      rescaledReducedTransportVelocity, reducedMeridianVelocity,
      reducedRadialVelocity, reducedAxialVelocity, meridianFlux,
      advectiveDerivative, reducedSwirlSource,
      axisExtendedRadialFourAxialLaplacian,
      radialFourAxialLaplacian]
  · simp [axisExtendedReducedVorticityProfileResidual, zeroReducedProfile,
      ReducedProfile.stationaryFields, rescaledReducedAdvection,
      rescaledReducedTransportVelocity, reducedMeridianVelocity,
      reducedRadialVelocity, reducedAxialVelocity, meridianFlux,
      advectiveDerivative, reducedVorticitySource,
      axisExtendedRadialFourAxialLaplacian,
      radialFourAxialLaplacian]
  · simp [axisExtendedReducedStreamFunctionProfileResidual,
      zeroReducedProfile, axisExtendedRadialFourAxialLaplacian,
      radialFourAxialLaplacian]

end

end AxisymmetricFlow
