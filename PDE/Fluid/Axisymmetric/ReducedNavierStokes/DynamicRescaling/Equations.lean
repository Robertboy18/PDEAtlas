/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Axisymmetric.ReducedNavierStokes.DynamicRescaling.Basic
import PDE.Fluid.Axisymmetric.ReducedNavierStokes.DynamicRescaling.Calculus

/-!
# Equation transport under dynamic axisymmetric rescaling

The chain rules of `DynamicRescaling.Calculus` and the scale compatibility laws combine into
exact residual identities. If

```text
Aω = AL,        dt/dτ = A,        ν̃ = νA/L²,
cω = cᵤ - λ,
```

then the dynamically rescaled residuals satisfy

```text
R̃ᵤ = A² Rᵤ,       R̃ω = A Aω Rω,       R̃ψ = Aω Rψ.
```

Both the ordinary positive-radius equations and their explicit smooth-axis
continuations are covered. Domain-level theorems then transport a physical
reduced Euler/Navier–Stokes solution to the corresponding dynamically
rescaled system.

The identities are exact: the rescaled residual is the physical residual, evaluated at the
physical point `Lx + Ze_z` and physical time `t(τ)`, multiplied by the indicated amplitude. At a
point where `A` and `L` are positive the two residuals therefore vanish together; the transport
theorems below record the direction from a physical solution to a rescaled one.

## Main results

* `HasDynamicReducedRegularityAt`: the pointwise joint differentiability and spatial `C²`
  regularity needed to apply the chain rules of `Calculus`.
* `rescaledReducedSwirlResidual_dynamicallyRescaledReducedFields`,
  `rescaledReducedVorticityResidual_dynamicallyRescaledReducedFields`: the off-axis identities
  `R̃ᵤ = A² Rᵤ` and `R̃ω = A Aω Rω`.
* `axisExtendedRescaledReducedSwirlResidual_dynamicallyRescaledReducedFields`,
  `axisExtendedRescaledReducedVorticityResidual_dynamicallyRescaledReducedFields`: the same
  identities for the axis-extended residuals, valid on the axis as well.
* `satisfiesDynamicRescaledReducedSystemOn_of_satisfiesReducedSystemOn`,
  `satisfiesAxisExtendedRescaledResidualSystemOn_of_satisfiesAxisExtendedResidualSystemOn`:
  a physical reduced solution on a domain transports to a dynamically rescaled solution on any
  rescaled domain mapped into it.

For the origin of the dynamic rescaling formulation see the references in `Basic`.
-/

@[expose] public section

namespace AxisymmetricFlow

set_option linter.missingDocs true

noncomputable section

/-- Pointwise regularity sufficient for transporting all three reduced
equations through the dynamic affine change of variables. -/
structure HasDynamicReducedRegularityAt
    (data : DynamicRescalingData) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ) : Prop where
  /-- Joint differentiability of reduced swirl. -/
  swirl_joint_differentiableAt :
    DifferentiableAt ℝ (Function.uncurry fields.swirl)
      (dynamicReducedSimilarityPoint data x τ, data.physicalTime τ)
  /-- Joint differentiability of reduced vorticity. -/
  vorticity_joint_differentiableAt :
    DifferentiableAt ℝ (Function.uncurry fields.vorticity)
      (dynamicReducedSimilarityPoint data x τ, data.physicalTime τ)
  /-- Spatial `C²` regularity of the physical swirl slice. -/
  swirl_spatial_contDiff :
    ContDiff ℝ 2 (fun y ↦ fields.swirl y (data.physicalTime τ))
  /-- Spatial `C²` regularity of the physical vorticity slice. -/
  vorticity_spatial_contDiff :
    ContDiff ℝ 2 (fun y ↦ fields.vorticity y (data.physicalTime τ))
  /-- Spatial `C²` regularity of the physical streamfunction slice. -/
  streamFunction_spatial_contDiff :
    ContDiff ℝ 2 (fun y ↦ fields.streamFunction y (data.physicalTime τ))

/-- Spatial differentiability of swirl follows from dynamic pointwise
regularity. -/
theorem HasDynamicReducedRegularityAt.swirl_spatial_differentiableAt
    {data : DynamicRescalingData} {fields : ReducedFields}
    {x : ℝ^2} {τ : ℝ}
    (hreg : HasDynamicReducedRegularityAt data fields x τ) :
    DifferentiableAt ℝ
      (fun y ↦ fields.swirl y (data.physicalTime τ))
      (dynamicReducedSimilarityPoint data x τ) :=
  (hreg.swirl_spatial_contDiff.differentiable
    (by norm_num)).differentiableAt

/-- Spatial differentiability of vorticity follows from dynamic pointwise
regularity. -/
theorem HasDynamicReducedRegularityAt.vorticity_spatial_differentiableAt
    {data : DynamicRescalingData} {fields : ReducedFields}
    {x : ℝ^2} {τ : ℝ}
    (hreg : HasDynamicReducedRegularityAt data fields x τ) :
    DifferentiableAt ℝ
      (fun y ↦ fields.vorticity y (data.physicalTime τ))
      (dynamicReducedSimilarityPoint data x τ) :=
  (hreg.vorticity_spatial_contDiff.differentiable
    (by norm_num)).differentiableAt

/-- Spatial differentiability of the streamfunction follows from dynamic
pointwise regularity. -/
theorem HasDynamicReducedRegularityAt.streamFunction_spatial_differentiableAt
    {data : DynamicRescalingData} {fields : ReducedFields}
    {x : ℝ^2} {τ : ℝ}
    (hreg : HasDynamicReducedRegularityAt data fields x τ) :
    DifferentiableAt ℝ
      (fun y ↦ fields.streamFunction y (data.physicalTime τ))
      (dynamicReducedSimilarityPoint data x τ) :=
  (hreg.streamFunction_spatial_contDiff.differentiable
    (by norm_num)).differentiableAt

/-- Off the axis, the dynamically rescaled swirl residual is `A²` times the
physical reduced swirl residual. -/
theorem rescaledReducedSwirlResidual_dynamicallyRescaledReducedFields
    (physicalViscosity : ℝ)
    (data : DynamicRescalingData) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hreg : HasDynamicReducedRegularityAt data fields x τ)
    (hlaws :
      SatisfiesDynamicRescalingLawsAt data physicalViscosity τ)
    (hr : x (0 : Fin 2) ≠ 0) :
    rescaledReducedSwirlResidual
        (dynamicallyRescaledReducedFields data fields)
        data.rescaledViscosity data.spatialRate data.axialDrift
        data.swirlRate x τ =
      data.swirlScale τ ^ 2 *
        reducedSwirlResidual physicalViscosity fields
          (dynamicReducedSimilarityPoint data x τ)
          (data.physicalTime τ) := by
  unfold rescaledReducedSwirlResidual reducedSwirlResidual
  change
    deriv (fun s ↦ dynamicallyRescaledSwirl data fields x s) τ +
        rescaledReducedAdvection
          (dynamicallyRescaledReducedFields data fields)
          data.spatialRate data.axialDrift
          (fun y ↦ dynamicallyRescaledSwirl data fields y τ) x τ -
      (reducedSwirlSource
          (dynamicallyRescaledReducedFields data fields) x τ +
        data.swirlRate τ * dynamicallyRescaledSwirl data fields x τ +
        data.rescaledViscosity τ *
          radialFourAxialLaplacian
            (fun y ↦ dynamicallyRescaledSwirl data fields y τ) x) =
      _
  rw [deriv_add_rescaledReducedAdvection_dynamicallyRescaledSwirl
    data fields x τ hlaws.spatialScale_pos.ne'
    hreg.swirl_joint_differentiableAt
   
    hreg.streamFunction_spatial_differentiableAt hlaws.toSatisfiesDynamicScaleODEsAt]
  rw [reducedSwirlSource_dynamicallyRescaledReducedFields
    data fields x τ hlaws.spatialScale_pos.ne'
    hreg.streamFunction_spatial_differentiableAt]
  rw [radialFourAxialLaplacian_dynamicallyRescaledSwirl
    data fields x τ hreg.swirl_spatial_contDiff
    hlaws.spatialScale_pos.ne' hr]
  rw [hlaws.rescaledViscosity_eq]
  field_simp [hlaws.spatialScale_pos.ne']
  ring

/-- Off the axis, the dynamically rescaled vorticity residual is `A Aω`
times the physical reduced vorticity residual. -/
theorem rescaledReducedVorticityResidual_dynamicallyRescaledReducedFields
    (physicalViscosity : ℝ)
    (data : DynamicRescalingData) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hreg : HasDynamicReducedRegularityAt data fields x τ)
    (hlaws :
      SatisfiesDynamicRescalingLawsAt data physicalViscosity τ)
    (hr : x (0 : Fin 2) ≠ 0) :
    rescaledReducedVorticityResidual
        (dynamicallyRescaledReducedFields data fields)
        data.rescaledViscosity data.spatialRate data.axialDrift
        data.vorticityRate x τ =
      (data.swirlScale τ * data.vorticityScale τ) *
        reducedVorticityResidual physicalViscosity fields
          (dynamicReducedSimilarityPoint data x τ)
          (data.physicalTime τ) := by
  unfold rescaledReducedVorticityResidual reducedVorticityResidual
  change
    deriv (fun s ↦ dynamicallyRescaledVorticity data fields x s) τ +
        rescaledReducedAdvection
          (dynamicallyRescaledReducedFields data fields)
          data.spatialRate data.axialDrift
          (fun y ↦ dynamicallyRescaledVorticity data fields y τ) x τ -
      (reducedVorticitySource
          (dynamicallyRescaledReducedFields data fields) x τ +
        data.vorticityRate τ *
          dynamicallyRescaledVorticity data fields x τ +
        data.rescaledViscosity τ *
          radialFourAxialLaplacian
            (fun y ↦ dynamicallyRescaledVorticity data fields y τ) x) =
      _
  rw [deriv_add_rescaledReducedAdvection_dynamicallyRescaledVorticity
    data fields x τ hlaws.spatialScale_pos.ne'
    hreg.vorticity_joint_differentiableAt
   
    hreg.streamFunction_spatial_differentiableAt hlaws.toSatisfiesDynamicScaleODEsAt]
  rw [reducedVorticitySource_dynamicallyRescaledReducedFields_compatible
    data fields x τ hlaws.vorticityScale_eq
    hreg.swirl_spatial_differentiableAt]
  rw [radialFourAxialLaplacian_dynamicallyRescaledVorticity
    data fields x τ hreg.vorticity_spatial_contDiff
    hlaws.spatialScale_pos.ne' hr]
  rw [hlaws.rescaledViscosity_eq]
  field_simp [hlaws.spatialScale_pos.ne']
  ring

/-- Including on the axis, the axis-extended dynamically rescaled swirl
residual is `A²` times the physical axis-extended swirl residual. -/
theorem axisExtendedRescaledReducedSwirlResidual_dynamicallyRescaledReducedFields
    (physicalViscosity : ℝ)
    (data : DynamicRescalingData) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hreg : HasDynamicReducedRegularityAt data fields x τ)
    (hlaws :
      SatisfiesDynamicRescalingLawsAt data physicalViscosity τ) :
    axisExtendedRescaledReducedSwirlResidual
        (dynamicallyRescaledReducedFields data fields)
        data.rescaledViscosity data.spatialRate data.axialDrift
        data.swirlRate x τ =
      data.swirlScale τ ^ 2 *
        axisExtendedReducedSwirlResidual physicalViscosity fields
          (dynamicReducedSimilarityPoint data x τ)
          (data.physicalTime τ) := by
  unfold axisExtendedRescaledReducedSwirlResidual
    axisExtendedReducedSwirlResidual
  change
    deriv (fun s ↦ dynamicallyRescaledSwirl data fields x s) τ +
        rescaledReducedAdvection
          (dynamicallyRescaledReducedFields data fields)
          data.spatialRate data.axialDrift
          (fun y ↦ dynamicallyRescaledSwirl data fields y τ) x τ -
      (reducedSwirlSource
          (dynamicallyRescaledReducedFields data fields) x τ +
        data.swirlRate τ * dynamicallyRescaledSwirl data fields x τ +
        data.rescaledViscosity τ *
          axisExtendedRadialFourAxialLaplacian
            (fun y ↦ dynamicallyRescaledSwirl data fields y τ) x) =
      _
  rw [deriv_add_rescaledReducedAdvection_dynamicallyRescaledSwirl
    data fields x τ hlaws.spatialScale_pos.ne'
    hreg.swirl_joint_differentiableAt
   
    hreg.streamFunction_spatial_differentiableAt hlaws.toSatisfiesDynamicScaleODEsAt]
  rw [reducedSwirlSource_dynamicallyRescaledReducedFields
    data fields x τ hlaws.spatialScale_pos.ne'
    hreg.streamFunction_spatial_differentiableAt]
  rw [axisExtendedRadialFourAxialLaplacian_dynamicallyRescaledSwirl
    data fields x τ hreg.swirl_spatial_contDiff
    hlaws.spatialScale_pos.ne']
  rw [hlaws.rescaledViscosity_eq]
  field_simp [hlaws.spatialScale_pos.ne']
  ring

/-- Including on the axis, the axis-extended dynamically rescaled vorticity
residual is `A Aω` times the physical axis-extended vorticity residual. -/
theorem axisExtendedRescaledReducedVorticityResidual_dynamicallyRescaledReducedFields
    (physicalViscosity : ℝ)
    (data : DynamicRescalingData) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hreg : HasDynamicReducedRegularityAt data fields x τ)
    (hlaws :
      SatisfiesDynamicRescalingLawsAt data physicalViscosity τ) :
    axisExtendedRescaledReducedVorticityResidual
        (dynamicallyRescaledReducedFields data fields)
        data.rescaledViscosity data.spatialRate data.axialDrift
        data.vorticityRate x τ =
      (data.swirlScale τ * data.vorticityScale τ) *
        axisExtendedReducedVorticityResidual physicalViscosity fields
          (dynamicReducedSimilarityPoint data x τ)
          (data.physicalTime τ) := by
  unfold axisExtendedRescaledReducedVorticityResidual
    axisExtendedReducedVorticityResidual
  change
    deriv (fun s ↦ dynamicallyRescaledVorticity data fields x s) τ +
        rescaledReducedAdvection
          (dynamicallyRescaledReducedFields data fields)
          data.spatialRate data.axialDrift
          (fun y ↦ dynamicallyRescaledVorticity data fields y τ) x τ -
      (reducedVorticitySource
          (dynamicallyRescaledReducedFields data fields) x τ +
        data.vorticityRate τ *
          dynamicallyRescaledVorticity data fields x τ +
        data.rescaledViscosity τ *
          axisExtendedRadialFourAxialLaplacian
            (fun y ↦ dynamicallyRescaledVorticity data fields y τ) x) =
      _
  rw [deriv_add_rescaledReducedAdvection_dynamicallyRescaledVorticity
    data fields x τ hlaws.spatialScale_pos.ne'
    hreg.vorticity_joint_differentiableAt
   
    hreg.streamFunction_spatial_differentiableAt hlaws.toSatisfiesDynamicScaleODEsAt]
  rw [reducedVorticitySource_dynamicallyRescaledReducedFields_compatible
    data fields x τ hlaws.vorticityScale_eq
    hreg.swirl_spatial_differentiableAt]
  rw [axisExtendedRadialFourAxialLaplacian_dynamicallyRescaledVorticity
    data fields x τ hreg.vorticity_spatial_contDiff
    hlaws.spatialScale_pos.ne']
  rw [hlaws.rescaledViscosity_eq]
  field_simp [hlaws.spatialScale_pos.ne']
  ring

/-- A physical off-axis reduced system transports to the dynamically
rescaled system on any domain mapped into the physical domain. -/
theorem satisfiesDynamicRescaledReducedSystemOn_of_satisfiesReducedSystemOn
    (physicalViscosity : ℝ)
    (data : DynamicRescalingData) (fields : ReducedFields)
    (physicalDomain rescaledDomain : Set (ℝ^2))
    (physicalTimes rescaledTimes : Set ℝ)
    (hphysical :
      SatisfiesReducedSystemOn physicalViscosity fields
        physicalDomain physicalTimes)
    (hdomain : rescaledDomain ⊆ positiveRadiusMeridian)
    (hmap :
      ∀ ⦃x : ℝ^2⦄ ⦃τ : ℝ⦄,
        x ∈ rescaledDomain → τ ∈ rescaledTimes →
          dynamicReducedSimilarityPoint data x τ ∈ physicalDomain ∧
            data.physicalTime τ ∈ physicalTimes)
    (hlaws :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        SatisfiesDynamicRescalingLawsAt data physicalViscosity τ)
    (hregularity :
      ∀ ⦃x : ℝ^2⦄ ⦃τ : ℝ⦄,
        x ∈ rescaledDomain → τ ∈ rescaledTimes →
          HasDynamicReducedRegularityAt data fields x τ) :
    SatisfiesRescaledReducedSystemOn
      (dynamicallyRescaledReducedFields data fields)
      data.rescaledViscosity data.spatialRate data.axialDrift
      data.swirlRate data.vorticityRate rescaledDomain rescaledTimes := by
  rcases hphysical with ⟨hswirl, hvorticity, hstream⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x τ hx hτ
    have hmapped := hmap hx hτ
    have hrescaled := rescaledReducedSwirlResidual_dynamicallyRescaledReducedFields
      physicalViscosity data fields x τ (hregularity hx hτ) (hlaws hτ)
      (ne_of_gt (hdomain hx))
    rw [hrescaled, hswirl hmapped.1 hmapped.2]
    ring
  · intro x τ hx hτ
    have hmapped := hmap hx hτ
    have hrescaled :=
      rescaledReducedVorticityResidual_dynamicallyRescaledReducedFields
        physicalViscosity data fields x τ (hregularity hx hτ) (hlaws hτ)
        (ne_of_gt (hdomain hx))
    rw [hrescaled, hvorticity hmapped.1 hmapped.2]
    ring
  · intro x τ hx hτ
    have hmapped := hmap hx hτ
    have hreg := hregularity hx hτ
    have hscale := (hlaws hτ).spatialScale_pos.ne'
    have hrescaled :=
      reducedStreamFunctionResidual_dynamicallyRescaledReducedFields
        data fields x τ hreg.streamFunction_spatial_contDiff hscale
        (hlaws hτ).vorticityScale_eq (ne_of_gt (hdomain hx))
    rw [hrescaled, hstream hmapped.1 hmapped.2]
    ring

/-- An algebraically axis-extended physical residual system transports to the corresponding
dynamically rescaled residual system on any mapped domain. -/
theorem satisfiesAxisExtendedRescaledResidualSystemOn_of_satisfiesAxisExtendedResidualSystemOn
    (physicalViscosity : ℝ)
    (data : DynamicRescalingData) (fields : ReducedFields)
    (physicalDomain rescaledDomain : Set (ℝ^2))
    (physicalTimes rescaledTimes : Set ℝ)
    (hphysical :
      SatisfiesAxisExtendedResidualSystemOn physicalViscosity fields
        physicalDomain physicalTimes)
    (hmap :
      ∀ ⦃x : ℝ^2⦄ ⦃τ : ℝ⦄,
        x ∈ rescaledDomain → τ ∈ rescaledTimes →
          dynamicReducedSimilarityPoint data x τ ∈ physicalDomain ∧
            data.physicalTime τ ∈ physicalTimes)
    (hlaws :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        SatisfiesDynamicRescalingLawsAt data physicalViscosity τ)
    (hregularity :
      ∀ ⦃x : ℝ^2⦄ ⦃τ : ℝ⦄,
        x ∈ rescaledDomain → τ ∈ rescaledTimes →
          HasDynamicReducedRegularityAt data fields x τ) :
    SatisfiesAxisExtendedRescaledResidualSystemOn
      (dynamicallyRescaledReducedFields data fields)
      data.rescaledViscosity data.spatialRate data.axialDrift
      data.swirlRate data.vorticityRate rescaledDomain rescaledTimes := by
  rcases hphysical with ⟨hswirl, hvorticity, hstream⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x τ hx hτ
    have hmapped := hmap hx hτ
    have hrescaled :=
      axisExtendedRescaledReducedSwirlResidual_dynamicallyRescaledReducedFields
        physicalViscosity data fields x τ (hregularity hx hτ) (hlaws hτ)
    rw [hrescaled, hswirl hmapped.1 hmapped.2]
    ring
  · intro x τ hx hτ
    have hmapped := hmap hx hτ
    have hrescaled :=
      axisExtendedRescaledReducedVorticityResidual_dynamicallyRescaledReducedFields
        physicalViscosity data fields x τ (hregularity hx hτ) (hlaws hτ)
    rw [hrescaled, hvorticity hmapped.1 hmapped.2]
    ring
  · intro x τ hx hτ
    have hmapped := hmap hx hτ
    have hreg := hregularity hx hτ
    have hrescaled :=
      axisExtendedReducedStreamFunctionResidual_dynamicallyRescaledReducedFields
        data fields x τ hreg.streamFunction_spatial_contDiff
        (hlaws hτ).spatialScale_pos.ne' (hlaws hτ).vorticityScale_eq
    rw [hrescaled, hstream hmapped.1 hmapped.2]
    ring

end

end AxisymmetricFlow
