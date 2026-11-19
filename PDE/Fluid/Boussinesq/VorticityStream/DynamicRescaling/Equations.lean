/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.VorticityStream.DynamicRescaling.Basic
import PDE.FDeriv.Calculus
import PDE.Fluid.Boussinesq.VorticityStream.DynamicRescaling.Calculus

/-!
# Equation transport under dynamic Boussinesq rescaling

The two-dimensional inviscid Boussinesq equations in vorticity–streamfunction form are

```text
∂ₜω + u·∇ω = ∂ₓθ,    ∂ₜθ + u·∇θ = 0,    u = ∇⊥ψ,    -Δψ = ω.
```

With the dynamically rescaled fields of `DynamicRescaling.Basic` (amplitudes `Cω`, `Cθ`,
`Cω / Cl²`, similarity point `Cl x`, clock `t(τ)`) and the scale ODEs `Cω' = cω Cω`,
`Cl' = -cl Cl`, `Cθ' = cθ Cθ`, the chain rules of `DynamicRescaling.Calculus` turn a pointwise
physical solution into a pointwise solution of the rescaled system of Chen and Hou
(Part I, (2.5) and (2.8))

```text
∂_τ ω̃ + (cl x + ũ)·∇ω̃ = cω ω̃ + ∂ₓθ̃,    ∂_τ θ̃ + (cl x + ũ)·∇θ̃ = cθ θ̃,
```

in which the dilation field `cl x` has been absorbed into the transport velocity. The buoyancy
term keeps its form only under the source-amplitude compatibility `Cθ Cl = Cω²`, which is taken
as a hypothesis. The residual identities hold in both directions; the forward implications are
their corollaries.

## Main results

* `rescaledVorticityResidual_dynamicallyRescaledFields`,
  `rescaledTemperatureResidual_dynamicallyRescaledFields`: the rescaled residuals are `Cω²` and
  `Cθ Cω` times the physical residuals at the similarity point, so the physical and the rescaled
  equations are equivalent at corresponding points.
* `vorticityEquation_dynamicallyRescaledFields`: the physical vorticity equation at the
  similarity point implies the rescaled vorticity equation at `x`.
* `temperatureEquation_dynamicallyRescaledFields`: the same for the temperature equation.
* `zeroStreamFunctionBoundary_dynamicallyRescaledFields`: a vanishing streamfunction trace on the
  boundary of the half-plane is preserved.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 2.1, (2.4)-(2.8).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

open PDE (advectiveDerivative)

namespace Boussinesq

open IncompressibleFlow
open PDE.Representations.Similarity

set_option linter.missingDocs true

noncomputable section

/-- The rescaled vorticity residual of the dynamically rescaled fields is `Cω²` times the
physical vorticity residual `∂ₜω + u·∇ω - ∂ₓθ` at the similarity point and physical time. The
buoyancy term needs the source compatibility `Cθ Cl = Cω²`. -/
theorem rescaledVorticityResidual_dynamicallyRescaledFields
    (data : DynamicRescalingData)
    (fields : VorticityStreamFields) (x : ℝ^2) (τ : ℝ)
    (hlaws : SatisfiesDynamicScaleODEsAt data τ)
    (hspatialScale : data.spatialScale τ ≠ 0)
    (hsourceScale :
      data.temperatureScale τ * data.spatialScale τ =
        data.vorticityScale τ ^ 2)
    (hvorticityJoint : DifferentiableAt ℝ
      (Function.uncurry fields.vorticity)
      (dynamicSimilarityPoint data x τ, data.physicalTime τ))
    (htemperatureSpatial : DifferentiableAt ℝ
      (fun y ↦ fields.temperature y (data.physicalTime τ))
      (dynamicSimilarityPoint data x τ))
    (hstream : ContDiff ℝ 1
      (fun y ↦ fields.streamFunction y (data.physicalTime τ))) :
    rescaledVorticityResidual (dynamicallyRescaledFields data fields)
        data.spatialRate data.vorticityRate x τ =
      data.vorticityScale τ ^ 2 *
        (deriv
            (fields.vorticity (dynamicSimilarityPoint data x τ))
            (data.physicalTime τ) +
          advectiveDerivative
            (fun y ↦ vorticityStreamVelocity fields y (data.physicalTime τ))
            (fun y ↦ fields.vorticity y (data.physicalTime τ))
            (dynamicSimilarityPoint data x τ) -
          (∂[(0 : Fin 2)]
            (fun y ↦ fields.temperature y (data.physicalTime τ)))
            (dynamicSimilarityPoint data x τ)) := by
  have hvorticitySpatial : DifferentiableAt ℝ
      (fun y ↦ fields.vorticity y (data.physicalTime τ))
      (dynamicSimilarityPoint data x τ) := by
    have hslice : DifferentiableAt ℝ
        (fun y : ℝ^2 ↦ (y, data.physicalTime τ))
        (dynamicSimilarityPoint data x τ) := by fun_prop
    convert! hvorticityJoint.comp (dynamicSimilarityPoint data x τ) hslice using 1
  unfold rescaledVorticityResidual
  rw [show
      (fun y ↦ rescaledTransportVelocity
        (dynamicallyRescaledFields data fields)
        data.spatialRate y τ) =
        fun y ↦
          (fun z ↦ data.spatialRate τ • z) y +
            (fun z ↦ vorticityStreamVelocity
              (dynamicallyRescaledFields data fields) z τ) y by
    rfl]
  rw [PDE.advectiveDerivative_add_advecting]
  change
    deriv (fun s ↦ rescaledVorticity data fields x s) τ +
          (advectiveDerivative
              (fun y ↦ data.spatialRate τ • y)
              (fun y ↦ rescaledVorticity data fields y τ) x +
            advectiveDerivative
              (fun y ↦ vorticityStreamVelocity
                (dynamicallyRescaledFields data fields) y τ)
              (fun y ↦ rescaledVorticity data fields y τ) x) -
      (data.vorticityRate τ * rescaledVorticity data fields x τ +
        (∂[(0 : Fin 2)]
          (fun y ↦ rescaledTemperature data fields y τ)) x) = _
  rw [deriv_rescaledVorticity data fields x τ hlaws hvorticityJoint]
  rw [dilationAdvection_rescaledVorticity
    data fields x τ hvorticitySpatial]
  rw [velocityAdvection_rescaledVorticity
    data fields x τ hspatialScale
    hstream hvorticitySpatial]
  rw [partialDeriv_rescaledTemperature
    data fields (0 : Fin 2) x τ htemperatureSpatial]
  unfold rescaledVorticity dynamicPullback
  rw [hsourceScale]
  simp only [dynamicSimilarityPoint]
  ring

/-- The rescaled temperature residual of the dynamically rescaled fields is `Cθ Cω` times the
physical temperature residual `∂ₜθ + u·∇θ` at the similarity point and physical time. -/
theorem rescaledTemperatureResidual_dynamicallyRescaledFields
    (data : DynamicRescalingData)
    (fields : VorticityStreamFields) (x : ℝ^2) (τ : ℝ)
    (hlaws : SatisfiesDynamicScaleODEsAt data τ)
    (hspatialScale : data.spatialScale τ ≠ 0)
    (htemperatureJoint : DifferentiableAt ℝ
      (Function.uncurry fields.temperature)
      (dynamicSimilarityPoint data x τ, data.physicalTime τ))
    (hstream : ContDiff ℝ 1
      (fun y ↦ fields.streamFunction y (data.physicalTime τ))) :
    rescaledTemperatureResidual (dynamicallyRescaledFields data fields)
        data.spatialRate data.temperatureRate x τ =
      data.temperatureScale τ * data.vorticityScale τ *
        (deriv
            (fields.temperature (dynamicSimilarityPoint data x τ))
            (data.physicalTime τ) +
          advectiveDerivative
            (fun y ↦ vorticityStreamVelocity fields y (data.physicalTime τ))
            (fun y ↦ fields.temperature y (data.physicalTime τ))
            (dynamicSimilarityPoint data x τ)) := by
  have htemperatureSpatial : DifferentiableAt ℝ
      (fun y ↦ fields.temperature y (data.physicalTime τ))
      (dynamicSimilarityPoint data x τ) := by
    have hslice : DifferentiableAt ℝ
        (fun y : ℝ^2 ↦ (y, data.physicalTime τ))
        (dynamicSimilarityPoint data x τ) := by fun_prop
    convert! htemperatureJoint.comp (dynamicSimilarityPoint data x τ) hslice using 1
  unfold rescaledTemperatureResidual
  rw [show
      (fun y ↦ rescaledTransportVelocity
        (dynamicallyRescaledFields data fields)
        data.spatialRate y τ) =
        fun y ↦
          (fun z ↦ data.spatialRate τ • z) y +
            (fun z ↦ vorticityStreamVelocity
              (dynamicallyRescaledFields data fields) z τ) y by
    rfl]
  rw [PDE.advectiveDerivative_add_advecting]
  change
    deriv (fun s ↦ rescaledTemperature data fields x s) τ +
          (advectiveDerivative
              (fun y ↦ data.spatialRate τ • y)
              (fun y ↦ rescaledTemperature data fields y τ) x +
            advectiveDerivative
              (fun y ↦ vorticityStreamVelocity
                (dynamicallyRescaledFields data fields) y τ)
              (fun y ↦ rescaledTemperature data fields y τ) x) -
      data.temperatureRate τ * rescaledTemperature data fields x τ = _
  rw [deriv_rescaledTemperature
    data fields x τ hlaws htemperatureJoint]
  rw [dilationAdvection_rescaledTemperature
    data fields x τ htemperatureSpatial]
  rw [velocityAdvection_rescaledTemperature
    data fields x τ hspatialScale
    hstream htemperatureSpatial]
  unfold rescaledTemperature dynamicPullback
  simp only [dynamicSimilarityPoint]
  ring

/-- The physical vorticity equation transforms into Chen–Hou's dynamically
rescaled vorticity equation at a point. -/
theorem vorticityEquation_dynamicallyRescaledFields
    (data : DynamicRescalingData)
    (fields : VorticityStreamFields) (x : ℝ^2) (τ : ℝ)
    (hlaws : SatisfiesDynamicScaleODEsAt data τ)
    (hspatialScale : data.spatialScale τ ≠ 0)
    (hsourceScale :
      data.temperatureScale τ * data.spatialScale τ =
        data.vorticityScale τ ^ 2)
    (hvorticityJoint : DifferentiableAt ℝ
      (Function.uncurry fields.vorticity)
      (dynamicSimilarityPoint data x τ, data.physicalTime τ))
    (htemperatureSpatial : DifferentiableAt ℝ
      (fun y ↦ fields.temperature y (data.physicalTime τ))
      (dynamicSimilarityPoint data x τ))
    (hstream : ContDiff ℝ 1
      (fun y ↦ fields.streamFunction y (data.physicalTime τ)))
    (hphysical :
      deriv
          (fields.vorticity (dynamicSimilarityPoint data x τ))
          (data.physicalTime τ) +
        advectiveDerivative
          (fun y ↦ vorticityStreamVelocity fields y (data.physicalTime τ))
          (fun y ↦ fields.vorticity y (data.physicalTime τ))
          (dynamicSimilarityPoint data x τ) =
        (∂[(0 : Fin 2)]
          (fun y ↦ fields.temperature y (data.physicalTime τ)))
          (dynamicSimilarityPoint data x τ)) :
    deriv
          (fun s ↦
            (dynamicallyRescaledFields data fields).vorticity x s) τ +
        advectiveDerivative
          (fun y ↦ rescaledTransportVelocity
            (dynamicallyRescaledFields data fields)
            data.spatialRate y τ)
          (fun y ↦
            (dynamicallyRescaledFields data fields).vorticity y τ) x =
      data.vorticityRate τ *
          (dynamicallyRescaledFields data fields).vorticity x τ +
        (∂[(0 : Fin 2)]
          (fun y ↦
            (dynamicallyRescaledFields data fields).temperature y τ)) x := by
  have h := rescaledVorticityResidual_dynamicallyRescaledFields data fields x τ hlaws
    hspatialScale hsourceScale hvorticityJoint htemperatureSpatial hstream
  rw [hphysical, sub_self, mul_zero] at h
  unfold rescaledVorticityResidual at h
  linarith

/-- The physical temperature equation transforms into the dynamically
rescaled temperature equation at a point. -/
theorem temperatureEquation_dynamicallyRescaledFields
    (data : DynamicRescalingData)
    (fields : VorticityStreamFields) (x : ℝ^2) (τ : ℝ)
    (hlaws : SatisfiesDynamicScaleODEsAt data τ)
    (hspatialScale : data.spatialScale τ ≠ 0)
    (htemperatureJoint : DifferentiableAt ℝ
      (Function.uncurry fields.temperature)
      (dynamicSimilarityPoint data x τ, data.physicalTime τ))
    (hstream : ContDiff ℝ 1
      (fun y ↦ fields.streamFunction y (data.physicalTime τ)))
    (hphysical :
      deriv
          (fields.temperature (dynamicSimilarityPoint data x τ))
          (data.physicalTime τ) +
        advectiveDerivative
          (fun y ↦ vorticityStreamVelocity fields y (data.physicalTime τ))
          (fun y ↦ fields.temperature y (data.physicalTime τ))
          (dynamicSimilarityPoint data x τ) = 0) :
    deriv
          (fun s ↦
            (dynamicallyRescaledFields data fields).temperature x s) τ +
        advectiveDerivative
          (fun y ↦ rescaledTransportVelocity
            (dynamicallyRescaledFields data fields)
            data.spatialRate y τ)
          (fun y ↦
            (dynamicallyRescaledFields data fields).temperature y τ) x =
      data.temperatureRate τ *
        (dynamicallyRescaledFields data fields).temperature x τ := by
  have h := rescaledTemperatureResidual_dynamicallyRescaledFields data fields x τ hlaws
    hspatialScale htemperatureJoint hstream
  rw [hphysical, mul_zero] at h
  unfold rescaledTemperatureResidual at h
  linarith

/-- A zero streamfunction boundary trace is preserved by dynamic rescaling. -/
theorem zeroStreamFunctionBoundary_dynamicallyRescaledFields
    (data : DynamicRescalingData)
    (fields : VorticityStreamFields) (x₁ τ : ℝ)
    (hboundary :
      fields.streamFunction
        (horizontalBoundaryPoint (data.spatialScale τ * x₁))
        (data.physicalTime τ) = 0) :
    (dynamicallyRescaledFields data fields).streamFunction
      (horizontalBoundaryPoint x₁) τ = 0 := by
  change
    (data.vorticityScale τ / data.spatialScale τ ^ 2) *
      fields.streamFunction
        (data.spatialScale τ • horizontalBoundaryPoint x₁)
        (data.physicalTime τ) = 0
  rw [show
      data.spatialScale τ • horizontalBoundaryPoint x₁ =
        horizontalBoundaryPoint (data.spatialScale τ * x₁) by
    ext i
    fin_cases i <;> simp [smul_eq_mul]]
  rw [hboundary, mul_zero]

end

end Boussinesq
