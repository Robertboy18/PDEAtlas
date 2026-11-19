/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.VorticityStream.DynamicRescaling.Basic
import PDE.Representations.Similarity.Calculus
import PDE.FDeriv.Laplacian.Congruence
import PDE.FDeriv.Calculus
import PDE.Analysis.Calculus.LocalExtension

/-!
# Calculus for dynamic Boussinesq rescaling

The dynamically rescaled vorticity–streamfunction Boussinesq fields of `DynamicRescaling.Basic`
are the physical fields evaluated at the similarity point `Cl(τ) x` and physical time `t(τ)`,
multiplied by the amplitudes `Cω` (vorticity), `Cθ` (temperature) and `Cω / Cl²`
(streamfunction). By the chain rule, each spatial derivative in the rescaled variables
contributes one factor of `Cl`, the reconstructed velocity `ũ = ∇⊥ψ̃` has amplitude `Cω / Cl`,
and the rescaled time derivative of a field with amplitude `C` and rate `c = C'/C` is
`C · (dt/dτ) · ∂ₜ(·) + c · (rescaled field)` plus the dilation term
produced by the moving spatial scale.

## Main results

* `vorticityStreamVelocity_dynamicallyRescaledFields`: the velocity of the rescaled fields is
  `(Cω / Cl)` times the physical velocity at the similarity point.
* `streamFunctionEquation_dynamicallyRescaledFields`: the Poisson equation `-Δψ = ω` is
  preserved pointwise by the rescaling.
* `partialDeriv_rescaledVorticity`, `partialDeriv_rescaledTemperature`: spatial derivatives
  carry the amplitude and one factor of `Cl`.
* `laplacian_rescaledStreamFunction`: the Laplacian of the rescaled stream function is `Cω`
  times the physical Laplacian at the similarity point; only a `C²` germ there is needed.
* `deriv_rescaledVorticity`, `deriv_rescaledTemperature`: exact time derivatives of the
  rescaled fields under the scale ODEs.
* `dilationAdvection_*`, `velocityAdvection_*`: advection by the dilation field `cl x` and by the
  rescaled velocity; the latter carries the common factors `Cω²` (vorticity) and `Cω Cθ`
  (temperature), which are the factors of the corresponding time derivatives.

Every lemma is a chain-rule computation on explicitly differentiable functions; the residual
identities assembled from them are in `DynamicRescaling.Equations`. The dynamic rescaling
formulation is the one of Chen and Hou, Part I, Section 2.1.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 2.1, (2.4)-(2.6).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

open PDE (laplacian advectiveDerivative)

namespace Boussinesq

open IncompressibleFlow
open PDE.Representations.Similarity

set_option linter.missingDocs true

noncomputable section

/-- The rescaled streamfunction reconstructs the velocity scaling
`ũ = Cω Cl⁻¹ u`. -/
theorem vorticityStreamVelocity_dynamicallyRescaledFields
    (data : DynamicRescalingData)
    (fields : VorticityStreamFields) (x : ℝ^2) (τ : ℝ)
    (hstream : DifferentiableAt ℝ
      (fun y ↦ fields.streamFunction y (data.physicalTime τ))
      (dynamicSimilarityPoint data x τ)) :
    vorticityStreamVelocity (dynamicallyRescaledFields data fields) x τ =
      (data.vorticityScale τ / data.spatialScale τ) •
        vorticityStreamVelocity fields
          (dynamicSimilarityPoint data x τ) (data.physicalTime τ) := by
  change
    planarStreamVelocity
        (fun y ↦
          (data.vorticityScale τ / data.spatialScale τ ^ 2) *
            fields.streamFunction
              (data.spatialScale τ • y) (data.physicalTime τ)) x =
      _
  rw [planarStreamVelocity_const_smul_comp_smul
    (fun y ↦ fields.streamFunction y (data.physicalTime τ))
    (data.vorticityScale τ / data.spatialScale τ ^ 2)
    (data.spatialScale τ) x hstream]
  congr 1
  by_cases hscale : data.spatialScale τ = 0
  · simp [hscale]
  · field_simp

/-- Dynamic rescaling preserves the streamfunction equation at a point. -/
theorem streamFunctionEquation_dynamicallyRescaledFields
    (data : DynamicRescalingData)
    (fields : VorticityStreamFields) (x : ℝ^2) (τ : ℝ)
    (hscale : data.spatialScale τ ≠ 0)
    (hstream :
      -laplacian
          (fun y ↦ fields.streamFunction y (data.physicalTime τ))
          (dynamicSimilarityPoint data x τ) =
        fields.vorticity
          (dynamicSimilarityPoint data x τ) (data.physicalTime τ)) :
    -laplacian
        (fun y ↦
          (dynamicallyRescaledFields data fields).streamFunction y τ) x =
      (dynamicallyRescaledFields data fields).vorticity x τ := by
  change
    -laplacian
        (fun y ↦
          (data.vorticityScale τ / data.spatialScale τ ^ 2) *
            fields.streamFunction
              (data.spatialScale τ • y) (data.physicalTime τ)) x =
      data.vorticityScale τ *
        fields.vorticity
          (data.spatialScale τ • x) (data.physicalTime τ)
  rw [show
      (fun y ↦
        (data.vorticityScale τ / data.spatialScale τ ^ 2) *
          fields.streamFunction
            (data.spatialScale τ • y) (data.physicalTime τ)) =
        fun y ↦ scaledProfileAnsatz
          (fun z ↦ fields.streamFunction z (data.physicalTime τ))
          (fun _ ↦ data.vorticityScale τ / data.spatialScale τ ^ 2)
          (fun _ ↦ data.spatialScale τ) 0 y 0 by
    funext y
    simp [scaledProfileAnsatz, centeredDilation]]
  rw [laplacian_scaled_profile_ansatz
    (fun z ↦ fields.streamFunction z (data.physicalTime τ))
    (fun _ ↦ data.vorticityScale τ / data.spatialScale τ ^ 2)
    (fun _ ↦ data.spatialScale τ) 0 x 0]
  simp only [centeredDilation, sub_zero]
  change
    -(data.vorticityScale τ / data.spatialScale τ ^ 2 *
        data.spatialScale τ ^ 2 *
          laplacian
            (fun z ↦ fields.streamFunction z (data.physicalTime τ))
            (dynamicSimilarityPoint data x τ)) =
      _
  rw [show
      data.vorticityScale τ / data.spatialScale τ ^ 2 *
          data.spatialScale τ ^ 2 =
        data.vorticityScale τ by
    field_simp]
  calc
    -(data.vorticityScale τ *
          laplacian
            (fun z ↦ fields.streamFunction z (data.physicalTime τ))
            (data.spatialScale τ • x)) =
        data.vorticityScale τ *
          (-laplacian
            (fun z ↦ fields.streamFunction z (data.physicalTime τ))
            (data.spatialScale τ • x)) := by ring
    _ = _ := by
      rw [show
          -laplacian
              (fun z ↦ fields.streamFunction z (data.physicalTime τ))
              (data.spatialScale τ • x) =
            fields.vorticity
              (data.spatialScale τ • x) (data.physicalTime τ) by
        simpa [dynamicSimilarityPoint] using hstream]

/-- A spatial derivative of rescaled vorticity gains one spatial-scale
factor in addition to its amplitude factor. -/
theorem partialDeriv_rescaledVorticity
    (data : DynamicRescalingData)
    (fields : VorticityStreamFields) (i : Fin 2) (x : ℝ^2) (τ : ℝ)
    (hvorticity : DifferentiableAt ℝ
      (fun y ↦ fields.vorticity y (data.physicalTime τ))
      (dynamicSimilarityPoint data x τ)) :
    (∂[i]
        (fun y ↦ rescaledVorticity data fields y τ)) x =
      data.vorticityScale τ * data.spatialScale τ *
        (∂[i]
          (fun y ↦ fields.vorticity y (data.physicalTime τ)))
          (dynamicSimilarityPoint data x τ) := by
  have hgradient := congrArg
    (fun v : ℝ^2 ↦ v i)
    (gradient_scaled_profile_ansatz
      (fun y ↦ fields.vorticity y (data.physicalTime τ))
      (fun _ ↦ data.vorticityScale τ)
      (fun _ ↦ data.spatialScale τ) 0 x 0
      (by
        simpa [dynamicSimilarityPoint, centeredDilation] using
          hvorticity))
  simpa [rescaledVorticity, dynamicPullback, scaledProfileAnsatz,
    centeredDilation, dynamicSimilarityPoint,
    PDE.gradient_apply_eq_partialDeriv, smul_eq_mul] using hgradient

/-- A spatial derivative of rescaled temperature gains one spatial-scale
factor in addition to its amplitude factor. -/
theorem partialDeriv_rescaledTemperature
    (data : DynamicRescalingData)
    (fields : VorticityStreamFields) (i : Fin 2) (x : ℝ^2) (τ : ℝ)
    (htemperature : DifferentiableAt ℝ
      (fun y ↦ fields.temperature y (data.physicalTime τ))
      (dynamicSimilarityPoint data x τ)) :
    (∂[i]
        (fun y ↦ rescaledTemperature data fields y τ)) x =
      data.temperatureScale τ * data.spatialScale τ *
        (∂[i]
          (fun y ↦ fields.temperature y (data.physicalTime τ)))
          (dynamicSimilarityPoint data x τ) := by
  have hgradient := congrArg
    (fun v : ℝ^2 ↦ v i)
    (gradient_scaled_profile_ansatz
      (fun y ↦ fields.temperature y (data.physicalTime τ))
      (fun _ ↦ data.temperatureScale τ)
      (fun _ ↦ data.spatialScale τ) 0 x 0
      (by
        simpa [dynamicSimilarityPoint, centeredDilation] using
          htemperature))
  simpa [rescaledTemperature, dynamicPullback, scaledProfileAnsatz,
    centeredDilation, dynamicSimilarityPoint,
    PDE.gradient_apply_eq_partialDeriv, smul_eq_mul] using hgradient

/-- Exact time derivative of dynamically rescaled vorticity. -/
theorem deriv_rescaledVorticity
    (data : DynamicRescalingData)
    (fields : VorticityStreamFields) (x : ℝ^2) (τ : ℝ)
    (hlaws : SatisfiesDynamicScaleODEsAt data τ)
    (hvorticity : DifferentiableAt ℝ
      (Function.uncurry fields.vorticity)
      (dynamicSimilarityPoint data x τ, data.physicalTime τ)) :
    deriv (fun s ↦ rescaledVorticity data fields x s) τ =
      data.vorticityScale τ *
          ((-data.spatialRate τ * data.spatialScale τ) *
              fderiv ℝ
                (fun y ↦ fields.vorticity y (data.physicalTime τ))
                (dynamicSimilarityPoint data x τ) x +
            data.vorticityScale τ *
              deriv
                (fields.vorticity (dynamicSimilarityPoint data x τ))
                (data.physicalTime τ)) +
        data.vorticityRate τ * data.vorticityScale τ *
          fields.vorticity
            (dynamicSimilarityPoint data x τ) (data.physicalTime τ) := by
  simpa [rescaledVorticity, dynamicSimilarityPoint, smul_eq_mul] using
    (hasDerivAt_dynamicPullback_expanded fields.vorticity
      data.vorticityScale data.spatialScale data.physicalTime x τ
      (data.vorticityRate τ * data.vorticityScale τ)
      (-data.spatialRate τ * data.spatialScale τ)
      (data.vorticityScale τ) hvorticity
      hlaws.vorticityScale_hasDerivAt
      hlaws.spatialScale_hasDerivAt
      hlaws.physicalTime_hasDerivAt).deriv

/-- Exact time derivative of dynamically rescaled temperature. -/
theorem deriv_rescaledTemperature
    (data : DynamicRescalingData)
    (fields : VorticityStreamFields) (x : ℝ^2) (τ : ℝ)
    (hlaws : SatisfiesDynamicScaleODEsAt data τ)
    (htemperature : DifferentiableAt ℝ
      (Function.uncurry fields.temperature)
      (dynamicSimilarityPoint data x τ, data.physicalTime τ)) :
    deriv (fun s ↦ rescaledTemperature data fields x s) τ =
      data.temperatureScale τ *
          ((-data.spatialRate τ * data.spatialScale τ) *
              fderiv ℝ
                (fun y ↦ fields.temperature y (data.physicalTime τ))
                (dynamicSimilarityPoint data x τ) x +
            data.vorticityScale τ *
              deriv
                (fields.temperature (dynamicSimilarityPoint data x τ))
                (data.physicalTime τ)) +
        data.temperatureRate τ * data.temperatureScale τ *
          fields.temperature
            (dynamicSimilarityPoint data x τ) (data.physicalTime τ) := by
  simpa [rescaledTemperature, dynamicSimilarityPoint, smul_eq_mul] using
    (hasDerivAt_dynamicPullback_expanded fields.temperature
      data.temperatureScale data.spatialScale data.physicalTime x τ
      (data.temperatureRate τ * data.temperatureScale τ)
      (-data.spatialRate τ * data.spatialScale τ)
      (data.vorticityScale τ) htemperature
      hlaws.temperatureScale_hasDerivAt
      hlaws.spatialScale_hasDerivAt
      hlaws.physicalTime_hasDerivAt).deriv

/-- Advection by the dilation field for rescaled vorticity. -/
theorem dilationAdvection_rescaledVorticity
    (data : DynamicRescalingData)
    (fields : VorticityStreamFields) (x : ℝ^2) (τ : ℝ)
    (hvorticity : DifferentiableAt ℝ
      (fun y ↦ fields.vorticity y (data.physicalTime τ))
      (dynamicSimilarityPoint data x τ)) :
    advectiveDerivative
        (fun y ↦ data.spatialRate τ • y)
        (fun y ↦ rescaledVorticity data fields y τ) x =
      (data.spatialRate τ * data.vorticityScale τ *
          data.spatialScale τ) *
        fderiv ℝ
          (fun y ↦ fields.vorticity y (data.physicalTime τ))
          (dynamicSimilarityPoint data x τ) x := by
  simpa [rescaledVorticity, dynamicSimilarityPoint, smul_eq_mul] using
    (advectiveDerivative_smul_id_dynamicPullback fields.vorticity
      data.vorticityScale data.spatialScale data.physicalTime
      (data.spatialRate τ) x τ hvorticity)

/-- Advection by the dilation field for rescaled temperature. -/
theorem dilationAdvection_rescaledTemperature
    (data : DynamicRescalingData)
    (fields : VorticityStreamFields) (x : ℝ^2) (τ : ℝ)
    (htemperature : DifferentiableAt ℝ
      (fun y ↦ fields.temperature y (data.physicalTime τ))
      (dynamicSimilarityPoint data x τ)) :
    advectiveDerivative
        (fun y ↦ data.spatialRate τ • y)
        (fun y ↦ rescaledTemperature data fields y τ) x =
      (data.spatialRate τ * data.temperatureScale τ *
          data.spatialScale τ) *
        fderiv ℝ
          (fun y ↦ fields.temperature y (data.physicalTime τ))
          (dynamicSimilarityPoint data x τ) x := by
  simpa [rescaledTemperature, dynamicSimilarityPoint, smul_eq_mul] using
    (advectiveDerivative_smul_id_dynamicPullback fields.temperature
      data.temperatureScale data.spatialScale data.physicalTime
      (data.spatialRate τ) x τ htemperature)

/-- Rescaled-velocity advection of rescaled vorticity carries the common
factor `Cω²`. -/
theorem velocityAdvection_rescaledVorticity
    (data : DynamicRescalingData)
    (fields : VorticityStreamFields) (x : ℝ^2) (τ : ℝ)
    (hscale : data.spatialScale τ ≠ 0)
    (hstream : ContDiff ℝ 1
      (fun y ↦ fields.streamFunction y (data.physicalTime τ)))
    (hvorticity : DifferentiableAt ℝ
      (fun y ↦ fields.vorticity y (data.physicalTime τ))
      (dynamicSimilarityPoint data x τ)) :
    advectiveDerivative
        (fun y ↦
          vorticityStreamVelocity
            (dynamicallyRescaledFields data fields) y τ)
        (fun y ↦ rescaledVorticity data fields y τ) x =
      data.vorticityScale τ ^ 2 *
        advectiveDerivative
          (fun y ↦ vorticityStreamVelocity fields y (data.physicalTime τ))
          (fun y ↦ fields.vorticity y (data.physicalTime τ))
          (dynamicSimilarityPoint data x τ) := by
  have hvelocity :
      (fun y ↦
        vorticityStreamVelocity
          (dynamicallyRescaledFields data fields) y τ) =
        fun y ↦
          (data.vorticityScale τ / data.spatialScale τ) •
            vorticityStreamVelocity fields
              (data.spatialScale τ • y) (data.physicalTime τ) := by
    funext y
    exact vorticityStreamVelocity_dynamicallyRescaledFields
      data fields y τ
      ((hstream.differentiable (by norm_num)).differentiableAt)
  rw [hvelocity]
  change
    advectiveDerivative
        (fun y ↦ (data.vorticityScale τ / data.spatialScale τ) •
          vorticityStreamVelocity fields
            (data.spatialScale τ • y) (data.physicalTime τ))
        (fun y ↦ data.vorticityScale τ *
          fields.vorticity
            (data.spatialScale τ • y) (data.physicalTime τ)) x =
      _
  rw [show
      (fun y ↦ data.vorticityScale τ *
        fields.vorticity
          (data.spatialScale τ • y) (data.physicalTime τ)) =
        fun y ↦ data.vorticityScale τ •
          fields.vorticity
            (data.spatialScale τ • y) (data.physicalTime τ) by
    funext y
    simp [smul_eq_mul]]
  rw [show
      (fun y ↦ (data.vorticityScale τ / data.spatialScale τ) •
        vorticityStreamVelocity fields
          (data.spatialScale τ • y) (data.physicalTime τ)) =
        fun y ↦ (data.vorticityScale τ / data.spatialScale τ) •
          (fun z ↦ vorticityStreamVelocity fields z
            (data.physicalTime τ))
            (centeredDilation (data.spatialScale τ) 0 y) by
    funext y
    simp [centeredDilation]]
  rw [show
      (fun y ↦ data.vorticityScale τ •
        fields.vorticity
          (data.spatialScale τ • y) (data.physicalTime τ)) =
        fun y ↦ data.vorticityScale τ •
          (fun z ↦ fields.vorticity z (data.physicalTime τ))
            (centeredDilation (data.spatialScale τ) 0 y) by
    funext y
    simp [centeredDilation]]
  rw [advectiveDerivative_smul_comp_centered_dilation
    (fun y ↦ vorticityStreamVelocity fields y (data.physicalTime τ))
    (fun y ↦ fields.vorticity y (data.physicalTime τ))
    (data.vorticityScale τ / data.spatialScale τ)
    (data.vorticityScale τ) (data.spatialScale τ) 0 x
    (by
      simpa [dynamicSimilarityPoint, centeredDilation] using
        hvorticity)]
  simp only [smul_eq_mul]
  rw [show
      data.vorticityScale τ / data.spatialScale τ *
            data.vorticityScale τ *
          data.spatialScale τ =
        data.vorticityScale τ ^ 2 by
    field_simp]
  simp [dynamicSimilarityPoint, centeredDilation]

/-- Rescaled-velocity advection of rescaled temperature carries the factor
`Cω Cθ`. -/
theorem velocityAdvection_rescaledTemperature
    (data : DynamicRescalingData)
    (fields : VorticityStreamFields) (x : ℝ^2) (τ : ℝ)
    (hscale : data.spatialScale τ ≠ 0)
    (hstream : ContDiff ℝ 1
      (fun y ↦ fields.streamFunction y (data.physicalTime τ)))
    (htemperature : DifferentiableAt ℝ
      (fun y ↦ fields.temperature y (data.physicalTime τ))
      (dynamicSimilarityPoint data x τ)) :
    advectiveDerivative
        (fun y ↦
          vorticityStreamVelocity
            (dynamicallyRescaledFields data fields) y τ)
        (fun y ↦ rescaledTemperature data fields y τ) x =
      (data.vorticityScale τ * data.temperatureScale τ) *
        advectiveDerivative
          (fun y ↦ vorticityStreamVelocity fields y (data.physicalTime τ))
          (fun y ↦ fields.temperature y (data.physicalTime τ))
          (dynamicSimilarityPoint data x τ) := by
  have hvelocity :
      (fun y ↦
        vorticityStreamVelocity
          (dynamicallyRescaledFields data fields) y τ) =
        fun y ↦
          (data.vorticityScale τ / data.spatialScale τ) •
            vorticityStreamVelocity fields
              (data.spatialScale τ • y) (data.physicalTime τ) := by
    funext y
    exact vorticityStreamVelocity_dynamicallyRescaledFields
      data fields y τ
      ((hstream.differentiable (by norm_num)).differentiableAt)
  rw [hvelocity]
  change
    advectiveDerivative
        (fun y ↦ (data.vorticityScale τ / data.spatialScale τ) •
          vorticityStreamVelocity fields
            (data.spatialScale τ • y) (data.physicalTime τ))
        (fun y ↦ data.temperatureScale τ *
          fields.temperature
            (data.spatialScale τ • y) (data.physicalTime τ)) x =
      _
  rw [show
      (fun y ↦ data.temperatureScale τ *
        fields.temperature
          (data.spatialScale τ • y) (data.physicalTime τ)) =
        fun y ↦ data.temperatureScale τ •
          (fun z ↦ fields.temperature z (data.physicalTime τ))
            (centeredDilation (data.spatialScale τ) 0 y) by
    funext y
    simp [centeredDilation, smul_eq_mul]]
  rw [show
      (fun y ↦ (data.vorticityScale τ / data.spatialScale τ) •
        vorticityStreamVelocity fields
          (data.spatialScale τ • y) (data.physicalTime τ)) =
        fun y ↦ (data.vorticityScale τ / data.spatialScale τ) •
          (fun z ↦ vorticityStreamVelocity fields z
            (data.physicalTime τ))
            (centeredDilation (data.spatialScale τ) 0 y) by
    funext y
    simp [centeredDilation]]
  rw [advectiveDerivative_smul_comp_centered_dilation
    (fun y ↦ vorticityStreamVelocity fields y (data.physicalTime τ))
    (fun y ↦ fields.temperature y (data.physicalTime τ))
    (data.vorticityScale τ / data.spatialScale τ)
    (data.temperatureScale τ) (data.spatialScale τ) 0 x
    (by
      simpa [dynamicSimilarityPoint, centeredDilation] using
        htemperature)]
  simp only [smul_eq_mul]
  rw [show
      data.vorticityScale τ / data.spatialScale τ *
            data.temperatureScale τ *
          data.spatialScale τ =
        data.vorticityScale τ * data.temperatureScale τ by
    field_simp]
  simp [dynamicSimilarityPoint, centeredDilation]

section

open Filter
open scoped Topology

/-- The Laplacian of the rescaled stream function is `C_ω` times the physical Laplacian. Only a
`C²` germ at the physical point is needed. -/
theorem laplacian_rescaledStreamFunction (data : DynamicRescalingData)
    (fields : VorticityStreamFields) (x : ℝ^2) (τ : ℝ) (hscale : data.spatialScale τ ≠ 0)
    (hstream : ContDiffAt ℝ 2 (fun y ↦ fields.streamFunction y (data.physicalTime τ))
      (dynamicSimilarityPoint data x τ)) :
    laplacian (fun y ↦ rescaledStreamFunction data fields y τ) x =
      data.vorticityScale τ *
        laplacian (fun y ↦ fields.streamFunction y (data.physicalTime τ))
          (dynamicSimilarityPoint data x τ) := by
  obtain ⟨g, hg, -, heq⟩ := hstream.exists_contDiff_compactSupport_eventuallyEq
  set c := data.vorticityScale τ / data.spatialScale τ ^ 2
  have hmap : Tendsto (fun y : ℝ^2 ↦ data.spatialScale τ • y) (𝓝 x)
      (𝓝 (dynamicSimilarityPoint data x τ)) :=
    (continuous_const_smul (data.spatialScale τ)).tendsto x
  have hlocal : (fun y ↦ rescaledStreamFunction data fields y τ) =ᶠ[𝓝 x]
      fun y ↦ c * g (centeredDilation (data.spatialScale τ) 0 y) := by
    filter_upwards [heq.comp_tendsto hmap] with y hy
    simp only [Function.comp_apply] at hy
    simp only [rescaledStreamFunction, centeredDilation, sub_zero, dynamicSimilarityPoint, c]
    rw [hy]
  rw [EuclideanLaplacian.laplacian_congr_nhds hlocal, PDE.laplacian_const_smul,
    laplacian_comp_centered_dilation g _ 0 x,
    show centeredDilation (data.spatialScale τ) 0 x = dynamicSimilarityPoint data x τ by
      simp [centeredDilation, dynamicSimilarityPoint],
    ← EuclideanLaplacian.laplacian_congr_nhds heq]
  simp only [c]
  field_simp

end

end

end Boussinesq
