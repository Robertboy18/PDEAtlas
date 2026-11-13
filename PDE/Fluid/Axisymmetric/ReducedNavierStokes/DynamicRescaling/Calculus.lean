/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Axisymmetric.ReducedNavierStokes.DynamicRescaling.Basic
import PDE.FDeriv.Calculus

/-!
# Calculus for dynamically rescaled reduced axisymmetric fields

The common-scale dynamic rescaling of the reduced axisymmetric Euler/Navier–Stokes system rests
on chain rules: one spatial derivative contributes one factor of `L`, the reduced operator
`E = ∂_{rr} + 3r⁻¹∂_r + ∂_{zz}` contributes `L²` (off the axis and at its assigned axis value),
and the nonlinear terms carry the same amplitudes as the time derivatives they balance. The axis
and off-axis calculations are separate, so Lean's totalized division is never used in place of
the smooth value of `3r⁻¹∂_r` at `r = 0`.

The bookkeeping principle: a rescaled field is `A(τ) u(Lx + Ze_z, t(τ))` for a
physical field `u`, so each derivative in the rescaled variable `x` brings one factor of `L`
relative to a derivative in the physical variable. Terms of the reduced equations that are
homogeneous of the same degree in `(A, L)` can then be compared once the compatibility
relations `Aω = AL`, `Aψ = A/L` of `Basic` are imposed. Every lemma here is a chain-rule
computation; there is no PDE content beyond the definitions of the reduced operators.

## Main results

* `partialDeriv_dynamicallyRescaledSwirl`, `partialDeriv_dynamicallyRescaledVorticity`,
  `partialDeriv_dynamicallyRescaledStreamFunction`: first derivatives carry the amplitude and
  one factor of `L`.
* `radialFourAxialLaplacian_dynamicReducedPullback`,
  `axisExtendedRadialFourAxialLaplacian_dynamicReducedPullback`: the reduced operator `E` scales
  by `L²`, off the axis and at the assigned axis value.
* `reducedMeridianVelocity_dynamicallyRescaledReducedFields`: the reconstructed meridian velocity
  has amplitude `A/L`.
* `reducedSwirlSource_*`, `reducedVorticitySource_*_compatible`, `reducedAdvection_*`: the
  nonlinear sources and the meridian advection have amplitudes `A²` (swirl) and `A Aω`
  (vorticity), the same as the corresponding time derivatives.
* `axisExtendedReducedStreamFunctionResidual_dynamicallyRescaledReducedFields`: under `Aω = AL`
  the stream residual transports with amplitude `Aω`, including on the axis.
* `deriv_add_rescaledReducedAdvection_dynamicallyRescaledSwirl` and its vorticity counterpart:
  the rescaled time derivative plus modulated advection by `λx + Ce_z + u` is the physical
  material derivative with amplitude `A²` (resp. `A Aω`) plus the linear rate term `cᵤ ũ₁`
  (resp. `cω ω̃₁`). These are the inputs to the residual identities of `Equations`.

For the origin of the dynamic rescaling formulation see the references in `Basic`.
-/

@[expose] public section

open PDE (advectiveDerivative)

namespace AxisymmetricFlow

open PDE.Common
open PDE.Representations.Similarity

set_option linter.missingDocs true

noncomputable section

/-- A spatial derivative of dynamically rescaled swirl carries amplitude
`A` and one spatial-scale factor `L`. -/
theorem partialDeriv_dynamicallyRescaledSwirl
    (data : DynamicRescalingData) (fields : ReducedFields)
    (i : Fin 2) (x : ℝ^2) (τ : ℝ)
    (hswirl :
      DifferentiableAt ℝ
        (fun y ↦ fields.swirl y (data.physicalTime τ))
        (dynamicReducedSimilarityPoint data x τ)) :
    (∂[i]
        (fun y ↦ dynamicallyRescaledSwirl data fields y τ)) x =
      data.swirlScale τ * data.spatialScale τ *
        (∂[i]
          (fun y ↦ fields.swirl y (data.physicalTime τ)))
          (dynamicReducedSimilarityPoint data x τ) := by
  simpa [dynamicallyRescaledSwirl, dynamicAffinePullback,
    dynamicReducedSimilarityPoint, dynamicAffinePoint, smul_eq_mul] using
    partialDeriv_const_mul_comp_affineDilation i
      (fun y ↦ fields.swirl y (data.physicalTime τ))
      (data.swirlScale τ) (data.spatialScale τ)
      (dynamicAxialShift data τ) x hswirl

/-- A spatial derivative of dynamically rescaled vorticity carries amplitude
`Aω` and one spatial-scale factor `L`. -/
theorem partialDeriv_dynamicallyRescaledVorticity
    (data : DynamicRescalingData) (fields : ReducedFields)
    (i : Fin 2) (x : ℝ^2) (τ : ℝ)
    (hvorticity :
      DifferentiableAt ℝ
        (fun y ↦ fields.vorticity y (data.physicalTime τ))
        (dynamicReducedSimilarityPoint data x τ)) :
    (∂[i]
        (fun y ↦ dynamicallyRescaledVorticity data fields y τ)) x =
      data.vorticityScale τ * data.spatialScale τ *
        (∂[i]
          (fun y ↦ fields.vorticity y (data.physicalTime τ)))
          (dynamicReducedSimilarityPoint data x τ) := by
  simpa [dynamicallyRescaledVorticity, dynamicAffinePullback,
    dynamicReducedSimilarityPoint, dynamicAffinePoint, smul_eq_mul] using
    partialDeriv_const_mul_comp_affineDilation i
      (fun y ↦ fields.vorticity y (data.physicalTime τ))
      (data.vorticityScale τ) (data.spatialScale τ)
      (dynamicAxialShift data τ) x hvorticity

/-- A spatial derivative of the dynamically rescaled streamfunction carries
amplitude `A/L` and one spatial-scale factor `L`. -/
theorem partialDeriv_dynamicallyRescaledStreamFunction
    (data : DynamicRescalingData) (fields : ReducedFields)
    (i : Fin 2) (x : ℝ^2) (τ : ℝ)
    (hstream :
      DifferentiableAt ℝ
        (fun y ↦ fields.streamFunction y (data.physicalTime τ))
        (dynamicReducedSimilarityPoint data x τ)) :
    (∂[i]
        (fun y ↦ dynamicallyRescaledStreamFunction data fields y τ)) x =
      (data.swirlScale τ / data.spatialScale τ) *
        data.spatialScale τ *
        (∂[i]
          (fun y ↦ fields.streamFunction y (data.physicalTime τ)))
          (dynamicReducedSimilarityPoint data x τ) := by
  simpa [dynamicallyRescaledStreamFunction,
    dynamicReducedSimilarityPoint, dynamicAffinePoint] using
    partialDeriv_const_mul_comp_affineDilation i
      (fun y ↦ fields.streamFunction y (data.physicalTime τ))
      (data.swirlScale τ / data.spatialScale τ)
      (data.spatialScale τ) (dynamicAxialShift data τ) x hstream

/-- A first derivative of an amplitude-scaled dynamic reduced pullback
carries one spatial-scale factor. -/
theorem partialDeriv_dynamicReducedPullback
    (data : DynamicRescalingData) (profile : ℝ^2 → ℝ)
    (amplitude : ℝ) (i : Fin 2) (x : ℝ^2) (τ : ℝ)
    (hprofile :
      DifferentiableAt ℝ profile
        (dynamicReducedSimilarityPoint data x τ)) :
    (∂[i]
        (fun y ↦ amplitude *
          profile (dynamicReducedSimilarityPoint data y τ))) x =
      amplitude * data.spatialScale τ *
        (∂[i] profile)
          (dynamicReducedSimilarityPoint data x τ) := by
  simpa [dynamicReducedSimilarityPoint, dynamicAffinePoint] using
    partialDeriv_const_mul_comp_affineDilation
      i profile amplitude (data.spatialScale τ)
      (dynamicAxialShift data τ) x hprofile

/-- A second derivative of an amplitude-scaled dynamic affine pullback
carries two spatial-scale factors. -/
theorem partialDeriv_partialDeriv_dynamicReducedPullback
    (data : DynamicRescalingData) (profile : ℝ^2 → ℝ)
    (amplitude : ℝ) (i k : Fin 2) (x : ℝ^2) (τ : ℝ)
    (hprofile : ContDiff ℝ 2 profile) :
    (∂[i]
        (fun y ↦ (∂[k]
          (fun z ↦ amplitude *
            profile (dynamicReducedSimilarityPoint data z τ))) y)) x =
      amplitude * data.spatialScale τ ^ 2 *
        (∂[i] (fun y ↦ (∂[k] profile) y))
          (dynamicReducedSimilarityPoint data x τ) := by
  simpa [dynamicReducedSimilarityPoint, dynamicAffinePoint] using
    partialDeriv_partialDeriv_const_mul_comp_affineDilation
      i k profile amplitude (data.spatialScale τ)
      (dynamicAxialShift data τ) x hprofile

/-- Off the axis, the radial-four-plus-axial operator scales by
`amplitude * L²` under the dynamic affine similarity map. -/
theorem radialFourAxialLaplacian_dynamicReducedPullback
    (data : DynamicRescalingData) (profile : ℝ^2 → ℝ)
    (amplitude : ℝ) (x : ℝ^2) (τ : ℝ)
    (hprofile : ContDiff ℝ 2 profile)
    (hscale : data.spatialScale τ ≠ 0)
    (hr : x (0 : Fin 2) ≠ 0) :
    radialFourAxialLaplacian
        (fun y ↦ amplitude *
          profile (dynamicReducedSimilarityPoint data y τ)) x =
      amplitude * data.spatialScale τ ^ 2 *
        radialFourAxialLaplacian profile
          (dynamicReducedSimilarityPoint data x τ) := by
  have hdiff :
      DifferentiableAt ℝ profile
        (dynamicReducedSimilarityPoint data x τ) :=
    (hprofile.differentiable (by norm_num)).differentiableAt
  unfold radialFourAxialLaplacian
  rw [partialDeriv_partialDeriv_dynamicReducedPullback data profile amplitude (0 : Fin 2)
        (0 : Fin 2) x τ hprofile,
      partialDeriv_dynamicReducedPullback data profile amplitude (0 : Fin 2) x τ hdiff,
      partialDeriv_partialDeriv_dynamicReducedPullback data profile amplitude (1 : Fin 2)
        (1 : Fin 2) x τ hprofile, dynamicReducedSimilarityPoint_radial]
  field_simp

/-- The algebraically axis-extended radial-four-plus-axial operator scales by
`amplitude * L²` both on and off the symmetry axis. -/
theorem axisExtendedRadialFourAxialLaplacian_dynamicReducedPullback
    (data : DynamicRescalingData) (profile : ℝ^2 → ℝ)
    (amplitude : ℝ) (x : ℝ^2) (τ : ℝ)
    (hprofile : ContDiff ℝ 2 profile)
    (hscale : data.spatialScale τ ≠ 0) :
    axisExtendedRadialFourAxialLaplacian
        (fun y ↦ amplitude *
          profile (dynamicReducedSimilarityPoint data y τ)) x =
      amplitude * data.spatialScale τ ^ 2 *
        axisExtendedRadialFourAxialLaplacian profile
          (dynamicReducedSimilarityPoint data x τ) := by
  by_cases hr : x (0 : Fin 2) = 0
  · have hpoint :
        dynamicReducedSimilarityPoint data x τ (0 : Fin 2) = 0 := by
      rw [dynamicReducedSimilarityPoint_radial, hr]
      ring
    rw [axisExtendedRadialFourAxialLaplacian_of_eq_zero _ _ hr,
        axisExtendedRadialFourAxialLaplacian_of_eq_zero _ _ hpoint,
        partialDeriv_partialDeriv_dynamicReducedPullback data profile amplitude (0 : Fin 2)
          (0 : Fin 2) x τ hprofile,
        partialDeriv_partialDeriv_dynamicReducedPullback data profile amplitude (1 : Fin 2)
          (1 : Fin 2) x τ hprofile]
    ring
  · have hpoint :
        dynamicReducedSimilarityPoint data x τ (0 : Fin 2) ≠ 0 := by
      rw [dynamicReducedSimilarityPoint_radial]
      exact mul_ne_zero hscale hr
    rw [axisExtendedRadialFourAxialLaplacian_of_ne _ _ hr,
        axisExtendedRadialFourAxialLaplacian_of_ne _ _ hpoint]
    exact radialFourAxialLaplacian_dynamicReducedPullback
      data profile amplitude x τ hprofile hscale hr

/-- The dynamically rescaled radial velocity has amplitude `A/L`. -/
theorem reducedRadialVelocity_dynamicallyRescaledReducedFields
    (data : DynamicRescalingData) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hstream :
      DifferentiableAt ℝ
        (fun y ↦ fields.streamFunction y (data.physicalTime τ))
        (dynamicReducedSimilarityPoint data x τ)) :
    reducedRadialVelocity
        (dynamicallyRescaledReducedFields data fields) x τ =
      (data.swirlScale τ / data.spatialScale τ) *
        reducedRadialVelocity fields
          (dynamicReducedSimilarityPoint data x τ)
          (data.physicalTime τ) := by
  rw [reducedRadialVelocity]
  change
    -x (0 : Fin 2) *
        (∂[(1 : Fin 2)]
          (fun y ↦ dynamicallyRescaledStreamFunction data fields y τ)) x =
      _
  rw [partialDeriv_dynamicallyRescaledStreamFunction data fields (1 : Fin 2) x τ hstream,
      reducedRadialVelocity, dynamicReducedSimilarityPoint_radial]
  ring

/-- The dynamically rescaled axial velocity has amplitude `A/L`. -/
theorem reducedAxialVelocity_dynamicallyRescaledReducedFields
    (data : DynamicRescalingData) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hstream :
      DifferentiableAt ℝ
        (fun y ↦ fields.streamFunction y (data.physicalTime τ))
        (dynamicReducedSimilarityPoint data x τ)) :
    reducedAxialVelocity
        (dynamicallyRescaledReducedFields data fields) x τ =
      (data.swirlScale τ / data.spatialScale τ) *
        reducedAxialVelocity fields
          (dynamicReducedSimilarityPoint data x τ)
          (data.physicalTime τ) := by
  rw [reducedAxialVelocity]
  change
    2 * dynamicallyRescaledStreamFunction data fields x τ +
        x (0 : Fin 2) *
          (∂[(0 : Fin 2)]
            (fun y ↦ dynamicallyRescaledStreamFunction data fields y τ)) x =
      _
  rw [partialDeriv_dynamicallyRescaledStreamFunction data fields (0 : Fin 2) x τ hstream,
      reducedAxialVelocity, dynamicReducedSimilarityPoint_radial]
  simp only [dynamicallyRescaledStreamFunction]
  ring

/-- The dynamically reconstructed meridian velocity has amplitude `A/L`. -/
theorem reducedMeridianVelocity_dynamicallyRescaledReducedFields
    (data : DynamicRescalingData) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hstream :
      DifferentiableAt ℝ
        (fun y ↦ fields.streamFunction y (data.physicalTime τ))
        (dynamicReducedSimilarityPoint data x τ)) :
    reducedMeridianVelocity
        (dynamicallyRescaledReducedFields data fields) x τ =
      (data.swirlScale τ / data.spatialScale τ) •
        reducedMeridianVelocity fields
          (dynamicReducedSimilarityPoint data x τ)
          (data.physicalTime τ) := by
  ext i
  fin_cases i
  · simpa [smul_eq_mul] using
      reducedRadialVelocity_dynamicallyRescaledReducedFields
        data fields x τ hstream
  · simpa [smul_eq_mul] using
      reducedAxialVelocity_dynamicallyRescaledReducedFields
        data fields x τ hstream

/-- The reduced swirl source of the dynamically rescaled fields has
amplitude `A²`. -/
theorem reducedSwirlSource_dynamicallyRescaledReducedFields
    (data : DynamicRescalingData) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hscale : data.spatialScale τ ≠ 0)
    (hstream :
      DifferentiableAt ℝ
        (fun y ↦ fields.streamFunction y (data.physicalTime τ))
        (dynamicReducedSimilarityPoint data x τ)) :
    reducedSwirlSource
        (dynamicallyRescaledReducedFields data fields) x τ =
      data.swirlScale τ ^ 2 *
        reducedSwirlSource fields
          (dynamicReducedSimilarityPoint data x τ)
          (data.physicalTime τ) := by
  unfold reducedSwirlSource
  change
    2 * dynamicallyRescaledSwirl data fields x τ *
        (∂[(1 : Fin 2)]
          (fun y ↦ dynamicallyRescaledStreamFunction data fields y τ)) x =
      _
  rw [partialDeriv_dynamicallyRescaledStreamFunction data fields (1 : Fin 2) x τ hstream]
  simp only [dynamicallyRescaledSwirl, dynamicAffinePullback,
    dynamicReducedSimilarityPoint, smul_eq_mul]
  field_simp

/-- The reduced vorticity source of the dynamically rescaled fields has
amplitude `A²L`. -/
theorem reducedVorticitySource_dynamicallyRescaledReducedFields
    (data : DynamicRescalingData) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hswirl :
      DifferentiableAt ℝ
        (fun y ↦ fields.swirl y (data.physicalTime τ))
        (dynamicReducedSimilarityPoint data x τ)) :
    reducedVorticitySource
        (dynamicallyRescaledReducedFields data fields) x τ =
      data.swirlScale τ ^ 2 * data.spatialScale τ *
        reducedVorticitySource fields
          (dynamicReducedSimilarityPoint data x τ)
          (data.physicalTime τ) := by
  unfold reducedVorticitySource
  change
    2 * dynamicallyRescaledSwirl data fields x τ *
        (∂[(1 : Fin 2)]
          (fun y ↦ dynamicallyRescaledSwirl data fields y τ)) x =
      _
  rw [partialDeriv_dynamicallyRescaledSwirl data fields (1 : Fin 2) x τ hswirl]
  simp only [dynamicallyRescaledSwirl, dynamicAffinePullback,
    dynamicReducedSimilarityPoint, smul_eq_mul]
  ring

/-- Under `Aω = AL`, the dynamically rescaled vorticity source has the
time-derivative amplitude `A Aω`. -/
theorem reducedVorticitySource_dynamicallyRescaledReducedFields_compatible
    (data : DynamicRescalingData) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hcompat :
      data.vorticityScale τ =
        data.swirlScale τ * data.spatialScale τ)
    (hswirl :
      DifferentiableAt ℝ
        (fun y ↦ fields.swirl y (data.physicalTime τ))
        (dynamicReducedSimilarityPoint data x τ)) :
    reducedVorticitySource
        (dynamicallyRescaledReducedFields data fields) x τ =
      (data.swirlScale τ * data.vorticityScale τ) *
        reducedVorticitySource fields
          (dynamicReducedSimilarityPoint data x τ)
          (data.physicalTime τ) := by
  rw [reducedVorticitySource_dynamicallyRescaledReducedFields data fields x τ hswirl, hcompat]
  ring

/-- Physical meridian advection of dynamically rescaled swirl has amplitude
`A²`. -/
theorem reducedAdvection_dynamicallyRescaledSwirl
    (data : DynamicRescalingData) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hscale : data.spatialScale τ ≠ 0)
    (hstream :
      DifferentiableAt ℝ
        (fun y ↦ fields.streamFunction y (data.physicalTime τ))
        (dynamicReducedSimilarityPoint data x τ))
    (hswirl :
      DifferentiableAt ℝ
        (fun y ↦ fields.swirl y (data.physicalTime τ))
        (dynamicReducedSimilarityPoint data x τ)) :
    reducedAdvection
        (dynamicallyRescaledReducedFields data fields)
        (fun y ↦ dynamicallyRescaledSwirl data fields y τ) x τ =
      data.swirlScale τ ^ 2 *
        reducedAdvection fields
          (fun y ↦ fields.swirl y (data.physicalTime τ))
          (dynamicReducedSimilarityPoint data x τ)
          (data.physicalTime τ) := by
  rw [reducedAdvection_eq, reducedAdvection_eq,
      reducedRadialVelocity_dynamicallyRescaledReducedFields data fields x τ hstream,
      reducedAxialVelocity_dynamicallyRescaledReducedFields data fields x τ hstream,
      partialDeriv_dynamicallyRescaledSwirl data fields (0 : Fin 2) x τ hswirl,
      partialDeriv_dynamicallyRescaledSwirl data fields (1 : Fin 2) x τ hswirl]
  field_simp

/-- Physical meridian advection of dynamically rescaled vorticity has
amplitude `A Aω`. -/
theorem reducedAdvection_dynamicallyRescaledVorticity
    (data : DynamicRescalingData) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hscale : data.spatialScale τ ≠ 0)
    (hstream :
      DifferentiableAt ℝ
        (fun y ↦ fields.streamFunction y (data.physicalTime τ))
        (dynamicReducedSimilarityPoint data x τ))
    (hvorticity :
      DifferentiableAt ℝ
        (fun y ↦ fields.vorticity y (data.physicalTime τ))
        (dynamicReducedSimilarityPoint data x τ)) :
    reducedAdvection
        (dynamicallyRescaledReducedFields data fields)
        (fun y ↦ dynamicallyRescaledVorticity data fields y τ) x τ =
      (data.swirlScale τ * data.vorticityScale τ) *
        reducedAdvection fields
          (fun y ↦ fields.vorticity y (data.physicalTime τ))
          (dynamicReducedSimilarityPoint data x τ)
          (data.physicalTime τ) := by
  rw [reducedAdvection_eq, reducedAdvection_eq,
      reducedRadialVelocity_dynamicallyRescaledReducedFields data fields x τ hstream,
      reducedAxialVelocity_dynamicallyRescaledReducedFields data fields x τ hstream,
      partialDeriv_dynamicallyRescaledVorticity data fields (0 : Fin 2) x τ hvorticity,
      partialDeriv_dynamicallyRescaledVorticity data fields (1 : Fin 2) x τ hvorticity]
  field_simp

/-- The off-axis reduced operator on dynamically rescaled swirl carries
amplitude `A L²`. -/
theorem radialFourAxialLaplacian_dynamicallyRescaledSwirl
    (data : DynamicRescalingData) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hswirl :
      ContDiff ℝ 2 (fun y ↦ fields.swirl y (data.physicalTime τ)))
    (hscale : data.spatialScale τ ≠ 0)
    (hr : x (0 : Fin 2) ≠ 0) :
    radialFourAxialLaplacian
        (fun y ↦ dynamicallyRescaledSwirl data fields y τ) x =
      data.swirlScale τ * data.spatialScale τ ^ 2 *
        radialFourAxialLaplacian
          (fun y ↦ fields.swirl y (data.physicalTime τ))
          (dynamicReducedSimilarityPoint data x τ) := by
  simpa [dynamicallyRescaledSwirl, dynamicAffinePullback,
    dynamicReducedSimilarityPoint, dynamicAffinePoint, smul_eq_mul] using
    radialFourAxialLaplacian_dynamicReducedPullback
      data (fun y ↦ fields.swirl y (data.physicalTime τ))
      (data.swirlScale τ) x τ hswirl hscale hr

/-- The off-axis reduced operator on dynamically rescaled vorticity carries
amplitude `Aω L²`. -/
theorem radialFourAxialLaplacian_dynamicallyRescaledVorticity
    (data : DynamicRescalingData) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hvorticity :
      ContDiff ℝ 2 (fun y ↦ fields.vorticity y (data.physicalTime τ)))
    (hscale : data.spatialScale τ ≠ 0)
    (hr : x (0 : Fin 2) ≠ 0) :
    radialFourAxialLaplacian
        (fun y ↦ dynamicallyRescaledVorticity data fields y τ) x =
      data.vorticityScale τ * data.spatialScale τ ^ 2 *
        radialFourAxialLaplacian
          (fun y ↦ fields.vorticity y (data.physicalTime τ))
          (dynamicReducedSimilarityPoint data x τ) := by
  simpa [dynamicallyRescaledVorticity, dynamicAffinePullback,
    dynamicReducedSimilarityPoint, dynamicAffinePoint, smul_eq_mul] using
    radialFourAxialLaplacian_dynamicReducedPullback
      data (fun y ↦ fields.vorticity y (data.physicalTime τ))
      (data.vorticityScale τ) x τ hvorticity hscale hr

/-- The axis-extended reduced operator on dynamically rescaled swirl carries
amplitude `A L²`, including on the axis. -/
theorem axisExtendedRadialFourAxialLaplacian_dynamicallyRescaledSwirl
    (data : DynamicRescalingData) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hswirl :
      ContDiff ℝ 2 (fun y ↦ fields.swirl y (data.physicalTime τ)))
    (hscale : data.spatialScale τ ≠ 0) :
    axisExtendedRadialFourAxialLaplacian
        (fun y ↦ dynamicallyRescaledSwirl data fields y τ) x =
      data.swirlScale τ * data.spatialScale τ ^ 2 *
        axisExtendedRadialFourAxialLaplacian
          (fun y ↦ fields.swirl y (data.physicalTime τ))
          (dynamicReducedSimilarityPoint data x τ) := by
  simpa [dynamicallyRescaledSwirl, dynamicAffinePullback,
    dynamicReducedSimilarityPoint, dynamicAffinePoint, smul_eq_mul] using
    axisExtendedRadialFourAxialLaplacian_dynamicReducedPullback
      data (fun y ↦ fields.swirl y (data.physicalTime τ))
      (data.swirlScale τ) x τ hswirl hscale

/-- The axis-extended reduced operator on dynamically rescaled vorticity
carries amplitude `Aω L²`, including on the axis. -/
theorem axisExtendedRadialFourAxialLaplacian_dynamicallyRescaledVorticity
    (data : DynamicRescalingData) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hvorticity :
      ContDiff ℝ 2 (fun y ↦ fields.vorticity y (data.physicalTime τ)))
    (hscale : data.spatialScale τ ≠ 0) :
    axisExtendedRadialFourAxialLaplacian
        (fun y ↦ dynamicallyRescaledVorticity data fields y τ) x =
      data.vorticityScale τ * data.spatialScale τ ^ 2 *
        axisExtendedRadialFourAxialLaplacian
          (fun y ↦ fields.vorticity y (data.physicalTime τ))
          (dynamicReducedSimilarityPoint data x τ) := by
  simpa [dynamicallyRescaledVorticity, dynamicAffinePullback,
    dynamicReducedSimilarityPoint, dynamicAffinePoint, smul_eq_mul] using
    axisExtendedRadialFourAxialLaplacian_dynamicReducedPullback
      data (fun y ↦ fields.vorticity y (data.physicalTime τ))
      (data.vorticityScale τ) x τ hvorticity hscale

/-- Off the axis, elliptic compatibility `Aω = AL` transports the reduced
streamfunction residual with amplitude `Aω`. -/
theorem reducedStreamFunctionResidual_dynamicallyRescaledReducedFields
    (data : DynamicRescalingData) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hstream :
      ContDiff ℝ 2
        (fun y ↦ fields.streamFunction y (data.physicalTime τ)))
    (hscale : data.spatialScale τ ≠ 0)
    (hcompat :
      data.vorticityScale τ =
        data.swirlScale τ * data.spatialScale τ)
    (hr : x (0 : Fin 2) ≠ 0) :
    reducedStreamFunctionResidual
        (dynamicallyRescaledReducedFields data fields) x τ =
      data.vorticityScale τ *
        reducedStreamFunctionResidual fields
          (dynamicReducedSimilarityPoint data x τ)
          (data.physicalTime τ) := by
  unfold reducedStreamFunctionResidual
  change
    -radialFourAxialLaplacian
        (fun y ↦ dynamicallyRescaledStreamFunction data fields y τ) x -
      dynamicallyRescaledVorticity data fields x τ =
      _
  rw [show (fun y ↦ dynamicallyRescaledStreamFunction data fields y τ) = fun y ↦
        (data.swirlScale τ / data.spatialScale τ) *
        (fun z ↦ fields.streamFunction z (data.physicalTime τ))
        (dynamicReducedSimilarityPoint data y τ) by rfl,
      radialFourAxialLaplacian_dynamicReducedPullback data
        (fun y ↦ fields.streamFunction y (data.physicalTime τ))
        (data.swirlScale τ / data.spatialScale τ) x τ hstream hscale hr]
  simp only [dynamicallyRescaledVorticity, dynamicAffinePullback,
    dynamicReducedSimilarityPoint, smul_eq_mul]
  rw [hcompat]
  field_simp

/-- Elliptic compatibility `Aω = AL` transports the axis-value-extended reduced
streamfunction residual with amplitude `Aω`. -/
theorem axisExtendedReducedStreamFunctionResidual_dynamicallyRescaledReducedFields
    (data : DynamicRescalingData) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hstream :
      ContDiff ℝ 2
        (fun y ↦ fields.streamFunction y (data.physicalTime τ)))
    (hscale : data.spatialScale τ ≠ 0)
    (hcompat :
      data.vorticityScale τ =
        data.swirlScale τ * data.spatialScale τ) :
    axisExtendedReducedStreamFunctionResidual
        (dynamicallyRescaledReducedFields data fields) x τ =
      data.vorticityScale τ *
        axisExtendedReducedStreamFunctionResidual fields
          (dynamicReducedSimilarityPoint data x τ)
          (data.physicalTime τ) := by
  unfold axisExtendedReducedStreamFunctionResidual
  change
    -axisExtendedRadialFourAxialLaplacian
        (fun y ↦ dynamicallyRescaledStreamFunction data fields y τ) x -
      dynamicallyRescaledVorticity data fields x τ =
      _
  rw [show (fun y ↦ dynamicallyRescaledStreamFunction data fields y τ) = fun y ↦
        (data.swirlScale τ / data.spatialScale τ) *
        (fun z ↦ fields.streamFunction z (data.physicalTime τ))
        (dynamicReducedSimilarityPoint data y τ) by rfl,
      axisExtendedRadialFourAxialLaplacian_dynamicReducedPullback data
        (fun y ↦ fields.streamFunction y (data.physicalTime τ))
        (data.swirlScale τ / data.spatialScale τ) x τ hstream hscale]
  simp only [dynamicallyRescaledVorticity, dynamicAffinePullback,
    dynamicReducedSimilarityPoint, smul_eq_mul]
  rw [hcompat]
  field_simp

/-- The time chain rule cancels the affine modulation advection.

For a pullback with amplitude `B`, amplitude rate `c`, physical-time rate
`A`, spatial rate `L' = -λL`, and axial shift rate `-CL e_z`, the sum of
the rescaled time derivative and advection by `λx + Ce_z` is
`BA ∂_t f + c f̃`. -/
theorem deriv_dynamicReducedPullback_add_modulationAdvection
    (data : DynamicRescalingData)
    (field : ℝ^2 → ℝ → ℝ)
    (amplitudeScale rate : ℝ → ℝ)
    (x : ℝ^2) (τ : ℝ)
    (hfield :
      DifferentiableAt ℝ (Function.uncurry field)
        (dynamicReducedSimilarityPoint data x τ, data.physicalTime τ))
    (hamplitude :
      HasDerivAt amplitudeScale
        (rate τ * amplitudeScale τ) τ)
    (hlaws : SatisfiesDynamicScaleODEsAt data τ) :
    deriv
        (fun s ↦ dynamicAffinePullback field amplitudeScale
          data.spatialScale (dynamicAxialShift data)
          data.physicalTime x s) τ +
      advectiveDerivative
        (fun y ↦
          data.spatialRate τ • y +
            data.axialDrift τ • axialUnit)
        (fun y ↦ dynamicAffinePullback field amplitudeScale
          data.spatialScale (dynamicAxialShift data)
          data.physicalTime y τ) x =
      amplitudeScale τ * data.swirlScale τ *
          deriv (field (dynamicReducedSimilarityPoint data x τ))
            (data.physicalTime τ) +
        rate τ *
          dynamicAffinePullback field amplitudeScale
            data.spatialScale (dynamicAxialShift data)
            data.physicalTime x τ := by
  have hspatial :
      DifferentiableAt ℝ (fun y ↦ field y (data.physicalTime τ)) (dynamicReducedSimilarityPoint
      data x τ) := by
    fun_prop
  have hpartial (i : Fin 2) :
      (∂[i]
          (fun y ↦ dynamicAffinePullback field amplitudeScale
            data.spatialScale (dynamicAxialShift data)
            data.physicalTime y τ)) x =
        amplitudeScale τ * data.spatialScale τ *
          (∂[i]
            (fun y ↦ field y (data.physicalTime τ)))
            (dynamicReducedSimilarityPoint data x τ) := by
    simpa [dynamicAffinePullback, dynamicReducedSimilarityPoint,
      dynamicAffinePoint, smul_eq_mul] using
      partialDeriv_const_mul_comp_affineDilation i
        (fun y ↦ field y (data.physicalTime τ))
        (amplitudeScale τ) (data.spatialScale τ)
        (dynamicAxialShift data τ) x hspatial
  rw [(hasDerivAt_dynamicAffinePullback_expanded field amplitudeScale data.spatialScale
      (dynamicAxialShift data) data.physicalTime x τ (rate τ * amplitudeScale τ)
      (-data.spatialRate τ * data.spatialScale τ) (data.swirlScale τ)
      ((-data.axialDrift τ * data.spatialScale τ) • axialUnit) hfield hamplitude
      hlaws.spatialScale_hasDerivAt hlaws.axialShift_hasDerivAt
      hlaws.physicalTime_hasDerivAt).deriv,
    PDE.advectiveDerivative_eq_sum_mul_partialDeriv, PDE.fderiv_apply_eq_sum_partialDeriv_mul]
  simp only [Fin.sum_univ_two]
  rw [hpartial 0, hpartial 1]
  simp only [Fin.isValue, neg_mul, neg_smul, PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply,
    smul_eq_mul, axialUnit_apply_zero, mul_zero, neg_zero, add_zero, mul_neg, axialUnit_apply_one,
    mul_one, dynamicReducedSimilarityPoint, dynamicAffinePullback]
  ring

/-- The swirl time chain rule plus affine modulation advection has physical
time-derivative amplitude `A²` and leaves the linear rate `cᵤ ũ₁`. -/
theorem deriv_dynamicallyRescaledSwirl_add_modulationAdvection
    (data : DynamicRescalingData) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hfield :
      DifferentiableAt ℝ (Function.uncurry fields.swirl)
        (dynamicReducedSimilarityPoint data x τ, data.physicalTime τ))
    (hlaws : SatisfiesDynamicScaleODEsAt data τ) :
    deriv (fun s ↦ dynamicallyRescaledSwirl data fields x s) τ +
      advectiveDerivative
        (fun y ↦
          data.spatialRate τ • y +
            data.axialDrift τ • axialUnit)
        (fun y ↦ dynamicallyRescaledSwirl data fields y τ) x =
      data.swirlScale τ ^ 2 *
          deriv
            (fields.swirl (dynamicReducedSimilarityPoint data x τ))
            (data.physicalTime τ) +
        data.swirlRate τ *
          dynamicallyRescaledSwirl data fields x τ := by
  have hspatial :
      DifferentiableAt ℝ (fun y ↦ fields.swirl y (data.physicalTime τ))
      (dynamicReducedSimilarityPoint data x τ) := by
    fun_prop
  simpa [dynamicallyRescaledSwirl, pow_two, mul_assoc] using
    deriv_dynamicReducedPullback_add_modulationAdvection
      data fields.swirl data.swirlScale data.swirlRate x τ
      hfield hlaws.swirlScale_hasDerivAt hlaws

/-- The vorticity time chain rule plus affine modulation advection has
physical time-derivative amplitude `A Aω` and leaves the linear rate
`cω ω̃₁`. -/
theorem deriv_dynamicallyRescaledVorticity_add_modulationAdvection
    (data : DynamicRescalingData) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hfield :
      DifferentiableAt ℝ (Function.uncurry fields.vorticity)
        (dynamicReducedSimilarityPoint data x τ, data.physicalTime τ))
    (hlaws : SatisfiesDynamicScaleODEsAt data τ) :
    deriv (fun s ↦ dynamicallyRescaledVorticity data fields x s) τ +
      advectiveDerivative
        (fun y ↦
          data.spatialRate τ • y +
            data.axialDrift τ • axialUnit)
        (fun y ↦ dynamicallyRescaledVorticity data fields y τ) x =
      (data.swirlScale τ * data.vorticityScale τ) *
          deriv
            (fields.vorticity
              (dynamicReducedSimilarityPoint data x τ))
            (data.physicalTime τ) +
        data.vorticityRate τ *
          dynamicallyRescaledVorticity data fields x τ := by
  have hspatial :
      DifferentiableAt ℝ (fun y ↦ fields.vorticity y (data.physicalTime τ))
      (dynamicReducedSimilarityPoint data x τ) := by
    fun_prop
  simpa [dynamicallyRescaledVorticity, mul_comm, mul_left_comm,
    mul_assoc] using
    deriv_dynamicReducedPullback_add_modulationAdvection
      data fields.vorticity data.vorticityScale data.vorticityRate x τ
      hfield hlaws.vorticityScale_hasDerivAt hlaws

/-- Modulated reduced advection is the sum of affine modulation advection
and advection by the reconstructed meridian velocity. -/
theorem rescaledReducedAdvection_eq_modulation_add_reducedAdvection
    (fields : ReducedFields)
    (spatialRate axialDrift : ℝ → ℝ)
    (f : ℝ^2 → ℝ) (x : ℝ^2) (t : ℝ) :
    rescaledReducedAdvection fields spatialRate axialDrift f x t =
      advectiveDerivative
          (fun y ↦
            spatialRate t • y + axialDrift t • axialUnit)
          f x +
        reducedAdvection fields f x t := by
  unfold rescaledReducedAdvection rescaledReducedTransportVelocity
  rw [PDE.advectiveDerivative_add_advecting]
  rfl

/-- The time derivative plus full modulated advection of dynamically
rescaled swirl is the physical material derivative with amplitude `A²`,
plus the linear amplitude-rate term. -/
theorem deriv_add_rescaledReducedAdvection_dynamicallyRescaledSwirl
    (data : DynamicRescalingData) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hscale : data.spatialScale τ ≠ 0)
    (hfield :
      DifferentiableAt ℝ (Function.uncurry fields.swirl)
        (dynamicReducedSimilarityPoint data x τ, data.physicalTime τ))
    (hstream :
      DifferentiableAt ℝ
        (fun y ↦ fields.streamFunction y (data.physicalTime τ))
        (dynamicReducedSimilarityPoint data x τ))
    (hlaws : SatisfiesDynamicScaleODEsAt data τ) :
    deriv (fun s ↦ dynamicallyRescaledSwirl data fields x s) τ +
      rescaledReducedAdvection
        (dynamicallyRescaledReducedFields data fields)
        data.spatialRate data.axialDrift
        (fun y ↦ dynamicallyRescaledSwirl data fields y τ) x τ =
      data.swirlScale τ ^ 2 *
          (deriv
              (fields.swirl (dynamicReducedSimilarityPoint data x τ))
              (data.physicalTime τ) +
            reducedAdvection fields
              (fun y ↦ fields.swirl y (data.physicalTime τ))
              (dynamicReducedSimilarityPoint data x τ)
              (data.physicalTime τ)) +
        data.swirlRate τ *
          dynamicallyRescaledSwirl data fields x τ := by
  have hswirl :
      DifferentiableAt ℝ (fun y ↦ fields.swirl y (data.physicalTime τ))
      (dynamicReducedSimilarityPoint data x τ) := by
    fun_prop
  rw [rescaledReducedAdvection_eq_modulation_add_reducedAdvection, ← add_assoc,
      deriv_dynamicallyRescaledSwirl_add_modulationAdvection data fields x τ hfield hlaws,
      reducedAdvection_dynamicallyRescaledSwirl data fields x τ hscale hstream hswirl]
  ring

/-- The time derivative plus full modulated advection of dynamically
rescaled vorticity is the physical material derivative with amplitude
`A Aω`, plus the linear amplitude-rate term. -/
theorem deriv_add_rescaledReducedAdvection_dynamicallyRescaledVorticity
    (data : DynamicRescalingData) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hscale : data.spatialScale τ ≠ 0)
    (hfield :
      DifferentiableAt ℝ (Function.uncurry fields.vorticity)
        (dynamicReducedSimilarityPoint data x τ, data.physicalTime τ))
    (hstream :
      DifferentiableAt ℝ
        (fun y ↦ fields.streamFunction y (data.physicalTime τ))
        (dynamicReducedSimilarityPoint data x τ))
    (hlaws : SatisfiesDynamicScaleODEsAt data τ) :
    deriv (fun s ↦ dynamicallyRescaledVorticity data fields x s) τ +
      rescaledReducedAdvection
        (dynamicallyRescaledReducedFields data fields)
        data.spatialRate data.axialDrift
        (fun y ↦ dynamicallyRescaledVorticity data fields y τ) x τ =
      (data.swirlScale τ * data.vorticityScale τ) *
          (deriv
              (fields.vorticity
                (dynamicReducedSimilarityPoint data x τ))
              (data.physicalTime τ) +
            reducedAdvection fields
              (fun y ↦ fields.vorticity y (data.physicalTime τ))
              (dynamicReducedSimilarityPoint data x τ)
              (data.physicalTime τ)) +
        data.vorticityRate τ *
          dynamicallyRescaledVorticity data fields x τ := by
  have hvorticity :
      DifferentiableAt ℝ (fun y ↦ fields.vorticity y (data.physicalTime τ))
      (dynamicReducedSimilarityPoint data x τ) := by
    fun_prop
  rw [rescaledReducedAdvection_eq_modulation_add_reducedAdvection, ← add_assoc,
      deriv_dynamicallyRescaledVorticity_add_modulationAdvection data fields x τ hfield
        hlaws,
      reducedAdvection_dynamicallyRescaledVorticity data fields x τ hscale hstream hvorticity]
  ring

end

end AxisymmetricFlow
