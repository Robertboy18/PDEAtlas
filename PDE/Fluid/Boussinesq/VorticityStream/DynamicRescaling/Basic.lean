/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.VorticityStream.RescaledSystem
public import PDE.Representations.Similarity.Dynamic

/-!
# Data and fields for dynamic Boussinesq rescaling

`DynamicRescalingData` holds the time-dependent scales `Cω`, `Cl`, `Cθ`, the clock `t(τ)` and
their logarithmic rates, and `dynamicallyRescaledFields` is the pullback of the physical
vorticity–streamfunction variables. The differential scale laws (`SatisfiesDynamicScaleODEsAt`)
are kept separate from positivity and amplitude compatibility
(`SatisfiesDynamicRescalingLawsAt`): the former drive the chain rule, while the latter are
needed by the upper-half-plane and source-term transformations.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 2.1, (2.4)-(2.7).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

namespace Boussinesq

open IncompressibleFlow
open PDE.Representations.Similarity

set_option linter.missingDocs true

noncomputable section

/-- Time-dependent scales, physical time, and logarithmic rates for the
Boussinesq dynamic rescaling. -/
structure DynamicRescalingData where
  /-- Vorticity amplitude `Cω`. -/
  vorticityScale : ℝ → ℝ
  /-- Spatial scale `Cl`. -/
  spatialScale : ℝ → ℝ
  /-- Temperature amplitude `Cθ`. -/
  temperatureScale : ℝ → ℝ
  /-- Physical time `t(τ)`. -/
  physicalTime : ℝ → ℝ
  /-- Logarithmic vorticity rate `cω`. -/
  vorticityRate : ℝ → ℝ
  /-- Negative logarithmic spatial rate `cl`. -/
  spatialRate : ℝ → ℝ
  /-- Logarithmic temperature rate `cθ`. -/
  temperatureRate : ℝ → ℝ

/-- Differential scale laws at one rescaled time. These are the hypotheses
needed by the chain rule, before imposing source-amplitude compatibility. -/
structure SatisfiesDynamicScaleODEsAt
    (data : DynamicRescalingData) (τ : ℝ) : Prop where
  /-- `Cω' = cω Cω`. -/
  vorticityScale_hasDerivAt :
    HasDerivAt data.vorticityScale
      (data.vorticityRate τ * data.vorticityScale τ) τ
  /-- `Cl' = -cl Cl`. -/
  spatialScale_hasDerivAt :
    HasDerivAt data.spatialScale
      (-data.spatialRate τ * data.spatialScale τ) τ
  /-- `Cθ' = cθ Cθ`. -/
  temperatureScale_hasDerivAt :
    HasDerivAt data.temperatureScale
      (data.temperatureRate τ * data.temperatureScale τ) τ
  /-- `t' = Cω`. -/
  physicalTime_hasDerivAt :
    HasDerivAt data.physicalTime (data.vorticityScale τ) τ

/-- Chen–Hou scale laws at one rescaled time. The amplitude identity is the
compatibility needed to transform the vorticity source term; it follows from
the integrated scales with compatible initial values. The rate identity is
equation (2.7) of Chen and Hou, Part I, and is also used by the normalization. -/
structure SatisfiesDynamicRescalingLawsAt
    (data : DynamicRescalingData) (τ : ℝ)
    extends SatisfiesDynamicScaleODEsAt data τ where
  /-- The spatial scale is positive, so dilation preserves the upper half-plane. -/
  spatialScale_pos : 0 < data.spatialScale τ
  /-- Source amplitudes agree: `Cθ Cl = Cω²`. -/
  sourceScale_eq :
    data.temperatureScale τ * data.spatialScale τ =
      data.vorticityScale τ ^ 2
  /-- Rate compatibility `cθ = cl + 2cω`. This is recorded explicitly:
  pointwise equality of the amplitudes alone does not imply an equality of
  their logarithmic derivatives. -/
  temperatureRate_eq :
    data.temperatureRate τ =
      data.spatialRate τ + 2 * data.vorticityRate τ

/-- Similarity point `Cl(τ)x` in physical coordinates. -/
def dynamicSimilarityPoint
    (data : DynamicRescalingData) (x : ℝ^2) (τ : ℝ) : ℝ^2 :=
  data.spatialScale τ • x

/-- Dynamically rescaled vorticity. -/
def rescaledVorticity
    (data : DynamicRescalingData)
    (fields : VorticityStreamFields) (x : ℝ^2) (τ : ℝ) : ℝ :=
  dynamicPullback fields.vorticity data.vorticityScale
    data.spatialScale data.physicalTime x τ

/-- Dynamically rescaled temperature. -/
def rescaledTemperature
    (data : DynamicRescalingData)
    (fields : VorticityStreamFields) (x : ℝ^2) (τ : ℝ) : ℝ :=
  dynamicPullback fields.temperature data.temperatureScale
    data.spatialScale data.physicalTime x τ

/-- Dynamically rescaled streamfunction. -/
def rescaledStreamFunction
    (data : DynamicRescalingData)
    (fields : VorticityStreamFields) (x : ℝ^2) (τ : ℝ) : ℝ :=
  (data.vorticityScale τ / data.spatialScale τ ^ 2) *
    fields.streamFunction (dynamicSimilarityPoint data x τ)
      (data.physicalTime τ)

/-- All three dynamically rescaled fields. -/
def dynamicallyRescaledFields
    (data : DynamicRescalingData)
    (fields : VorticityStreamFields) : VorticityStreamFields where
  vorticity := rescaledVorticity data fields
  temperature := rescaledTemperature data fields
  streamFunction := rescaledStreamFunction data fields

/-- The rescaled vorticity, temperature, streamfunction, and boundary
equations all hold on the prescribed rescaled times. -/
def SatisfiesDynamicRescaledSystemOn
    (data : DynamicRescalingData)
    (fields : VorticityStreamFields) (rescaledTimes : Set ℝ) : Prop :=
  SatisfiesRescaledScalarEquationsOn
      (dynamicallyRescaledFields data fields)
      data.spatialRate data.vorticityRate data.temperatureRate
      upperHalfPlane rescaledTimes ∧
    SatisfiesStreamFunctionEquationOn
      (dynamicallyRescaledFields data fields) rescaledTimes ∧
    HasZeroStreamFunctionBoundaryOn
      (dynamicallyRescaledFields data fields) rescaledTimes

namespace SatisfiesDynamicRescaledSystemOn

/-- Extract the rescaled vorticity and temperature equations. -/
theorem scalar_equations
    {data : DynamicRescalingData}
    {fields : VorticityStreamFields} {rescaledTimes : Set ℝ}
    (h : SatisfiesDynamicRescaledSystemOn data fields rescaledTimes) :
    SatisfiesRescaledScalarEquationsOn
      (dynamicallyRescaledFields data fields)
      data.spatialRate data.vorticityRate data.temperatureRate
      upperHalfPlane rescaledTimes :=
  h.1

/-- Extract the rescaled Dirichlet Poisson equation. -/
theorem streamFunction_equation
    {data : DynamicRescalingData}
    {fields : VorticityStreamFields} {rescaledTimes : Set ℝ}
    (h : SatisfiesDynamicRescaledSystemOn data fields rescaledTimes) :
    SatisfiesStreamFunctionEquationOn
      (dynamicallyRescaledFields data fields) rescaledTimes :=
  h.2.1

/-- Extract the zero horizontal boundary trace of the rescaled streamfunction. -/
theorem zero_streamFunction_boundary
    {data : DynamicRescalingData}
    {fields : VorticityStreamFields} {rescaledTimes : Set ℝ}
    (h : SatisfiesDynamicRescaledSystemOn data fields rescaledTimes) :
    HasZeroStreamFunctionBoundaryOn
      (dynamicallyRescaledFields data fields) rescaledTimes :=
  h.2.2

end SatisfiesDynamicRescaledSystemOn

/-- Positive spatial dilation preserves the open upper half-plane. -/
theorem dynamicSimilarityPoint_mem_upperHalfPlane
    (data : DynamicRescalingData) {x : ℝ^2} {τ : ℝ}
    (hscale : 0 < data.spatialScale τ)
    (hx : x ∈ upperHalfPlane) :
    dynamicSimilarityPoint data x τ ∈ upperHalfPlane := by
  change 0 < (data.spatialScale τ • x) 1
  simpa using mul_pos hscale hx

/-- The physical point of `C_l⁻¹ w` is `w`. -/
theorem dynamicSimilarityPoint_inv_smul (data : DynamicRescalingData) {τ : ℝ}
    (hscale : data.spatialScale τ ≠ 0) (w : ℝ^2) :
    dynamicSimilarityPoint data ((data.spatialScale τ)⁻¹ • w) τ = w := by
  simp [dynamicSimilarityPoint, smul_smul, hscale]

end

end Boussinesq
