/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Axisymmetric.ReducedNavierStokes.RescaledSystem
public import PDE.Representations.Similarity.DynamicAffine

/-!
# Data and fields for dynamic axisymmetric rescaling

Let `A(τ)` be the reduced-swirl amplitude, `L(τ)` the common meridian
length scale, and `Z(τ)` an axial center.  The physical point represented by
the rescaled coordinate `x = (r,z)` is

```text
X(x,τ) = L(τ)x + Z(τ)e_z.
```

Compatibility of the two evolution equations and the elliptic equation fixes
the remaining scales:

```text
Aω = A L,        Aψ = A / L,
dt/dτ = A,       ν̃ = ν A / L².
```

Writing

```text
A' = cᵤ A,       L' = -λL,       Z' = -CL
```

then forces

```text
cω = cᵤ - λ,     ν̃' = (cᵤ + 2λ)ν̃.
```

We define the scale data, their pointwise ODE laws and the compatible field pullback, and we
show that the similarity point map preserves the positive-radius meridian. The spatial and
equation-level chain rules are in `DynamicRescaling.Calculus` and
`DynamicRescaling.Equations`. The fixed-rate specialisation `cᵤ = -1`, `cω = -(1 + λ)` is the
traveling ansatz of `TravelingWave`.

## Main definitions and results

* `DynamicRescalingData`: the scale functions `A`, `L`, `Aω`, `Z`, `t`, `ν̃` and the
  logarithmic rates `cᵤ`, `λ`, `cω`, `C` as functions of rescaled time `τ`.
* `SatisfiesDynamicScaleODEsAt`: the pointwise ODE laws `A' = cᵤA`, `L' = -λL`, `Aω' = cωAω`,
  `(Ze_z)' = -CLe_z`, `t' = A`, `ν̃' = (cᵤ + 2λ)ν̃` at one rescaled time.
* `SatisfiesDynamicRescalingLawsAt`: the ODE laws together with positivity of `A` and `L` and
  the algebraic compatibility relations `Aω = AL`, `ν̃ = νA/L²`, `cω = cᵤ - λ`.
* `dynamicReducedSimilarityPoint`, `dynamicallyRescaledReducedFields`: the physical point
  `Lx + Ze_z` and the pullback of a rescaled profile to physical reduced fields with the
  compatible amplitudes `A`, `AL`, `A/L`.
* `vorticityScaleDerivative_balance`, `streamFunctionScaleDerivative_balance`,
  `rescaledViscosityDerivative_balance`: the product and quotient rules showing that the
  compatibility relations are propagated by the ODE laws.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 2.1, (2.4)-(2.7), pp. 5-6,
  for dynamic rescaling, in which the amplitude and length scale of a possibly singular solution
  evolve by ODEs chosen to normalise the rescaled profile (there without an axial center).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

namespace AxisymmetricFlow

open PDE.Representations.Similarity

set_option linter.missingDocs true

noncomputable section

/-- Time-dependent scales, center, viscosity, and logarithmic rates for the
reduced axisymmetric dynamic rescaling. -/
structure DynamicRescalingData where
  /-- Reduced-swirl amplitude `A`. -/
  swirlScale : ℝ → ℝ
  /-- Common meridian spatial scale `L`. -/
  spatialScale : ℝ → ℝ
  /-- Reduced-vorticity amplitude `Aω`. -/
  vorticityScale : ℝ → ℝ
  /-- Physical axial center `Z`. -/
  axialCenter : ℝ → ℝ
  /-- Physical time `t(τ)`. -/
  physicalTime : ℝ → ℝ
  /-- Viscosity in rescaled coordinates. -/
  rescaledViscosity : ℝ → ℝ
  /-- Logarithmic reduced-swirl rate `cᵤ`. -/
  swirlRate : ℝ → ℝ
  /-- Negative logarithmic spatial rate `λ`. -/
  spatialRate : ℝ → ℝ
  /-- Axial transport drift `C`. -/
  axialDrift : ℝ → ℝ
  /-- Logarithmic reduced-vorticity rate `cω`. -/
  vorticityRate : ℝ → ℝ

/-- Differential scale laws at one rescaled time. -/
structure SatisfiesDynamicScaleODEsAt
    (data : DynamicRescalingData) (τ : ℝ) : Prop where
  /-- `A' = cᵤ A`. -/
  swirlScale_hasDerivAt :
    HasDerivAt data.swirlScale
      (data.swirlRate τ * data.swirlScale τ) τ
  /-- `L' = -λL`. -/
  spatialScale_hasDerivAt :
    HasDerivAt data.spatialScale
      (-data.spatialRate τ * data.spatialScale τ) τ
  /-- `Aω' = cω Aω`. -/
  vorticityScale_hasDerivAt :
    HasDerivAt data.vorticityScale
      (data.vorticityRate τ * data.vorticityScale τ) τ
  /-- `(Ze_z)' = -CL e_z`; this sign produces `+C∂_z` in rescaled
  transport. -/
  axialShift_hasDerivAt :
    HasDerivAt (fun s ↦ data.axialCenter s • axialUnit)
      ((-data.axialDrift τ * data.spatialScale τ) • axialUnit) τ
  /-- `t' = A`. -/
  physicalTime_hasDerivAt :
    HasDerivAt data.physicalTime (data.swirlScale τ) τ
  /-- `ν̃' = (cᵤ + 2λ)ν̃`. -/
  rescaledViscosity_hasDerivAt :
    HasDerivAt data.rescaledViscosity
      ((data.swirlRate τ + 2 * data.spatialRate τ) *
        data.rescaledViscosity τ) τ

/-- Full pointwise compatibility laws for a physical viscosity `ν`. -/
structure SatisfiesDynamicRescalingLawsAt
    (data : DynamicRescalingData) (physicalViscosity τ : ℝ)
    extends SatisfiesDynamicScaleODEsAt data τ where
  /-- Positive swirl scale preserves time orientation. -/
  swirlScale_pos : 0 < data.swirlScale τ
  /-- Positive spatial scale preserves the radial half-plane. -/
  spatialScale_pos : 0 < data.spatialScale τ
  /-- Elliptic/source compatibility `Aω = AL`. -/
  vorticityScale_eq :
    data.vorticityScale τ =
      data.swirlScale τ * data.spatialScale τ
  /-- Viscosity compatibility `ν̃ = νA/L²`. -/
  rescaledViscosity_eq :
    data.rescaledViscosity τ =
      physicalViscosity * data.swirlScale τ /
        data.spatialScale τ ^ 2
  /-- Logarithmic-rate compatibility `cω = cᵤ - λ`. -/
  vorticityRate_eq :
    data.vorticityRate τ =
      data.swirlRate τ - data.spatialRate τ

/-- Vector-valued axial shift `Z(τ)e_z`. -/
def dynamicAxialShift
    (data : DynamicRescalingData) (τ : ℝ) : ℝ^2 :=
  data.axialCenter τ • axialUnit

/-- Physical similarity point `L(τ)x + Z(τ)e_z`. -/
def dynamicReducedSimilarityPoint
    (data : DynamicRescalingData) (x : ℝ^2) (τ : ℝ) : ℝ^2 :=
  dynamicAffinePoint data.spatialScale (dynamicAxialShift data) x τ

/-- The radial coordinate of the physical similarity point is `Lr`. -/
@[simp]
theorem dynamicReducedSimilarityPoint_radial
    (data : DynamicRescalingData) (x : ℝ^2) (τ : ℝ) :
    dynamicReducedSimilarityPoint data x τ (0 : Fin 2) =
      data.spatialScale τ * x (0 : Fin 2) := by
  simp [dynamicReducedSimilarityPoint, dynamicAffinePoint,
    affineDilation, dynamicAxialShift, smul_eq_mul]

/-- The axial coordinate of the physical similarity point is `Lz + Z`. -/
@[simp]
theorem dynamicReducedSimilarityPoint_axial
    (data : DynamicRescalingData) (x : ℝ^2) (τ : ℝ) :
    dynamicReducedSimilarityPoint data x τ (1 : Fin 2) =
      data.spatialScale τ * x (1 : Fin 2) + data.axialCenter τ := by
  simp [dynamicReducedSimilarityPoint, dynamicAffinePoint,
    affineDilation, dynamicAxialShift, smul_eq_mul]

/-- Positive spatial scaling and axial translation preserve the open
positive-radius meridian. -/
theorem dynamicReducedSimilarityPoint_mem_positiveRadiusMeridian
    (data : DynamicRescalingData) {x : ℝ^2} {τ : ℝ}
    (hscale : 0 < data.spatialScale τ)
    (hx : x ∈ positiveRadiusMeridian) :
    dynamicReducedSimilarityPoint data x τ ∈ positiveRadiusMeridian := by
  rw [mem_positiveRadiusMeridian_iff] at hx ⊢
  rw [dynamicReducedSimilarityPoint_radial]
  exact mul_pos hscale hx

/-- Nonnegative spatial scaling and axial translation preserve the closed
nonnegative-radius meridian. -/
theorem dynamicReducedSimilarityPoint_mem_nonnegativeRadiusMeridian
    (data : DynamicRescalingData) {x : ℝ^2} {τ : ℝ}
    (hscale : 0 ≤ data.spatialScale τ)
    (hx : x ∈ nonnegativeRadiusMeridian) :
    dynamicReducedSimilarityPoint data x τ ∈ nonnegativeRadiusMeridian := by
  rw [mem_nonnegativeRadiusMeridian_iff] at hx ⊢
  rw [dynamicReducedSimilarityPoint_radial]
  exact mul_nonneg hscale hx

/-- Dynamically rescaled reduced swirl. -/
def dynamicallyRescaledSwirl
    (data : DynamicRescalingData) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ) : ℝ :=
  dynamicAffinePullback fields.swirl data.swirlScale data.spatialScale
    (dynamicAxialShift data) data.physicalTime x τ

/-- Dynamically rescaled reduced azimuthal vorticity. -/
def dynamicallyRescaledVorticity
    (data : DynamicRescalingData) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ) : ℝ :=
  dynamicAffinePullback fields.vorticity data.vorticityScale
    data.spatialScale (dynamicAxialShift data) data.physicalTime x τ

/-- Dynamically rescaled reduced streamfunction, with amplitude `A/L`. -/
def dynamicallyRescaledStreamFunction
    (data : DynamicRescalingData) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ) : ℝ :=
  (data.swirlScale τ / data.spatialScale τ) *
    fields.streamFunction (dynamicReducedSimilarityPoint data x τ)
      (data.physicalTime τ)

/-- All three dynamically rescaled reduced fields. -/
def dynamicallyRescaledReducedFields
    (data : DynamicRescalingData)
    (fields : ReducedFields) : ReducedFields where
  swirl := dynamicallyRescaledSwirl data fields
  vorticity := dynamicallyRescaledVorticity data fields
  streamFunction := dynamicallyRescaledStreamFunction data fields

/-- Under amplitude compatibility, the streamfunction amplitude `A/L`
equals the elliptically natural amplitude `Aω/L²`. -/
theorem streamFunctionScale_eq_vorticityScale_div_sq
    (data : DynamicRescalingData) (τ : ℝ)
    (hscale : data.spatialScale τ ≠ 0)
    (hcompat :
      data.vorticityScale τ =
        data.swirlScale τ * data.spatialScale τ) :
    data.swirlScale τ / data.spatialScale τ =
      data.vorticityScale τ / data.spatialScale τ ^ 2 := by
  rw [hcompat]
  field_simp

/-- The axial shift has derivative `-CL e_z` under the center ODE. -/
theorem hasDerivAt_dynamicAxialShift
    (data : DynamicRescalingData) (τ : ℝ)
    (hlaws : SatisfiesDynamicScaleODEsAt data τ) :
    HasDerivAt (dynamicAxialShift data)
      ((-data.axialDrift τ * data.spatialScale τ) • axialUnit) τ := by
  exact hlaws.axialShift_hasDerivAt

/-- Product-rule balance behind the compatible vorticity rate:
`(AL)' = (cᵤ-λ)AL` when `A' = cᵤA` and `L' = -λL`. -/
theorem vorticityScaleDerivative_balance
    (swirlScale spatialScale swirlRate spatialRate : ℝ) :
    (swirlRate * swirlScale) * spatialScale +
        swirlScale * (-spatialRate * spatialScale) =
      (swirlRate - spatialRate) *
        (swirlScale * spatialScale) := by
  ring

/-- Quotient-rule balance behind the streamfunction-amplitude rate:
`(A/L)' = (cᵤ+λ)A/L`. -/
theorem streamFunctionScaleDerivative_balance
    (swirlScale spatialScale swirlRate spatialRate : ℝ)
    (hscale : spatialScale ≠ 0) :
    ((swirlRate * swirlScale) * spatialScale -
          swirlScale * (-spatialRate * spatialScale)) /
        spatialScale ^ 2 =
      (swirlRate + spatialRate) *
        (swirlScale / spatialScale) := by
  field_simp
  ring

/-- Quotient-rule balance behind the rescaled-viscosity rate:
`(νA/L²)' = (cᵤ+2λ)νA/L²`. -/
theorem rescaledViscosityDerivative_balance
    (physicalViscosity swirlScale spatialScale
      swirlRate spatialRate : ℝ)
    (hscale : spatialScale ≠ 0) :
    ((physicalViscosity * (swirlRate * swirlScale)) *
          spatialScale ^ 2 -
        (physicalViscosity * swirlScale) *
          (2 * spatialScale * (-spatialRate * spatialScale))) /
        (spatialScale ^ 2) ^ 2 =
      (swirlRate + 2 * spatialRate) *
        (physicalViscosity * swirlScale / spatialScale ^ 2) := by
  field_simp
  ring

end

end AxisymmetricFlow
