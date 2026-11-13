/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Axisymmetric.ReducedNavierStokes.DynamicRescaling.Calculus
public import PDE.Fluid.Axisymmetric.ReducedNavierStokes.DynamicRescaling.ScaleRates
import PDE.FDeriv.Calculus

/-!
# Dynamic rescaling with variable convection strength

The parameter `eps` multiplies physical meridian advection only. The affine
frame velocity, stretching terms, and elliptic equation keep their original
coefficients. All fields are real-valued functions on the meridian plane and time.

We use the forward pullback: `u = A u_phys(Lx + Ze_z, t(τ))`,
`ω = Aω ω_phys(Lx + Ze_z, t(τ))`, and `ψ = (A/L) ψ_phys(Lx + Ze_z, t(τ))`.
The scale compatibility is `Aω = AL`, and the physical clock satisfies `t' = A`.

The main theorem transports both evolution equations and the axis-extended
elliptic equation on any mapped domain. It derives `cω = cu - λ` by differentiating the local
scale identity. Its inputs are the physical equations, field regularity,
and the five inviscid scale and clock laws; no rescaled equation or rate
compatibility is an input.

The axis-inclusive theorem uses the extended stream operator on both sides,
with value `4∂rr + ∂zz` at `r = 0`. Its domain may meet the axis. Radial parity
and smooth physical reconstruction are separate from this residual identity.

## Main results

* `convectionRescaledReducedSwirlResidual_dynamicallyRescaledReducedFields`,
  `convectionRescaledReducedVorticityResidual_dynamicallyRescaledReducedFields`: the rescaled
  residuals are `A²` and `A Aω` times the physical ones.
* `satisfiesAxisExtendedConvectionRescaledResidualSystemOn_of_scale_compatibility`: the
  axis-inclusive transport of the physical system, with `cω = cu - λ` derived.
* `satisfiesConvectionRescaledReducedSystemOn_of_scale_compatibility`: the same on
  positive-radius domains with the ordinary stream operator.
-/

@[expose] public section

open PDE (advectiveDerivative)

namespace AxisymmetricFlow

open PDE.Common
open scoped Topology

noncomputable section

/-- Advection by the moving frame plus `eps` times the reconstructed physical
meridian velocity. In coordinates its coefficients are `λr + eps*u_r` and
`λz + C + eps*u_z`. -/
def convectionRescaledReducedAdvection
    (eps : ℝ) (fields : ReducedFields)
    (spatialRate axialDrift : ℝ → ℝ)
    (f : ℝ^2 → ℝ) (x : ℝ^2) (τ : ℝ) : ℝ :=
  advectiveDerivative
      (fun y ↦ spatialRate τ • y + axialDrift τ • axialUnit) f x +
    eps * reducedAdvection fields f x τ

/-- The swirl pullback chain rule with arbitrary convection strength.
Only physical meridian advection acquires the coefficient `eps`. -/
theorem deriv_add_convectionRescaledReducedAdvection_dynamicallyRescaledSwirl
    (eps : ℝ) (data : DynamicRescalingData) (fields : ReducedFields)
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
      convectionRescaledReducedAdvection eps
        (dynamicallyRescaledReducedFields data fields)
        data.spatialRate data.axialDrift
        (fun y ↦ dynamicallyRescaledSwirl data fields y τ) x τ =
      data.swirlScale τ ^ 2 *
          (deriv
              (fields.swirl (dynamicReducedSimilarityPoint data x τ))
              (data.physicalTime τ) +
            eps * reducedAdvection fields
              (fun y ↦ fields.swirl y (data.physicalTime τ))
              (dynamicReducedSimilarityPoint data x τ)
              (data.physicalTime τ)) +
        data.swirlRate τ * dynamicallyRescaledSwirl data fields x τ := by
  have hswirl :
      DifferentiableAt ℝ (fun y ↦ fields.swirl y (data.physicalTime τ))
        (dynamicReducedSimilarityPoint data x τ) :=
    hfield.comp (f := fun y : ℝ^2 ↦ (y, data.physicalTime τ))
      (dynamicReducedSimilarityPoint data x τ)
      (differentiableAt_id.prodMk (differentiableAt_const _))
  unfold convectionRescaledReducedAdvection
  rw [← add_assoc,
    deriv_dynamicallyRescaledSwirl_add_modulationAdvection data fields x τ hfield hlaws,
    reducedAdvection_dynamicallyRescaledSwirl data fields x τ hscale hstream hswirl]
  ring

/-- Coordinate form of transport: `eps` multiplies the reconstructed velocity,
while the coordinate-frame terms retain coefficients `λ` and `C`. -/
theorem convectionRescaledReducedAdvection_eq
    (eps : ℝ) (fields : ReducedFields)
    (spatialRate axialDrift : ℝ → ℝ)
    (f : ℝ^2 → ℝ) (x : ℝ^2) (τ : ℝ) :
    convectionRescaledReducedAdvection eps fields spatialRate axialDrift f x τ =
      (spatialRate τ * x (0 : Fin 2) +
          eps * reducedRadialVelocity fields x τ) *
          (∂[(0 : Fin 2)] f) x +
        (spatialRate τ * x (1 : Fin 2) + axialDrift τ +
          eps * reducedAxialVelocity fields x τ) *
          (∂[(1 : Fin 2)] f) x := by
  unfold convectionRescaledReducedAdvection
  rw [PDE.advectiveDerivative_eq_sum_mul_partialDeriv, reducedAdvection_eq]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Fin.sum_univ_two, Fin.isValue,
    axialUnit_apply_zero, mul_zero, add_zero, axialUnit_apply_one, mul_one]
  ring

/-- The vorticity pullback has transport amplitude `A Aω` for every convection
strength. The amplitude rate contributes the separate term `cω ω̃`. -/
theorem deriv_add_convectionRescaledReducedAdvection_dynamicallyRescaledVorticity
    (eps : ℝ) (data : DynamicRescalingData) (fields : ReducedFields)
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
      convectionRescaledReducedAdvection eps
        (dynamicallyRescaledReducedFields data fields)
        data.spatialRate data.axialDrift
        (fun y ↦ dynamicallyRescaledVorticity data fields y τ) x τ =
      (data.swirlScale τ * data.vorticityScale τ) *
          (deriv
              (fields.vorticity (dynamicReducedSimilarityPoint data x τ))
              (data.physicalTime τ) +
            eps * reducedAdvection fields
              (fun y ↦ fields.vorticity y (data.physicalTime τ))
              (dynamicReducedSimilarityPoint data x τ)
              (data.physicalTime τ)) +
        data.vorticityRate τ * dynamicallyRescaledVorticity data fields x τ := by
  have hvorticity :
      DifferentiableAt ℝ (fun y ↦ fields.vorticity y (data.physicalTime τ))
        (dynamicReducedSimilarityPoint data x τ) :=
    hfield.comp (f := fun y : ℝ^2 ↦ (y, data.physicalTime τ))
      (dynamicReducedSimilarityPoint data x τ)
      (differentiableAt_id.prodMk (differentiableAt_const _))
  unfold convectionRescaledReducedAdvection
  rw [← add_assoc,
    deriv_dynamicallyRescaledVorticity_add_modulationAdvection data fields x τ hfield
      hlaws,
    reducedAdvection_dynamicallyRescaledVorticity data fields x τ hscale hstream hvorticity]
  ring

/-- Defect in `∂t u + eps (u_r ∂r u + u_z ∂z u) = 2u ∂z ψ`.
The stretching source is independent of `eps`. -/
def convectionReducedSwirlResidual
    (eps : ℝ) (fields : ReducedFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  deriv (fields.swirl x) t +
      eps * reducedAdvection fields (fun y ↦ fields.swirl y t) x t -
    reducedSwirlSource fields x t

/-- Defect in `∂t ω + eps (u_r ∂r ω + u_z ∂z ω) = 2u ∂z u`. -/
def convectionReducedVorticityResidual
    (eps : ℝ) (fields : ReducedFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  deriv (fields.vorticity x) t +
      eps * reducedAdvection fields (fun y ↦ fields.vorticity y t) x t -
    reducedVorticitySource fields x t

/-- Defect in the dynamically rescaled swirl equation, with stretching source
`2u ∂z ψ` and amplitude-rate term `cu u`. -/
def convectionRescaledReducedSwirlResidual
    (eps : ℝ) (fields : ReducedFields)
    (spatialRate axialDrift swirlRate : ℝ → ℝ)
    (x : ℝ^2) (τ : ℝ) : ℝ :=
  deriv (fields.swirl x) τ +
      convectionRescaledReducedAdvection eps fields spatialRate axialDrift
        (fun y ↦ fields.swirl y τ) x τ -
    (reducedSwirlSource fields x τ + swirlRate τ * fields.swirl x τ)

/-- Defect in the dynamically rescaled vorticity equation, with source
`2u ∂z u` and independently specified amplitude-rate term `cω ω`. -/
def convectionRescaledReducedVorticityResidual
    (eps : ℝ) (fields : ReducedFields)
    (spatialRate axialDrift vorticityRate : ℝ → ℝ)
    (x : ℝ^2) (τ : ℝ) : ℝ :=
  deriv (fields.vorticity x) τ +
      convectionRescaledReducedAdvection eps fields spatialRate axialDrift
        (fun y ↦ fields.vorticity y τ) x τ -
    (reducedVorticitySource fields x τ + vorticityRate τ * fields.vorticity x τ)

/-- The inviscid physical system with variable convection strength and the ordinary
reduced elliptic equation `-Eψ = ω`. This predicate imposes no radius restriction
and retains the ordinary operator even at `r = 0`. For domains meeting the axis,
use `SatisfiesAxisExtendedConvectionResidualSystemOn`. -/
def SatisfiesConvectionReducedSystemOn
    (eps : ℝ) (fields : ReducedFields)
    (domain : Set (ℝ^2)) (times : Set ℝ) : Prop :=
  (∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ domain → t ∈ times →
    convectionReducedSwirlResidual eps fields x t = 0) ∧
  (∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ domain → t ∈ times →
    convectionReducedVorticityResidual eps fields x t = 0) ∧
  SatisfiesReducedStreamFunctionEquationOn fields domain times

/-- All three dynamically rescaled equations using the ordinary elliptic operator,
including at `r = 0`; this predicate imposes no radius restriction. For domains
meeting the axis, use `SatisfiesAxisExtendedConvectionRescaledResidualSystemOn`.
Rate compatibility is independent of this predicate and is derived from the
amplitude laws in the transformation theorem. -/
def SatisfiesConvectionRescaledReducedSystemOn
    (eps : ℝ) (fields : ReducedFields)
    (spatialRate axialDrift swirlRate vorticityRate : ℝ → ℝ)
    (domain : Set (ℝ^2)) (times : Set ℝ) : Prop :=
  (∀ ⦃x : ℝ^2⦄ ⦃τ : ℝ⦄, x ∈ domain → τ ∈ times →
    convectionRescaledReducedSwirlResidual eps fields
      spatialRate axialDrift swirlRate x τ = 0) ∧
  (∀ ⦃x : ℝ^2⦄ ⦃τ : ℝ⦄, x ∈ domain → τ ∈ times →
    convectionRescaledReducedVorticityResidual eps fields
      spatialRate axialDrift vorticityRate x τ = 0) ∧
  SatisfiesReducedStreamFunctionEquationOn fields domain times

/-- The swirl residual of the pullback is `A²` times its physical
counterpart. No scale compatibility or physical PDE is assumed. -/
theorem convectionRescaledReducedSwirlResidual_dynamicallyRescaledReducedFields
    (eps : ℝ) (data : DynamicRescalingData) (fields : ReducedFields)
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
    convectionRescaledReducedSwirlResidual eps
        (dynamicallyRescaledReducedFields data fields)
        data.spatialRate data.axialDrift data.swirlRate x τ =
      data.swirlScale τ ^ 2 *
        convectionReducedSwirlResidual eps fields
          (dynamicReducedSimilarityPoint data x τ) (data.physicalTime τ) := by
  unfold convectionRescaledReducedSwirlResidual convectionReducedSwirlResidual
  rw [show (dynamicallyRescaledReducedFields data fields).swirl =
      dynamicallyRescaledSwirl data fields from rfl,
    deriv_add_convectionRescaledReducedAdvection_dynamicallyRescaledSwirl
      eps data fields x τ hscale hfield hstream hlaws,
    reducedSwirlSource_dynamicallyRescaledReducedFields data fields x τ hscale hstream]
  ring

/-- Under `Aω = AL`, the vorticity residual of the pullback is
`A Aω` times the physical residual. This uses the source scaling as well as
the time and space chain rules. -/
theorem convectionRescaledReducedVorticityResidual_dynamicallyRescaledReducedFields
    (eps : ℝ) (data : DynamicRescalingData) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hscale : data.spatialScale τ ≠ 0)
    (hcompat : data.vorticityScale τ = data.swirlScale τ * data.spatialScale τ)
    (hfield :
      DifferentiableAt ℝ (Function.uncurry fields.vorticity)
        (dynamicReducedSimilarityPoint data x τ, data.physicalTime τ))
    (hswirl :
      DifferentiableAt ℝ
        (fun y ↦ fields.swirl y (data.physicalTime τ))
        (dynamicReducedSimilarityPoint data x τ))
    (hstream :
      DifferentiableAt ℝ
        (fun y ↦ fields.streamFunction y (data.physicalTime τ))
        (dynamicReducedSimilarityPoint data x τ))
    (hlaws : SatisfiesDynamicScaleODEsAt data τ) :
    convectionRescaledReducedVorticityResidual eps
        (dynamicallyRescaledReducedFields data fields)
        data.spatialRate data.axialDrift data.vorticityRate x τ =
      (data.swirlScale τ * data.vorticityScale τ) *
        convectionReducedVorticityResidual eps fields
          (dynamicReducedSimilarityPoint data x τ) (data.physicalTime τ) := by
  unfold convectionRescaledReducedVorticityResidual convectionReducedVorticityResidual
  rw [show (dynamicallyRescaledReducedFields data fields).vorticity =
      dynamicallyRescaledVorticity data fields from rfl,
    deriv_add_convectionRescaledReducedAdvection_dynamicallyRescaledVorticity
      eps data fields x τ hscale hfield hstream hlaws,
    reducedVorticitySource_dynamicallyRescaledReducedFields_compatible
      data fields x τ hcompat hswirl]
  ring

/-- The physical convection-varied residual system with the axis-extended
stream operator. At `r = 0` that operator is `4∂rr + ∂zz`. Radial parity and
the regularity needed to interpret this value as a limit are separate properties. -/
def SatisfiesAxisExtendedConvectionResidualSystemOn
    (eps : ℝ) (fields : ReducedFields)
    (domain : Set (ℝ^2)) (times : Set ℝ) : Prop :=
  (∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ domain → t ∈ times →
    convectionReducedSwirlResidual eps fields x t = 0) ∧
  (∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ domain → t ∈ times →
    convectionReducedVorticityResidual eps fields x t = 0) ∧
  (∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ domain → t ∈ times →
    axisExtendedReducedStreamFunctionResidual fields x t = 0)

/-- The dynamically rescaled convection-varied residual system, including the
axis value `4∂rr ψ + ∂zz ψ` in the elliptic equation. The evolution residuals
are the same on and off the axis. Neither radial parity nor a rate relation is part of the
predicate. -/
def SatisfiesAxisExtendedConvectionRescaledResidualSystemOn
    (eps : ℝ) (fields : ReducedFields)
    (spatialRate axialDrift swirlRate vorticityRate : ℝ → ℝ)
    (domain : Set (ℝ^2)) (times : Set ℝ) : Prop :=
  (∀ ⦃x : ℝ^2⦄ ⦃τ : ℝ⦄, x ∈ domain → τ ∈ times →
    convectionRescaledReducedSwirlResidual eps fields
      spatialRate axialDrift swirlRate x τ = 0) ∧
  (∀ ⦃x : ℝ^2⦄ ⦃τ : ℝ⦄, x ∈ domain → τ ∈ times →
    convectionRescaledReducedVorticityResidual eps fields
      spatialRate axialDrift vorticityRate x τ = 0) ∧
  (∀ ⦃x : ℝ^2⦄ ⦃τ : ℝ⦄, x ∈ domain → τ ∈ times →
    axisExtendedReducedStreamFunctionResidual fields x τ = 0)

/-- All three physical equations with the extended axis value transport under
the dynamic pullback, and the vorticity-rate relation is derived.

The domains may contain the axis. The physical elliptic premise uses the same
axis-extended operator as the conclusion; an ordinary off-axis residual cannot
replace it at `r = 0`. Neighborhood scale compatibility supplies differentiation
of `Aω = AL`, while the streamfunction's spatial C² regularity supplies the
second-derivative chain rule. Radial parity and a smooth three-dimensional lift are
separate questions. -/
theorem satisfiesAxisExtendedConvectionRescaledResidualSystemOn_of_scale_compatibility
    (eps : ℝ) (data : DynamicRescalingData) (fields : ReducedFields)
    (physicalDomain rescaledDomain : Set (ℝ^2))
    (physicalTimes rescaledTimes : Set ℝ)
    (hphysical :
      SatisfiesAxisExtendedConvectionResidualSystemOn eps fields
        physicalDomain physicalTimes)
    (hmap :
      ∀ ⦃x : ℝ^2⦄ ⦃τ : ℝ⦄, x ∈ rescaledDomain → τ ∈ rescaledTimes →
        dynamicReducedSimilarityPoint data x τ ∈ physicalDomain ∧
          data.physicalTime τ ∈ physicalTimes)
    (hswirl_pos :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes → 0 < data.swirlScale τ)
    (hspatial_pos :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes → 0 < data.spatialScale τ)
    (hswirlScale :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        HasDerivAt data.swirlScale (data.swirlRate τ * data.swirlScale τ) τ)
    (hspatialScale :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        HasDerivAt data.spatialScale (-data.spatialRate τ * data.spatialScale τ) τ)
    (hvorticityScale :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        HasDerivAt data.vorticityScale (data.vorticityRate τ * data.vorticityScale τ) τ)
    (hcenter :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        HasDerivAt (fun s ↦ data.axialCenter s • axialUnit)
          ((-data.axialDrift τ * data.spatialScale τ) • axialUnit) τ)
    (hclock :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        HasDerivAt data.physicalTime (data.swirlScale τ) τ)
    (hcompat :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        data.vorticityScale =ᶠ[𝓝 τ] fun s ↦ data.swirlScale s * data.spatialScale s)
    (hswirl :
      ∀ ⦃x : ℝ^2⦄ ⦃τ : ℝ⦄, x ∈ rescaledDomain → τ ∈ rescaledTimes →
        DifferentiableAt ℝ (Function.uncurry fields.swirl)
          (dynamicReducedSimilarityPoint data x τ, data.physicalTime τ))
    (hvorticity :
      ∀ ⦃x : ℝ^2⦄ ⦃τ : ℝ⦄, x ∈ rescaledDomain → τ ∈ rescaledTimes →
        DifferentiableAt ℝ (Function.uncurry fields.vorticity)
          (dynamicReducedSimilarityPoint data x τ, data.physicalTime τ))
    (hstream :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        ContDiff ℝ 2 (fun y ↦ fields.streamFunction y (data.physicalTime τ))) :
    SatisfiesAxisExtendedConvectionRescaledResidualSystemOn eps
        (dynamicallyRescaledReducedFields data fields)
        data.spatialRate data.axialDrift data.swirlRate data.vorticityRate
        rescaledDomain rescaledTimes ∧
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        data.vorticityRate τ = data.swirlRate τ - data.spatialRate τ := by
  let inviscidData : DynamicRescalingData :=
    { data with rescaledViscosity := fun _ ↦ 0 }
  have hodes ⦃τ : ℝ⦄ (hτ : τ ∈ rescaledTimes) :
      SatisfiesDynamicScaleODEsAt inviscidData τ := by
    refine
      { swirlScale_hasDerivAt := hswirlScale hτ
        spatialScale_hasDerivAt := hspatialScale hτ
        vorticityScale_hasDerivAt := hvorticityScale hτ
        axialShift_hasDerivAt := hcenter hτ
        physicalTime_hasDerivAt := hclock hτ
        rescaledViscosity_hasDerivAt := ?_ }
    simpa [inviscidData] using (hasDerivAt_const τ (0 : ℝ))
  have hrate ⦃τ : ℝ⦄ (hτ : τ ∈ rescaledTimes) :
      data.vorticityRate τ = data.swirlRate τ - data.spatialRate τ :=
    (hodes hτ).vorticityRate_eq_of_scale_compatibility
      (hswirl_pos hτ).ne' (hspatial_pos hτ).ne' (hcompat hτ)
  have hswirlSpatial ⦃x : ℝ^2⦄ ⦃τ : ℝ⦄
      (hx : x ∈ rescaledDomain) (hτ : τ ∈ rescaledTimes) :
      DifferentiableAt ℝ (fun y ↦ fields.swirl y (data.physicalTime τ))
        (dynamicReducedSimilarityPoint data x τ) :=
    (hswirl hx hτ).comp (f := fun y : ℝ^2 ↦ (y, data.physicalTime τ))
      (dynamicReducedSimilarityPoint data x τ)
      (differentiableAt_id.prodMk (differentiableAt_const _))
  rcases hphysical with ⟨hphysicalSwirl, hphysicalVorticity, hphysicalStream⟩
  refine ⟨⟨fun x τ hx hτ ↦ ?_, fun x τ hx hτ ↦ ?_, fun x τ hx hτ ↦ ?_⟩, hrate⟩
  · exact (convectionRescaledReducedSwirlResidual_dynamicallyRescaledReducedFields eps
      inviscidData fields x τ (hspatial_pos hτ).ne' (hswirl hx hτ)
      ((hstream hτ).differentiable (by norm_num)).differentiableAt (hodes hτ)).trans
      (mul_eq_zero_of_right _ (hphysicalSwirl (hmap hx hτ).1 (hmap hx hτ).2))
  · exact (convectionRescaledReducedVorticityResidual_dynamicallyRescaledReducedFields eps
      inviscidData fields x τ (hspatial_pos hτ).ne' (hcompat hτ).eq_of_nhds
      (hvorticity hx hτ) (hswirlSpatial hx hτ)
      ((hstream hτ).differentiable (by norm_num)).differentiableAt (hodes hτ)).trans
      (mul_eq_zero_of_right _ (hphysicalVorticity (hmap hx hτ).1 (hmap hx hτ).2))
  · rw [axisExtendedReducedStreamFunctionResidual_dynamicallyRescaledReducedFields
      data fields x τ (hstream hτ) (hspatial_pos hτ).ne' (hcompat hτ).eq_of_nhds,
      hphysicalStream (hmap hx hτ).1 (hmap hx hτ).2, mul_zero]

/-- The three physical equations transport to the dynamic system for arbitrary
real `eps`, and differentiating `Aω = AL` derives `cω = cu - λ`.

The compatibility identity holds on a neighborhood of each rescaled time.
Joint differentiability supplies spatial derivatives of swirl and vorticity;
only the streamfunction needs two spatial derivatives. The five inviscid
scale and clock laws suffice, with no viscosity hypothesis. Positive spatial
scaling preserves positive radius, so this follows from the axis-inclusive
theorem after restricting the physical domain and identifying the two operators. -/
theorem satisfiesConvectionRescaledReducedSystemOn_of_scale_compatibility
    (eps : ℝ) (data : DynamicRescalingData) (fields : ReducedFields)
    (physicalDomain rescaledDomain : Set (ℝ^2))
    (physicalTimes rescaledTimes : Set ℝ)
    (hphysical :
      SatisfiesConvectionReducedSystemOn eps fields physicalDomain physicalTimes)
    (hdomain : rescaledDomain ⊆ positiveRadiusMeridian)
    (hmap :
      ∀ ⦃x : ℝ^2⦄ ⦃τ : ℝ⦄, x ∈ rescaledDomain → τ ∈ rescaledTimes →
        dynamicReducedSimilarityPoint data x τ ∈ physicalDomain ∧
          data.physicalTime τ ∈ physicalTimes)
    (hswirl_pos :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes → 0 < data.swirlScale τ)
    (hspatial_pos :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes → 0 < data.spatialScale τ)
    (hswirlScale :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        HasDerivAt data.swirlScale (data.swirlRate τ * data.swirlScale τ) τ)
    (hspatialScale :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        HasDerivAt data.spatialScale (-data.spatialRate τ * data.spatialScale τ) τ)
    (hvorticityScale :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        HasDerivAt data.vorticityScale (data.vorticityRate τ * data.vorticityScale τ) τ)
    (hcenter :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        HasDerivAt (fun s ↦ data.axialCenter s • axialUnit)
          ((-data.axialDrift τ * data.spatialScale τ) • axialUnit) τ)
    (hclock :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        HasDerivAt data.physicalTime (data.swirlScale τ) τ)
    (hcompat :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        data.vorticityScale =ᶠ[𝓝 τ] fun s ↦ data.swirlScale s * data.spatialScale s)
    (hswirl :
      ∀ ⦃x : ℝ^2⦄ ⦃τ : ℝ⦄, x ∈ rescaledDomain → τ ∈ rescaledTimes →
        DifferentiableAt ℝ (Function.uncurry fields.swirl)
          (dynamicReducedSimilarityPoint data x τ, data.physicalTime τ))
    (hvorticity :
      ∀ ⦃x : ℝ^2⦄ ⦃τ : ℝ⦄, x ∈ rescaledDomain → τ ∈ rescaledTimes →
        DifferentiableAt ℝ (Function.uncurry fields.vorticity)
          (dynamicReducedSimilarityPoint data x τ, data.physicalTime τ))
    (hstream :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        ContDiff ℝ 2 (fun y ↦ fields.streamFunction y (data.physicalTime τ))) :
    SatisfiesConvectionRescaledReducedSystemOn eps
        (dynamicallyRescaledReducedFields data fields)
        data.spatialRate data.axialDrift data.swirlRate data.vorticityRate
        rescaledDomain rescaledTimes ∧
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        data.vorticityRate τ = data.swirlRate τ - data.spatialRate τ := by
  have hphysicalExtended :
      SatisfiesAxisExtendedConvectionResidualSystemOn eps fields
        (physicalDomain ∩ positiveRadiusMeridian) physicalTimes := by
    refine ⟨fun x t hx ht ↦ hphysical.1 hx.1 ht, fun x t hx ht ↦ hphysical.2.1 hx.1 ht,
      fun x t hx ht ↦ ?_⟩
    rw [axisExtendedReducedStreamFunctionResidual_of_ne _ _ _ (ne_of_gt hx.2)]
    exact hphysical.2.2 hx.1 ht
  have hmapExtended ⦃x : ℝ^2⦄ ⦃τ : ℝ⦄
      (hx : x ∈ rescaledDomain) (hτ : τ ∈ rescaledTimes) :
      dynamicReducedSimilarityPoint data x τ ∈
          physicalDomain ∩ positiveRadiusMeridian ∧
        data.physicalTime τ ∈ physicalTimes :=
    ⟨⟨(hmap hx hτ).1, dynamicReducedSimilarityPoint_mem_positiveRadiusMeridian
      data (hspatial_pos hτ) (hdomain hx)⟩, (hmap hx hτ).2⟩
  obtain ⟨hsystem, hrate⟩ :=
    satisfiesAxisExtendedConvectionRescaledResidualSystemOn_of_scale_compatibility
      eps data fields (physicalDomain ∩ positiveRadiusMeridian) rescaledDomain
      physicalTimes rescaledTimes hphysicalExtended hmapExtended
      hswirl_pos hspatial_pos hswirlScale hspatialScale hvorticityScale hcenter hclock
      hcompat hswirl hvorticity hstream
  refine ⟨⟨hsystem.1, hsystem.2.1, fun x τ hx hτ ↦ ?_⟩, hrate⟩
  simpa only [axisExtendedReducedStreamFunctionResidual_of_ne _ _ _ (ne_of_gt (hdomain hx))]
    using hsystem.2.2 hx hτ

end

end AxisymmetricFlow
