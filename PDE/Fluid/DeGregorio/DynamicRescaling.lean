/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.RealPair.Dilation
public import PDE.Fluid.DeGregorio.DynamicRescaling.Stationary
public import PDE.Fluid.DeGregorio.Model
public import PDE.Representations.Similarity.Dynamic
import CAS.ExactTactic

/-!
# Dynamic rescaling of the De Gregorio transport equation

With amplitude `Cω`, length scale `Cl`, and physical time `t(τ)`, set
`ω̃(x,τ) = Cω(τ) ω(Cl(τ)x,t(τ))` and
`ũ(x,τ) = Cω(τ) / Cl(τ) u(Cl(τ)x,t(τ))`.
The scale laws are `Cω' = cω Cω`, `Cl' = -cl Cl`, and `t' = Cω`.
The rescaled equation is `ω̃_τ + (cl x + a ũ) ω̃_x = (cω + ũ_x) ω̃`.

The residual identity follows from the generic dynamic-pullback chain rule; the remaining
algebra is done by the `cas` tactic of SymLean, our computer algebra system for Lean.
For nonzero scales it gives both directions of transport equivalence at corresponding
points. Positive spatial scales preserve the concrete Biot–Savart relation by spectral
Hilbert covariance, so a classical solution of the physical equation becomes a classical
solution of the rescaled equation.

## Main definitions

* `DynamicRescalingData`, `SatisfiesDynamicScaleODEsAt`: the scales, the clock, the
  rates, and the three scale laws.
* `dynamicallyRescaledFields`: the rescaled vorticity and velocity.
* `SatisfiesRescaledTransportEquationOn`, `IsClassicalRescaledSolutionOn`: the rescaled
  equation and its classical solutions.

## Main results

* `rescaledTransportResidual_dynamicallyRescaledFields`: the rescaled residual is `Cω²`
  times the physical residual at the corresponding point.
* `satisfiesRescaledTransportEquationOn_iff_transport`: transport equivalence on the image
  of the clock.
* `IsClassicalSolutionOn.dynamicallyRescaledFields`: classical solutions of the physical
  equation give classical solutions of the rescaled equation.

## References

* J. Chen, T. Y. Hou, and D. Huang, "On the finite time blowup of the De Gregorio model for the 3D
  Euler equations", *Comm. Pure Appl. Math.* 74 (2021), no. 6, 1282-1350; numbering of
  arXiv:1905.06387v3, Section 3.1, (3.1)-(3.3), p. 7, and Section 3.2, (3.4), p. 8.
  <https://doi.org/10.1002/cpa.21991>
  <https://arxiv.org/abs/1905.06387v3>
-/

@[expose] public section

namespace DeGregorio

open PDE.Analysis PDE.Representations.Similarity

noncomputable section

/-- Amplitude, length, physical time, and the two logarithmic rates. -/
structure DynamicRescalingData where
  /-- Vorticity amplitude `Cω`. -/
  vorticityScale : ℝ → ℝ
  /-- Spatial scale `Cl`. -/
  spatialScale : ℝ → ℝ
  /-- Physical time as a function of rescaled time. -/
  physicalTime : ℝ → ℝ
  /-- Logarithmic amplitude rate `cω`. -/
  vorticityRate : ℝ → ℝ
  /-- Negative logarithmic spatial rate `cl`. -/
  spatialRate : ℝ → ℝ

/-- Differential form of the three scale laws in equation (3.3). -/
structure SatisfiesDynamicScaleODEsAt (data : DynamicRescalingData) (τ : ℝ) : Prop where
  /-- `Cω' = cω Cω`. -/
  vorticityScale_hasDerivAt :
    HasDerivAt data.vorticityScale (data.vorticityRate τ * data.vorticityScale τ) τ
  /-- `Cl' = -cl Cl`. -/
  spatialScale_hasDerivAt :
    HasDerivAt data.spatialScale (-data.spatialRate τ * data.spatialScale τ) τ
  /-- `t' = Cω`. -/
  physicalTime_hasDerivAt :
    HasDerivAt data.physicalTime (data.vorticityScale τ) τ

/-- The reciprocal amplitude obeys the sign convention of `ODE.AmplitudeClock`:
`sU' = -cω sU`, where `sU = Cω⁻¹`. The physical clock rate is `Cω`. -/
theorem SatisfiesDynamicScaleODEsAt.inv_vorticityScale_hasDerivAt
    {data : DynamicRescalingData} {τ : ℝ}
    (hlaws : SatisfiesDynamicScaleODEsAt data τ)
    (hamplitude : data.vorticityScale τ ≠ 0) :
    HasDerivAt (fun s ↦ (data.vorticityScale s)⁻¹)
      (-data.vorticityRate τ * (data.vorticityScale τ)⁻¹) τ := by
  exact (hlaws.vorticityScale_hasDerivAt.inv hamplitude).congr_deriv (by cas using hamplitude)

/-- The pullback of both physical fields with their respective amplitudes. -/
def dynamicallyRescaledFields (data : DynamicRescalingData) (fields : Fields) : Fields where
  vorticity :=
    dynamicPullback fields.vorticity data.vorticityScale data.spatialScale data.physicalTime
  velocity := fun x τ ↦ data.vorticityScale τ / data.spatialScale τ *
    fields.velocity (data.spatialScale τ * x) (data.physicalTime τ)

/-- The rescaled transport residual, with the stretching term subtracted. -/
def rescaledTransportResidual
    (a : ℝ) (fields : Fields) (spatialRate vorticityRate : ℝ → ℝ) (x τ : ℝ) : ℝ :=
  deriv (fields.vorticity x) τ +
    (spatialRate τ * x + a * fields.velocity x τ) *
      deriv (fun y ↦ fields.vorticity y τ) x -
        (vorticityRate τ + deriv (fun y ↦ fields.velocity y τ) x) * fields.vorticity x τ

/-- Transport in the dynamically rescaled coordinates. -/
def SatisfiesRescaledTransportEquationOn
    (a : ℝ) (fields : Fields) (spatialRate vorticityRate : ℝ → ℝ)
    (times : Set ℝ) : Prop :=
  ∀ ⦃x τ : ℝ⦄, τ ∈ times →
    deriv (fields.vorticity x) τ +
        (spatialRate τ * x + a * fields.velocity x τ) *
          deriv (fun y ↦ fields.vorticity y τ) x =
      (vorticityRate τ + deriv (fun y ↦ fields.velocity y τ) x) * fields.vorticity x τ

/-- A classical solution of the rescaled equation: regularity, transport, and the concrete
Biot–Savart relation. -/
structure IsClassicalRescaledSolutionOn
    (a : ℝ) (fields : Fields) (spatialRate vorticityRate : ℝ → ℝ)
    (times : Set ℝ) : Prop where
  /-- Derivatives used in the equation exist. -/
  regularity : HasClassicalRegularityOn fields times
  /-- The rescaled vorticity transport equation. -/
  transport : SatisfiesRescaledTransportEquationOn a fields spatialRate vorticityRate times
  /-- The unchanged Biot–Savart equation, interpreted in complex `L²`. -/
  biotSavart : SatisfiesBiotSavartOn fields times

/-- The rescaled equation is equivalent to vanishing of its residual. -/
theorem satisfiesRescaledTransportEquationOn_iff
    (a : ℝ) (fields : Fields) (spatialRate vorticityRate : ℝ → ℝ) (times : Set ℝ) :
    SatisfiesRescaledTransportEquationOn a fields spatialRate vorticityRate times ↔
      ∀ ⦃x τ : ℝ⦄, τ ∈ times →
        rescaledTransportResidual a fields spatialRate vorticityRate x τ = 0 := by
  simp only [SatisfiesRescaledTransportEquationOn, rescaledTransportResidual, sub_eq_zero]

/-- A spatial derivative of pulled-back vorticity gains the factor `Cω Cl`. -/
theorem deriv_dynamicallyRescaledFields_vorticity
    (data : DynamicRescalingData) (fields : Fields) (x τ : ℝ)
    (hω : DifferentiableAt ℝ (fun y ↦ fields.vorticity y (data.physicalTime τ))
      (data.spatialScale τ * x)) :
    deriv (fun y ↦ (dynamicallyRescaledFields data fields).vorticity y τ) x =
      data.vorticityScale τ * data.spatialScale τ *
        deriv (fun y ↦ fields.vorticity y (data.physicalTime τ))
          (data.spatialScale τ * x) := by
  have h := (hω.hasDerivAt.comp x
    ((hasDerivAt_id x).const_mul (data.spatialScale τ))).const_mul (data.vorticityScale τ)
  simpa [dynamicallyRescaledFields, dynamicPullback, smul_eq_mul, mul_comm, mul_left_comm,
    mul_assoc] using h.deriv

/-- A spatial velocity derivative rescales by the vorticity amplitude. -/
theorem hasDerivAt_dynamicallyRescaledFields_velocity
    (data : DynamicRescalingData) (fields : Fields) (x τ : ℝ)
    (hscale : data.spatialScale τ ≠ 0) {v : ℝ}
    (hu : HasDerivAt (fun y ↦ fields.velocity y (data.physicalTime τ)) v
      (data.spatialScale τ * x)) :
    HasDerivAt (fun y ↦ (dynamicallyRescaledFields data fields).velocity y τ)
      (data.vorticityScale τ * v) x := by
  have h := (hu.comp x
    ((hasDerivAt_id x).const_mul (data.spatialScale τ))).const_mul
      (data.vorticityScale τ / data.spatialScale τ)
  apply h.congr_deriv
  cas using hscale

/-- A spatial derivative of pulled-back velocity has amplitude `Cω`. -/
theorem deriv_dynamicallyRescaledFields_velocity
    (data : DynamicRescalingData) (fields : Fields) (x τ : ℝ)
    (hscale : data.spatialScale τ ≠ 0)
    (hu : DifferentiableAt ℝ (fun y ↦ fields.velocity y (data.physicalTime τ))
      (data.spatialScale τ * x)) :
    deriv (fun y ↦ (dynamicallyRescaledFields data fields).velocity y τ) x =
      data.vorticityScale τ *
        deriv (fun y ↦ fields.velocity y (data.physicalTime τ))
          (data.spatialScale τ * x) :=
  (hasDerivAt_dynamicallyRescaledFields_velocity data fields x τ hscale hu.hasDerivAt).deriv

/-- The generic spacetime chain rule specialized to De Gregorio's scale laws. -/
theorem deriv_dynamicallyRescaledFields_time
    (data : DynamicRescalingData) (fields : Fields) (x τ : ℝ)
    (hlaws : SatisfiesDynamicScaleODEsAt data τ)
    (hω : DifferentiableAt ℝ (Function.uncurry fields.vorticity)
      (data.spatialScale τ * x, data.physicalTime τ)) :
    deriv ((dynamicallyRescaledFields data fields).vorticity x) τ =
      data.vorticityScale τ *
          ((-data.spatialRate τ * data.spatialScale τ) *
              (x * deriv (fun y ↦ fields.vorticity y (data.physicalTime τ))
                (data.spatialScale τ * x)) +
            data.vorticityScale τ *
              deriv (fields.vorticity (data.spatialScale τ * x)) (data.physicalTime τ)) +
        data.vorticityRate τ * data.vorticityScale τ *
          fields.vorticity (data.spatialScale τ * x) (data.physicalTime τ) := by
  simpa [dynamicallyRescaledFields, smul_eq_mul, fderiv_eq_smul_deriv] using
    (hasDerivAt_dynamicPullback_expanded fields.vorticity
      data.vorticityScale data.spatialScale data.physicalTime x τ
      (data.vorticityRate τ * data.vorticityScale τ)
      (-data.spatialRate τ * data.spatialScale τ) (data.vorticityScale τ)
      hω hlaws.vorticityScale_hasDerivAt hlaws.spatialScale_hasDerivAt
      hlaws.physicalTime_hasDerivAt).deriv

/-- The rescaled residual at `(x, τ)` is `Cω(τ)²` times the physical residual at
`(Cl(τ) x, t(τ))`. -/
theorem rescaledTransportResidual_dynamicallyRescaledFields
    (a : ℝ) (data : DynamicRescalingData) (fields : Fields) (x τ : ℝ)
    (hlaws : SatisfiesDynamicScaleODEsAt data τ)
    (hscale : data.spatialScale τ ≠ 0)
    (hω : DifferentiableAt ℝ (Function.uncurry fields.vorticity)
      (data.spatialScale τ * x, data.physicalTime τ))
    (hu : DifferentiableAt ℝ (fun y ↦ fields.velocity y (data.physicalTime τ))
      (data.spatialScale τ * x)) :
    rescaledTransportResidual a (dynamicallyRescaledFields data fields)
        data.spatialRate data.vorticityRate x τ =
      data.vorticityScale τ ^ 2 *
        transportResidual a fields (data.spatialScale τ * x) (data.physicalTime τ) := by
  have hωspace := hω.comp (data.spatialScale τ * x)
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) (data.spatialScale τ * x)
      (data.physicalTime τ)).differentiableAt
  unfold rescaledTransportResidual
  rw [deriv_dynamicallyRescaledFields_time data fields x τ hlaws hω,
    deriv_dynamicallyRescaledFields_vorticity data fields x τ hωspace,
    deriv_dynamicallyRescaledFields_velocity data fields x τ hscale hu]
  unfold transportResidual dynamicallyRescaledFields dynamicPullback
  simp only [smul_eq_mul]
  cas using hscale

/-- The rescaled residual vanishes at `(x, τ)` exactly when the physical residual
vanishes at `(Cl(τ) x, t(τ))`. Recovering the physical equation uses `Cω(τ) ≠ 0`. -/
theorem rescaledTransportResidual_eq_zero_iff
    (a : ℝ) (data : DynamicRescalingData) (fields : Fields) (x τ : ℝ)
    (hlaws : SatisfiesDynamicScaleODEsAt data τ)
    (hscale : data.spatialScale τ ≠ 0) (hamplitude : data.vorticityScale τ ≠ 0)
    (hω : DifferentiableAt ℝ (Function.uncurry fields.vorticity)
      (data.spatialScale τ * x, data.physicalTime τ))
    (hu : DifferentiableAt ℝ (fun y ↦ fields.velocity y (data.physicalTime τ))
      (data.spatialScale τ * x)) :
    rescaledTransportResidual a (dynamicallyRescaledFields data fields)
        data.spatialRate data.vorticityRate x τ = 0 ↔
      transportResidual a fields (data.spatialScale τ * x) (data.physicalTime τ) = 0 := by
  rw [rescaledTransportResidual_dynamicallyRescaledFields a data fields x τ
    hlaws hscale hω hu]
  exact mul_eq_zero_iff_left (pow_ne_zero 2 hamplitude)

/-- A physical transport solution satisfies the rescaled transport equation. -/
theorem satisfiesRescaledTransportEquationOn_of_transport
    (a : ℝ) (data : DynamicRescalingData) (fields : Fields)
    (physicalTimes rescaledTimes : Set ℝ)
    (hregularity : HasClassicalRegularityOn fields physicalTimes)
    (htransport : SatisfiesTransportEquationOn a fields physicalTimes)
    (htime : Set.MapsTo data.physicalTime rescaledTimes physicalTimes)
    (hlaws : ∀ τ ∈ rescaledTimes, SatisfiesDynamicScaleODEsAt data τ)
    (hscale : ∀ τ ∈ rescaledTimes, data.spatialScale τ ≠ 0) :
    SatisfiesRescaledTransportEquationOn a (dynamicallyRescaledFields data fields)
      data.spatialRate data.vorticityRate rescaledTimes := by
  rw [satisfiesRescaledTransportEquationOn_iff]
  intro x τ hτ
  rw [rescaledTransportResidual_dynamicallyRescaledFields a data fields x τ
    (hlaws τ hτ) (hscale τ hτ)
    (hregularity.vorticity_differentiableAt (htime hτ))
    (hregularity.velocity_differentiableAt (htime hτ))]
  rw [(satisfiesTransportEquationOn_iff a fields physicalTimes).mp htransport (htime hτ),
    mul_zero]

/-- The rescaled equation holds on a set of rescaled times exactly when the physical
equation holds on its image under the clock. Every spatial point is reached because
`Cl(τ) ≠ 0`. -/
theorem satisfiesRescaledTransportEquationOn_iff_transport
    (a : ℝ) (data : DynamicRescalingData) (fields : Fields) (rescaledTimes : Set ℝ)
    (hregularity : HasClassicalRegularityOn fields (data.physicalTime '' rescaledTimes))
    (hlaws : ∀ τ ∈ rescaledTimes, SatisfiesDynamicScaleODEsAt data τ)
    (hscale : ∀ τ ∈ rescaledTimes, data.spatialScale τ ≠ 0)
    (hamplitude : ∀ τ ∈ rescaledTimes, data.vorticityScale τ ≠ 0) :
    SatisfiesRescaledTransportEquationOn a (dynamicallyRescaledFields data fields)
        data.spatialRate data.vorticityRate rescaledTimes ↔
      SatisfiesTransportEquationOn a fields (data.physicalTime '' rescaledTimes) := by
  constructor
  · intro htransport
    rw [satisfiesTransportEquationOn_iff]
    rintro x t ⟨τ, hτ, rfl⟩
    have htime : data.physicalTime τ ∈ data.physicalTime '' rescaledTimes :=
      ⟨τ, hτ, rfl⟩
    have hpoint := (rescaledTransportResidual_eq_zero_iff a data fields
      (x / data.spatialScale τ) τ (hlaws τ hτ) (hscale τ hτ) (hamplitude τ hτ)
      (hregularity.vorticity_differentiableAt htime)
      (hregularity.velocity_differentiableAt htime)).mp
        ((satisfiesRescaledTransportEquationOn_iff _ _ _ _ _).mp htransport hτ)
    simpa only [mul_div_cancel₀ x (hscale τ hτ)] using hpoint
  · intro htransport
    exact satisfiesRescaledTransportEquationOn_of_transport a data fields _ _
      hregularity htransport (fun τ hτ ↦ ⟨τ, hτ, rfl⟩) hlaws hscale

/-- The scale laws and physical regularity imply the regularity of the pulled-back fields. -/
theorem HasClassicalRegularityOn.dynamicallyRescaledFields
    (data : DynamicRescalingData) (fields : Fields) (physicalTimes rescaledTimes : Set ℝ)
    (hregularity : HasClassicalRegularityOn fields physicalTimes)
    (htime : Set.MapsTo data.physicalTime rescaledTimes physicalTimes)
    (hlaws : ∀ τ ∈ rescaledTimes, SatisfiesDynamicScaleODEsAt data τ) :
    HasClassicalRegularityOn (dynamicallyRescaledFields data fields) rescaledTimes := by
  constructor
  · intro x τ hτ
    have hsnd : DifferentiableAt ℝ (fun p : ℝ × ℝ ↦ p.2) (x, τ) :=
      differentiableAt_snd
    have hfst : DifferentiableAt ℝ (fun p : ℝ × ℝ ↦ p.1) (x, τ) :=
      differentiableAt_fst
    have hA := (hlaws τ hτ).vorticityScale_hasDerivAt.differentiableAt.comp
      (x, τ) hsnd
    have hL := (hlaws τ hτ).spatialScale_hasDerivAt.differentiableAt.comp
      (x, τ) hsnd
    have hT := (hlaws τ hτ).physicalTime_hasDerivAt.differentiableAt.comp
      (x, τ) hsnd
    have hpath := (hL.mul hfst).prodMk hT
    have hω := (hregularity.vorticity_differentiableAt
      (x := data.spatialScale τ * x) (htime hτ)).comp (x, τ) hpath
    change DifferentiableAt ℝ
      (fun p : ℝ × ℝ ↦ data.vorticityScale p.2 *
        fields.vorticity (data.spatialScale p.2 * p.1) (data.physicalTime p.2)) (x, τ)
    exact hA.mul hω
  · intro x τ hτ
    have hu := (hregularity.velocity_differentiableAt
      (x := data.spatialScale τ * x) (htime hτ)).comp x
        ((hasDerivAt_id x).const_mul (data.spatialScale τ)).differentiableAt
    simpa only [DeGregorio.dynamicallyRescaledFields, Function.comp_def] using
      hu.const_mul (data.vorticityScale τ / data.spatialScale τ)

/-- Positive spatial scales preserve the Biot–Savart law. The scale laws are not used. -/
theorem SatisfiesBiotSavartOn.dynamicallyRescaledFields
    (data : DynamicRescalingData) (fields : Fields)
    (physicalTimes rescaledTimes : Set ℝ)
    (hbiotSavart : SatisfiesBiotSavartOn fields physicalTimes)
    (hregularity : HasClassicalRegularityOn fields physicalTimes)
    (htime : Set.MapsTo data.physicalTime rescaledTimes physicalTimes)
    (hscale : ∀ τ ∈ rescaledTimes, 0 < data.spatialScale τ) :
    SatisfiesBiotSavartOn (dynamicallyRescaledFields data fields) rescaledTimes := by
  intro τ hτ
  have hpair := ((hbiotSavart (htime hτ)).dilate (hscale τ hτ)).const_mul
    (data.vorticityScale τ)
  have hderiv : deriv (fun y ↦
      (DeGregorio.dynamicallyRescaledFields data fields).velocity y τ) =
      fun x ↦ data.vorticityScale τ *
        deriv (fun y ↦ fields.velocity y (data.physicalTime τ)) (data.spatialScale τ * x) := by
    funext x
    exact deriv_dynamicallyRescaledFields_velocity data fields x τ (hscale τ hτ).ne'
      (hregularity.velocity_differentiableAt (htime hτ))
  rw [hderiv]
  exact hpair

/-- Positive spatial scales transfer a classical De Gregorio solution to the
rescaled equation, including the concrete spectral Biot–Savart law. -/
theorem IsClassicalSolutionOn.dynamicallyRescaledFields
    (a : ℝ) (data : DynamicRescalingData) (fields : Fields)
    (physicalTimes rescaledTimes : Set ℝ)
    (hsolution : IsClassicalSolutionOn a fields physicalTimes)
    (htime : Set.MapsTo data.physicalTime rescaledTimes physicalTimes)
    (hlaws : ∀ τ ∈ rescaledTimes, SatisfiesDynamicScaleODEsAt data τ)
    (hscale : ∀ τ ∈ rescaledTimes, 0 < data.spatialScale τ) :
    IsClassicalRescaledSolutionOn a (dynamicallyRescaledFields data fields)
      data.spatialRate data.vorticityRate rescaledTimes where
  regularity := hsolution.regularity.dynamicallyRescaledFields
    data fields physicalTimes rescaledTimes htime hlaws
  transport := satisfiesRescaledTransportEquationOn_of_transport a data fields
    physicalTimes rescaledTimes hsolution.regularity hsolution.transport htime hlaws
      (fun τ hτ ↦ (hscale τ hτ).ne')
  biotSavart := hsolution.biotSavart.dynamicallyRescaledFields data fields
    physicalTimes rescaledTimes hsolution.regularity htime hscale

/-- A classical solution of the physical equation solves the rescaled equation with
zero rates. -/
theorem IsClassicalSolutionOn.toRescaled {a : ℝ} {fields : Fields} {times : Set ℝ}
    (hsol : IsClassicalSolutionOn a fields times) :
    IsClassicalRescaledSolutionOn a fields (fun _ ↦ 0) (fun _ ↦ 0) times where
  regularity := hsol.regularity
  transport := fun _ _ hτ ↦ by
    simpa only [zero_mul, zero_add] using hsol.transport hτ
  biotSavart := hsol.biotSavart

/-- For time-independent fields, the rescaled transport residual is the negative of the
stationary right-hand side. -/
theorem rescaledTransportResidual_stationary
    (a spatialRate vorticityRate : ℝ) (ω u : ℝ → ℝ) (x τ : ℝ) :
    rescaledTransportResidual a
        ⟨fun x _ ↦ ω x, fun x _ ↦ u x⟩
        (fun _ ↦ spatialRate) (fun _ ↦ vorticityRate) x τ =
      -stationaryResidual a spatialRate vorticityRate ω u x := by
  unfold rescaledTransportResidual stationaryResidual
  simp only [deriv_const, zero_add]
  cas

end

end DeGregorio
