/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.VorticityStream.DynamicRescaling.Clock
public import PDE.Fluid.Boussinesq.VorticityStream.DynamicRescaling.Equations
public import PDE.Analysis.Calculus.TimeReflection
public import Mathlib.MeasureTheory.Function.L2Space
import PDE.Fluid.Boussinesq.VorticityStream.DynamicRescaling.Calculus

/-!
# Undoing the dynamic rescaling

At physical time `t` the inverse clock gives the rescaled time `τ = t⁻¹(t)`, and the physical
fields are recovered from rescaled fields `ω̃, θ̃, φ̃` by undoing the amplitudes and the dilation:

```text
ω(y, t) = C_ω(τ)⁻¹ ω̃(C_l(τ)⁻¹ y, τ),   θ(y, t) = C_θ(τ)⁻¹ θ̃(C_l(τ)⁻¹ y, τ),
φ(y, t) = C_l(τ)² C_ω(τ)⁻¹ φ̃(C_l(τ)⁻¹ y, τ).
```

These are `reconstructedFields data R`. For the rescaling `ofRates l₀ cl cω` with continuous rates
and `l₀ > 0`, a classical solution of the rescaled system (2.8) on a set `U` of rescaled times gives
a classical solution of the physical system on `t(U)`
(`isClassicalVorticityStreamSolutionOn_reconstructedFields`).

A rescaled solution on `[0, ∞)` is regular at `τ = 0` only from the right, while the classical
physical solution predicate on `[0, T)` uses ordinary time derivatives at `t = 0`. The first-order
reflection `VorticityStreamFields.reflectTimeZero` of the rescaled vorticity and temperature across
`τ = 0` supplies them: it agrees with `R` for `τ ≥ 0` and is jointly differentiable at `τ = 0`
(`isClassicalVorticityStreamSolutionOn_reconstructedFields_reflectTimeZero`).

The dilation preserves the upper half-plane, so the physical sup norm of the vorticity is `C_ω(τ)⁻¹`
times the rescaled one (`iSup_reconstructedFields_vorticity`). With the rescaled solution in place
of the profile `ω̄`, this is the relation `‖ω_phy(t(τ))‖_∞ ≈ C_ω(τ)⁻¹ ‖ω̄‖_∞` of Chen and Hou,
Part I, Section 2.2, through which their Section 5.9.4 passes from stability to blowup. The physical
velocity is `C_l C_ω⁻¹` times the rescaled velocity at the rescaled point
(`vorticityStreamVelocity_reconstructedFields`), and square integrability on the half-plane
transfers (`memLp_vorticityStreamVelocity_reconstructedFields`).

The construction is shared by the Boussinesq system on the half-plane and by the wall coordinates
of axisymmetric Euler, whose rescaling is the same `DynamicRescalingData`.

## Main definitions

* `reconstructedFields`: the physical fields of rescaled fields, with the amplitudes and the
  dilation undone at the rescaled time `t⁻¹(t)`.
* `VorticityStreamFields.reflectTimeZero`: the fields with vorticity and temperature reflected
  across `τ = 0` to first order.

## Main results

* `dynamicallyRescaledFields_reconstructedFields`: rescaling the reconstructed fields gives back
  the rescaled fields.
* `isClassicalVorticityStreamSolutionOn_reconstructedFields`: a classical solution of the rescaled
  system on `U` gives a classical solution of the physical system on `t(U)`.
* `isClassicalVorticityStreamSolutionOn_reconstructedFields_reflectTimeZero`: the same for a
  rescaled solution on `[0, ∞)`, after reflecting across `τ = 0`.
* `iSup_reconstructedFields_vorticity`: the physical sup norm of the vorticity over the upper
  half-plane is `C_ω(τ)⁻¹` times the rescaled one.
* `vorticityStreamVelocity_reconstructedFields`: the physical velocity is `C_l C_ω⁻¹` times the
  rescaled velocity at the rescaled point.
* `memLp_vorticityStreamVelocity_reconstructedFields`: square integrability of the velocity over
  the upper half-plane transfers to the reconstructed fields.

## How it works

We first check that the dynamic rescaling of the reconstructed fields is `R` again
(`dynamicallyRescaledFields_reconstructedFields`). The residual identities
`rescaledVorticityResidual_dynamicallyRescaledFields` and
`rescaledTemperatureResidual_dynamicallyRescaledFields` then write the rescaled residuals of `R` at
`(C_l(τ)⁻¹ y, τ)` as `C_ω(τ)²` and `C_θ(τ) C_ω(τ)` times the physical residuals at `(y, t(τ))`, so
the physical equations hold wherever the rescaled ones do. The Poisson equation transfers in the
same way by `laplacian_rescaledStreamFunction`, and the Dirichlet condition because the dilation
maps the boundary to itself. The regularity of the physical fields comes from that of `R`: the
inverse clock is `C¹` (`contDiffOn_rescaledTime_ofRates`), and so are the amplitudes for continuous
rates (`contDiff_spatialScale_ofRates`, `contDiff_vorticityScale_ofRates`,
`contDiff_temperatureScale_ofRates`).

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 2.1, (2.4)-(2.8),
  Section 2.2, p. 6, and Section 5.9.4, p. 93.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open Filter Set Function MeasureTheory
open scoped Topology ENNReal
open IncompressibleFlow PDE.Representations.Similarity
open PDE (advectiveDerivative laplacian)

namespace Boussinesq

set_option linter.missingDocs true

open DynamicRescalingData

/-- The physical fields of the rescaled fields `R` under the rescaling `data`: undo the
amplitudes and the dilation at the rescaled time `t⁻¹(t)`. -/
def reconstructedFields (data : DynamicRescalingData) (R : VorticityStreamFields) :
    VorticityStreamFields where
  vorticity y t := (data.vorticityScale (data.rescaledTime t))⁻¹ *
    R.vorticity ((data.spatialScale (data.rescaledTime t))⁻¹ • y) (data.rescaledTime t)
  temperature y t := (data.temperatureScale (data.rescaledTime t))⁻¹ *
    R.temperature ((data.spatialScale (data.rescaledTime t))⁻¹ • y) (data.rescaledTime t)
  streamFunction y t :=
    data.spatialScale (data.rescaledTime t) ^ 2 / data.vorticityScale (data.rescaledTime t) *
      R.streamFunction ((data.spatialScale (data.rescaledTime t))⁻¹ • y) (data.rescaledTime t)

section OfRates

variable {l₀ : ℝ} {cl cω : ℝ → ℝ}

/-- Rescaling the reconstructed fields gives back the rescaled fields. -/
theorem dynamicallyRescaledFields_reconstructedFields (hl₀ : 0 < l₀) (hcω : Continuous cω)
    (R : VorticityStreamFields) :
    dynamicallyRescaledFields (ofRates l₀ cl cω) (reconstructedFields (ofRates l₀ cl cω) R) =
      R := by
  have hA := vorticityScale_ofRates_pos (l₀ := l₀) cl cω
  have hL := spatialScale_ofRates_pos hl₀ cl cω
  have hT := temperatureScale_ofRates_pos hl₀ cl cω
  cases R with
  | mk ω θ ψ =>
    simp only [dynamicallyRescaledFields]
    congr 1 <;> funext x τ
    · simp only [rescaledVorticity, dynamicPullback, reconstructedFields, smul_eq_mul,
        rescaledTime_ofRates_physicalTime cl hcω, smul_smul, inv_mul_cancel₀ (hL τ).ne', one_smul,
        mul_inv_cancel_left₀ (hA τ).ne']
    · simp only [rescaledTemperature, dynamicPullback, reconstructedFields, smul_eq_mul,
        rescaledTime_ofRates_physicalTime cl hcω, smul_smul, inv_mul_cancel₀ (hL τ).ne', one_smul,
        mul_inv_cancel_left₀ (hT τ).ne']
    · simp only [rescaledStreamFunction, reconstructedFields, dynamicSimilarityPoint,
        rescaledTime_ofRates_physicalTime cl hcω, smul_smul, inv_mul_cancel₀ (hL τ).ne', one_smul]
      have := (hA τ).ne'
      have := (hL τ).ne'
      field_simp

/-- At time zero the reconstructed vorticity is the rescaled vorticity at `l₀⁻¹ y`. -/
theorem reconstructedFields_vorticity_zero (hcω : Continuous cω) (R : VorticityStreamFields)
    (y : ℝ^2) :
    (reconstructedFields (ofRates l₀ cl cω) R).vorticity y 0 = R.vorticity (l₀⁻¹ • y) 0 := by
  simp [reconstructedFields, rescaledTime_ofRates_zero cl hcω]

/-- At time zero the reconstructed temperature is `l₀` times the rescaled temperature at
`l₀⁻¹ y`. -/
theorem reconstructedFields_temperature_zero (hcω : Continuous cω) (R : VorticityStreamFields)
    (y : ℝ^2) :
    (reconstructedFields (ofRates l₀ cl cω) R).temperature y 0 =
      l₀ * R.temperature (l₀⁻¹ • y) 0 := by
  simp [reconstructedFields, rescaledTime_ofRates_zero cl hcω]

/-- The undone scalar `A(t⁻¹(t))⁻¹ f(C_l(t⁻¹(t))⁻¹ y, t⁻¹(t))`. -/
private def undo (l₀ : ℝ) (cl cω : ℝ → ℝ) (A : ℝ → ℝ) (f : ℝ^2 → ℝ → ℝ) (p : ℝ^2 × ℝ) : ℝ :=
  (A ((ofRates l₀ cl cω).rescaledTime p.2))⁻¹ *
    f (((ofRates l₀ cl cω).spatialScale ((ofRates l₀ cl cω).rescaledTime p.2))⁻¹ • p.1)
      ((ofRates l₀ cl cω).rescaledTime p.2)

/-- The point `(C_l(t⁻¹(t))⁻¹ y, t⁻¹(t))` of the rescaled variables. -/
private def chart (l₀ : ℝ) (cl cω : ℝ → ℝ) (p : ℝ^2 × ℝ) : ℝ^2 × ℝ :=
  (((ofRates l₀ cl cω).spatialScale ((ofRates l₀ cl cω).rescaledTime p.2))⁻¹ • p.1,
    (ofRates l₀ cl cω).rescaledTime p.2)

/-- At the physical time `t(τ)` the chart is `(C_l(τ)⁻¹ y, τ)`. -/
private theorem chart_physicalTime (hcω : Continuous cω) (y : ℝ^2) (τ : ℝ) :
    chart l₀ cl cω (y, (ofRates l₀ cl cω).physicalTime τ) =
      (((ofRates l₀ cl cω).spatialScale τ)⁻¹ • y, τ) := by
  simp [chart, rescaledTime_ofRates_physicalTime cl hcω]

/-- For continuous rates and `l₀ > 0` the chart is differentiable at every point `(y, t(τ))`. -/
private theorem differentiableAt_chart (hl₀ : 0 < l₀) (hcl : Continuous cl)
    (hcω : Continuous cω) (y : ℝ^2)
    (τ : ℝ) : DifferentiableAt ℝ (chart l₀ cl cω) (y, (ofRates l₀ cl cω).physicalTime τ) := by
  have hσ : DifferentiableAt ℝ (fun p : ℝ^2 × ℝ ↦ (ofRates l₀ cl cω).rescaledTime p.2)
      (y, (ofRates l₀ cl cω).physicalTime τ) :=
    (rescaledTime_ofRates_hasStrictDerivAt cl hcω τ).hasDerivAt.differentiableAt.comp
      (y, (ofRates l₀ cl cω).physicalTime τ) differentiableAt_snd
  have hL : DifferentiableAt ℝ
      (fun p : ℝ^2 × ℝ ↦ (ofRates l₀ cl cω).spatialScale ((ofRates l₀ cl cω).rescaledTime p.2))
      (y, (ofRates l₀ cl cω).physicalTime τ) :=
    ((contDiff_spatialScale_ofRates cω hcl).differentiable (by norm_num) _).comp _ hσ
  have hLne : (ofRates l₀ cl cω).spatialScale
      ((ofRates l₀ cl cω).rescaledTime (y, (ofRates l₀ cl cω).physicalTime τ).2) ≠ 0 :=
    (spatialScale_ofRates_pos hl₀ cl cω _).ne'
  exact ((hL.inv hLne).smul differentiableAt_fst).prodMk hσ

/-- For continuous rates and `l₀ > 0` the chart is `C¹` on `ℝ² × t(ℝ)`. -/
private theorem contDiffOn_chart (hl₀ : 0 < l₀) (hcl : Continuous cl) (hcω : Continuous cω) :
    ContDiffOn ℝ 1 (chart l₀ cl cω) (univ ×ˢ range (ofRates l₀ cl cω).physicalTime) := by
  have hσ : ContDiffOn ℝ 1 (fun p : ℝ^2 × ℝ ↦ (ofRates l₀ cl cω).rescaledTime p.2)
      (univ ×ˢ range (ofRates l₀ cl cω).physicalTime) :=
    (contDiffOn_rescaledTime_ofRates cl hcω).comp contDiff_snd.contDiffOn
      fun p hp ↦ hp.2
  have hL : ContDiffOn ℝ 1
      (fun p : ℝ^2 × ℝ ↦ (ofRates l₀ cl cω).spatialScale ((ofRates l₀ cl cω).rescaledTime p.2))
      (univ ×ˢ range (ofRates l₀ cl cω).physicalTime) :=
    (contDiff_spatialScale_ofRates cω hcl).comp_contDiffOn hσ
  exact ((hL.inv fun p _ ↦ (spatialScale_ofRates_pos hl₀ cl cω _).ne').smul
    contDiff_fst.contDiffOn).prodMk hσ

/-- For a nonvanishing `C¹` amplitude `A`, the undone scalar of `f` is differentiable at `(y, t(τ))`
when `f` is differentiable at the chart point `(C_l(τ)⁻¹ y, τ)`. -/
private theorem differentiableAt_undo (hl₀ : 0 < l₀) (hcl : Continuous cl) (hcω : Continuous cω)
    {A : ℝ → ℝ} (hA : ContDiff ℝ 1 A) (hA0 : ∀ τ, A τ ≠ 0) {f : ℝ^2 → ℝ → ℝ} {y : ℝ^2}
    {τ : ℝ} (hf : DifferentiableAt ℝ (uncurry f) (((ofRates l₀ cl cω).spatialScale τ)⁻¹ • y, τ)) :
    DifferentiableAt ℝ (undo l₀ cl cω A f) (y, (ofRates l₀ cl cω).physicalTime τ) := by
  have hσ : DifferentiableAt ℝ (fun p : ℝ^2 × ℝ ↦ (ofRates l₀ cl cω).rescaledTime p.2)
      (y, (ofRates l₀ cl cω).physicalTime τ) :=
    (rescaledTime_ofRates_hasStrictDerivAt cl hcω τ).hasDerivAt.differentiableAt.comp
      (y, (ofRates l₀ cl cω).physicalTime τ) differentiableAt_snd
  have hAσ : DifferentiableAt ℝ (fun p : ℝ^2 × ℝ ↦ (A ((ofRates l₀ cl cω).rescaledTime p.2))⁻¹)
      (y, (ofRates l₀ cl cω).physicalTime τ) :=
    ((hA.differentiable (by norm_num) _).comp _ hσ).inv (hA0 _)
  have hfc : DifferentiableAt ℝ (fun p ↦ uncurry f (chart l₀ cl cω p))
      (y, (ofRates l₀ cl cω).physicalTime τ) :=
    (by rw [chart_physicalTime hcω]; exact hf :
      DifferentiableAt ℝ (uncurry f) (chart l₀ cl cω (y, (ofRates l₀ cl cω).physicalTime τ))).comp
      _ (differentiableAt_chart hl₀ hcl hcω y τ)
  exact hAσ.mul hfc

/-- For a nonvanishing `C¹` amplitude `A`, the undone scalar of a function `C¹` on `ℝ² × U` is `C¹`
on `ℝ² × t(U)`. -/
private theorem contDiffOn_undo (hl₀ : 0 < l₀) (hcl : Continuous cl) (hcω : Continuous cω)
    {A : ℝ → ℝ} (hA : ContDiff ℝ 1 A) (hA0 : ∀ τ, A τ ≠ 0) {f : ℝ^2 → ℝ → ℝ} {U : Set ℝ}
    (hf : ContDiffOn ℝ 1 (uncurry f) (univ ×ˢ U)) :
    ContDiffOn ℝ 1 (undo l₀ cl cω A f) (univ ×ˢ ((ofRates l₀ cl cω).physicalTime '' U)) := by
  have hsub : univ ×ˢ ((ofRates l₀ cl cω).physicalTime '' U) ⊆
      univ ×ˢ range (ofRates l₀ cl cω).physicalTime :=
    prod_mono (subset_refl (univ : Set (ℝ^2))) (image_subset_range _ _)
  have hσ : ContDiffOn ℝ 1 (fun p : ℝ^2 × ℝ ↦ (ofRates l₀ cl cω).rescaledTime p.2)
      (univ ×ˢ range (ofRates l₀ cl cω).physicalTime) :=
    (contDiffOn_rescaledTime_ofRates cl hcω).comp contDiff_snd.contDiffOn
      fun p hp ↦ hp.2
  have hAσ : ContDiffOn ℝ 1 (fun p : ℝ^2 × ℝ ↦ (A ((ofRates l₀ cl cω).rescaledTime p.2))⁻¹)
      (univ ×ˢ range (ofRates l₀ cl cω).physicalTime) :=
    (hA.comp_contDiffOn hσ).inv fun _ _ ↦ hA0 _
  have hmaps : MapsTo (chart l₀ cl cω) (univ ×ˢ ((ofRates l₀ cl cω).physicalTime '' U))
      (univ ×ˢ U) := by
    rintro ⟨y, _⟩ ⟨-, τ, hτ, rfl⟩
    rw [chart_physicalTime hcω]
    exact ⟨mem_univ _, hτ⟩
  exact (hAσ.mono hsub).mul (hf.comp ((contDiffOn_chart hl₀ hcl hcω).mono hsub) hmaps)

/-- **Undoing the dynamic rescaling.** Let `R` be rescaled fields on a set `U` of rescaled times
whose vorticity and temperature are `C¹` within `ℝ² × U` and jointly differentiable at every
point of `ℝ² × U`, whose stream functions are `C²`, and which solve the rescaled system (2.8)
with the rates `c_l`, `c_ω`, `c_θ = c_l + 2 c_ω`, the Poisson equation and the Dirichlet
condition on `U`. Then, for continuous rates, the reconstructed fields are a classical solution
of the physical system on the physical times `t(U)`. -/
theorem isClassicalVorticityStreamSolutionOn_reconstructedFields (hl₀ : 0 < l₀)
    (hcl : Continuous cl) (hcω : Continuous cω) {R : VorticityStreamFields} {U : Set ℝ}
    (hω : ContDiffOn ℝ 1 (uncurry R.vorticity) (univ ×ˢ U))
    (hθ : ContDiffOn ℝ 1 (uncurry R.temperature) (univ ×ˢ U))
    (hωAt : ∀ τ ∈ U, ∀ x, DifferentiableAt ℝ (uncurry R.vorticity) (x, τ))
    (hθAt : ∀ τ ∈ U, ∀ x, DifferentiableAt ℝ (uncurry R.temperature) (x, τ))
    (hψ : ∀ τ ∈ U, ContDiff ℝ 2 (fun x ↦ R.streamFunction x τ))
    (hequations : SatisfiesRescaledScalarEquationsOn R cl cω (fun τ ↦ cl τ + 2 * cω τ)
      upperHalfPlane U)
    (hstream : SatisfiesStreamFunctionEquationOn R U)
    (hboundary : HasZeroStreamFunctionBoundaryOn R U) :
    IsClassicalVorticityStreamSolutionOn (reconstructedFields (ofRates l₀ cl cω) R)
      ((ofRates l₀ cl cω).physicalTime '' U) := by
  set data := ofRates l₀ cl cω with hdata
  set P := reconstructedFields data R with hP
  have hlaws := satisfiesDynamicRescalingLawsAt_ofRates hl₀ hcl hcω
  have hrescale : dynamicallyRescaledFields data P = R :=
    dynamicallyRescaledFields_reconstructedFields hl₀ hcω R
  have hPω : uncurry P.vorticity = undo l₀ cl cω data.vorticityScale R.vorticity := rfl
  have hPθ : uncurry P.temperature = undo l₀ cl cω data.temperatureScale R.temperature := rfl
  have hA := contDiff_vorticityScale_ofRates (l₀ := l₀) cl hcω
  have hA0 : ∀ τ, data.vorticityScale τ ≠ 0 := fun τ ↦ (vorticityScale_ofRates_pos cl cω τ).ne'
  have hT := contDiff_temperatureScale_ofRates (l₀ := l₀) hcl hcω
  have hT0 : ∀ τ, data.temperatureScale τ ≠ 0 :=
    fun τ ↦ (temperatureScale_ofRates_pos hl₀ cl cω τ).ne'
  have hL0 : ∀ τ, data.spatialScale τ ≠ 0 := fun τ ↦ (spatialScale_ofRates_pos hl₀ cl cω τ).ne'
  have hPωAt : ∀ τ ∈ U, ∀ y, DifferentiableAt ℝ (uncurry P.vorticity)
      (y, data.physicalTime τ) := fun τ hτ y ↦
    hPω ▸ differentiableAt_undo hl₀ hcl hcω hA hA0 (hωAt τ hτ _)
  have hPθAt : ∀ τ ∈ U, ∀ y, DifferentiableAt ℝ (uncurry P.temperature)
      (y, data.physicalTime τ) := fun τ hτ y ↦
    hPθ ▸ differentiableAt_undo hl₀ hcl hcω hT hT0 (hθAt τ hτ _)
  have hslice {f : ℝ^2 → ℝ → ℝ} {y : ℝ^2} {t : ℝ}
      (h : DifferentiableAt ℝ (uncurry f) (y, t)) : DifferentiableAt ℝ (fun z ↦ f z t) y := by
    exact h.comp y (by fun_prop : DifferentiableAt ℝ (fun z : ℝ^2 ↦ (z, t)) y)
  have hPψ : ∀ τ ∈ U, ContDiff ℝ 2 (fun y ↦ P.streamFunction y (data.physicalTime τ)) := by
    intro τ hτ
    simp only [hP, reconstructedFields, hdata, rescaledTime_ofRates_physicalTime cl hcω]
    exact contDiff_const.mul ((hψ τ hτ).comp (contDiff_const_smul _))
  have hpoint {τ : ℝ} {w : ℝ^2} (hw : w ∈ upperHalfPlane) :
      (data.spatialScale τ)⁻¹ • w ∈ upperHalfPlane := by
    change 0 < ((data.spatialScale τ)⁻¹ • w) 1
    simpa using mul_pos (inv_pos.2 (spatialScale_ofRates_pos hl₀ cl cω τ)) hw
  have hsim {τ : ℝ} (w : ℝ^2) :
      dynamicSimilarityPoint data ((data.spatialScale τ)⁻¹ • w) τ = w :=
    dynamicSimilarityPoint_inv_smul data (hL0 τ) w
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact contDiffOn_undo hl₀ hcl hcω hA hA0 hω
  · exact contDiffOn_undo hl₀ hcl hcω hT hT0 hθ
  · rintro y _ ⟨τ, hτ, rfl⟩
    exact (hPωAt τ hτ y).comp _ (by fun_prop)
  · rintro y _ ⟨τ, hτ, rfl⟩
    exact (hPθAt τ hτ y).comp _ (by fun_prop)
  · rintro _ ⟨τ, hτ, rfl⟩
    exact hPψ τ hτ
  · rintro w _ hw ⟨τ, hτ, rfl⟩
    have hres := rescaledVorticityResidual_dynamicallyRescaledFields data P
      ((data.spatialScale τ)⁻¹ • w) τ (hlaws τ).toSatisfiesDynamicScaleODEsAt (hL0 τ)
      (hlaws τ).sourceScale_eq (by rw [hsim]; exact hPωAt τ hτ w)
      (by rw [hsim]; exact hslice (hPθAt τ hτ w)) ((hPψ τ hτ).of_le (by norm_num))
    rw [hrescale, hsim] at hres
    have h0 := (satisfiesRescaledVorticityEquationAtTime_iff_residual_eq_zero R cl cω
      upperHalfPlane τ).1 (hequations.1 hτ) (hpoint (τ := τ) hw)
    rw [show data.spatialRate = cl from rfl, show data.vorticityRate = cω from rfl, h0] at hres
    have := (mul_eq_zero.1 hres.symm).resolve_left (pow_ne_zero 2 (hA0 τ))
    linarith
  · rintro w _ hw ⟨τ, hτ, rfl⟩
    have hres := rescaledTemperatureResidual_dynamicallyRescaledFields data P
      ((data.spatialScale τ)⁻¹ • w) τ (hlaws τ).toSatisfiesDynamicScaleODEsAt (hL0 τ)
      (by rw [hsim]; exact hPθAt τ hτ w) ((hPψ τ hτ).of_le (by norm_num))
    rw [hrescale, hsim] at hres
    have h0 := (satisfiesRescaledTemperatureEquationAtTime_iff_residual_eq_zero R cl
      (fun τ ↦ cl τ + 2 * cω τ) upperHalfPlane τ).1 (hequations.2 hτ) (hpoint (τ := τ) hw)
    rw [show data.spatialRate = cl from rfl,
      show data.temperatureRate = fun τ ↦ cl τ + 2 * cω τ from rfl, h0] at hres
    exact (mul_eq_zero.1 hres.symm).resolve_left (mul_ne_zero (hT0 τ) (hA0 τ))
  · rintro w _ hw ⟨τ, hτ, rfl⟩
    have h := hstream (hpoint (τ := τ) hw) hτ
    have hψeq : (fun x ↦ R.streamFunction x τ) =
        fun x ↦ rescaledStreamFunction data P x τ := by
      rw [← hrescale]
      rfl
    have hωeq : R.vorticity ((data.spatialScale τ)⁻¹ • w) τ =
        data.vorticityScale τ * P.vorticity w (data.physicalTime τ) := by
      rw [← hrescale]
      change data.vorticityScale τ • P.vorticity (dynamicSimilarityPoint data _ τ) _ = _
      rw [hsim, smul_eq_mul]
    rw [hψeq, hωeq, laplacian_rescaledStreamFunction data P _ τ (hL0 τ)
      (by rw [hsim]; exact (hPψ τ hτ).contDiffAt), hsim] at h
    have h' : data.vorticityScale τ *
        (-laplacian (fun y ↦ P.streamFunction y (data.physicalTime τ)) w -
          P.vorticity w (data.physicalTime τ)) = 0 := by linarith
    linarith [(mul_eq_zero.1 h').resolve_left (hA0 τ)]
  · rintro z _ ⟨τ, hτ, rfl⟩
    simp only [hP, reconstructedFields, hdata, rescaledTime_ofRates_physicalTime cl hcω]
    rw [show ((ofRates l₀ cl cω).spatialScale τ)⁻¹ • horizontalBoundaryPoint z =
        horizontalBoundaryPoint (((ofRates l₀ cl cω).spatialScale τ)⁻¹ * z) by
      ext i
      fin_cases i <;> simp [horizontalBoundaryPoint, smul_eq_mul],
      hboundary _ hτ, mul_zero]

end OfRates

/-- The rescaled scalar equations at a time depend on the rates only through their values at that
time. -/
theorem SatisfiesRescaledScalarEquationsOn.congr_rates {F : VorticityStreamFields}
    {cl cω cθ cl' cω' cθ' : ℝ → ℝ} {D : Set (ℝ^2)} {times : Set ℝ}
    (h : SatisfiesRescaledScalarEquationsOn F cl cω cθ D times)
    (hrates : ∀ τ ∈ times, cl τ = cl' τ ∧ cω τ = cω' τ ∧ cθ τ = cθ' τ) :
    SatisfiesRescaledScalarEquationsOn F cl' cω' cθ' D times := by
  have hu {τ : ℝ} (hτ : τ ∈ times) : (fun y ↦ rescaledTransportVelocity F cl' y τ) =
      fun y ↦ rescaledTransportVelocity F cl y τ := by
    funext y
    simp [rescaledTransportVelocity, (hrates τ hτ).1]
  refine ⟨fun τ hτ x hx ↦ ?_, fun τ hτ x hx ↦ ?_⟩
  · rw [hu hτ, ← (hrates τ hτ).2.1]
    exact h.1 hτ hx
  · rw [hu hτ, ← (hrates τ hτ).2.2]
    exact h.2 hτ hx

/-! ### Reflection across the initial time -/

/-- The fields with vorticity and temperature reflected across `τ = 0` to first order
(`PDE.Analysis.reflectTimeZero`); the stream function is unchanged. They agree with `F` at
nonnegative times. -/
def VorticityStreamFields.reflectTimeZero (F : VorticityStreamFields) : VorticityStreamFields where
  vorticity := PDE.Analysis.reflectTimeZero F.vorticity
  temperature := PDE.Analysis.reflectTimeZero F.temperature
  streamFunction := F.streamFunction

/-- The reflected vorticity agrees with the vorticity at nonnegative times. -/
theorem VorticityStreamFields.reflectTimeZero_vorticity (F : VorticityStreamFields) {τ : ℝ}
    (hτ : 0 ≤ τ) (x : ℝ^2) : F.reflectTimeZero.vorticity x τ = F.vorticity x τ :=
  PDE.Analysis.reflectTimeZero_of_nonneg _ hτ

/-- The reflected temperature agrees with the temperature at nonnegative times. -/
theorem VorticityStreamFields.reflectTimeZero_temperature (F : VorticityStreamFields) {τ : ℝ}
    (hτ : 0 ≤ τ) (x : ℝ^2) : F.reflectTimeZero.temperature x τ = F.temperature x τ :=
  PDE.Analysis.reflectTimeZero_of_nonneg _ hτ

/-- On `[0, ∞)` the reflected fields solve the same rescaled equations. -/
theorem SatisfiesRescaledScalarEquationsOn.reflectTimeZero {F : VorticityStreamFields}
    {cl cω cθ : ℝ → ℝ} (hreg : HasClassicalVorticityStreamRegularityOn F (Ici 0))
    (h : SatisfiesRescaledScalarEquationsOn F cl cω cθ upperHalfPlane (Ici 0)) :
    SatisfiesRescaledScalarEquationsOn F.reflectTimeZero cl cω cθ upperHalfPlane (Ici 0) := by
  have hωd : DifferentiableOn ℝ (uncurry F.vorticity) (univ ×ˢ Ici 0) :=
    hreg.vorticity_contDiffOn.differentiableOn (by norm_num)
  have hθd : DifferentiableOn ℝ (uncurry F.temperature) (univ ×ˢ Ici 0) :=
    hreg.temperature_contDiffOn.differentiableOn (by norm_num)
  have hω (τ : ℝ) (hτ : 0 ≤ τ) :
      (fun y ↦ F.reflectTimeZero.vorticity y τ) = fun y ↦ F.vorticity y τ :=
    funext fun y ↦ F.reflectTimeZero_vorticity hτ y
  have hθ (τ : ℝ) (hτ : 0 ≤ τ) :
      (fun y ↦ F.reflectTimeZero.temperature y τ) = fun y ↦ F.temperature y τ :=
    funext fun y ↦ F.reflectTimeZero_temperature hτ y
  have hu (τ : ℝ) : (fun y ↦ rescaledTransportVelocity F.reflectTimeZero cl y τ) =
      fun y ↦ rescaledTransportVelocity F cl y τ := rfl
  refine ⟨fun τ hτ x hx ↦ ?_, fun τ hτ x hx ↦ ?_⟩
  · have hd : deriv (fun s ↦ F.reflectTimeZero.vorticity x s) τ =
        deriv (fun s ↦ F.vorticity x s) τ :=
      PDE.Analysis.deriv_reflectTimeZero hωd hτ (hreg.vorticity_differentiableAt_time hτ)
    rw [hd, hu, hω τ hτ, hθ τ hτ, F.reflectTimeZero_vorticity hτ]
    exact h.1 hτ hx
  · have hd : deriv (fun s ↦ F.reflectTimeZero.temperature x s) τ =
        deriv (fun s ↦ F.temperature x s) τ :=
      PDE.Analysis.deriv_reflectTimeZero hθd hτ (hreg.temperature_differentiableAt_time hτ)
    rw [hd, hu, hθ τ hτ, F.reflectTimeZero_temperature hτ]
    exact h.2 hτ hx

/-- **Undoing the dynamic rescaling of a solution on `[0, ∞)`.** A classical solution of the
rescaled system (2.8) with the rates `c_l`, `c_ω`, `c_l + 2 c_ω` on `[0, ∞)`, with the Poisson
equation and the Dirichlet condition, gives, after reflecting the vorticity and the temperature
across `τ = 0`, a classical solution of the physical system on `t([0, ∞))`, with ordinary time
derivatives at `t = 0`. -/
theorem isClassicalVorticityStreamSolutionOn_reconstructedFields_reflectTimeZero
    {l₀ : ℝ} (hl₀ : 0 < l₀) {cl cω : ℝ → ℝ} (hcl : Continuous cl) (hcω : Continuous cω)
    {R : VorticityStreamFields}
    (hreg : HasClassicalVorticityStreamRegularityOn R (Ici 0))
    (hequations : SatisfiesRescaledScalarEquationsOn R cl cω (fun τ ↦ cl τ + 2 * cω τ)
      upperHalfPlane (Ici 0))
    (hstream : SatisfiesStreamFunctionEquationOn R (Ici 0))
    (hboundary : HasZeroStreamFunctionBoundaryOn R (Ici 0)) :
    IsClassicalVorticityStreamSolutionOn (reconstructedFields (ofRates l₀ cl cω) R.reflectTimeZero)
      ((ofRates l₀ cl cω).physicalTime '' Ici 0) := by
  have hωd : DifferentiableOn ℝ (uncurry R.vorticity) (univ ×ˢ Ici 0) :=
    hreg.vorticity_contDiffOn.differentiableOn (by norm_num)
  have hθd : DifferentiableOn ℝ (uncurry R.temperature) (univ ×ˢ Ici 0) :=
    hreg.temperature_contDiffOn.differentiableOn (by norm_num)
  refine isClassicalVorticityStreamSolutionOn_reconstructedFields hl₀ hcl hcω
    (PDE.Analysis.contDiffOn_reflectTimeZero hreg.vorticity_contDiffOn)
    (PDE.Analysis.contDiffOn_reflectTimeZero hreg.temperature_contDiffOn)
    (fun τ hτ x ↦ PDE.Analysis.differentiableAt_reflectTimeZero hωd hτ)
    (fun τ hτ x ↦ PDE.Analysis.differentiableAt_reflectTimeZero hθd hτ)
    (fun τ hτ ↦ hreg.streamFunction_spatial_contDiff hτ)
    (hequations.reflectTimeZero hreg) ?_ hboundary
  intro x τ hx hτ
  rw [R.reflectTimeZero_vorticity hτ]
  exact hstream hx hτ

/-- At nonnegative rescaled times the reconstructed fields of the reflected fields are those of
the fields. -/
theorem reconstructedFields_reflectTimeZero_vorticity (data : DynamicRescalingData)
    (R : VorticityStreamFields) {t : ℝ} (ht : 0 ≤ data.rescaledTime t) (y : ℝ^2) :
    (reconstructedFields data R.reflectTimeZero).vorticity y t =
      (reconstructedFields data R).vorticity y t := by
  simp only [reconstructedFields, R.reflectTimeZero_vorticity ht]

/-- At nonnegative rescaled times the reconstructed temperature of the reflected fields is that
of the fields. -/
theorem reconstructedFields_reflectTimeZero_temperature (data : DynamicRescalingData)
    (R : VorticityStreamFields) {t : ℝ} (ht : 0 ≤ data.rescaledTime t) (y : ℝ^2) :
    (reconstructedFields data R.reflectTimeZero).temperature y t =
      (reconstructedFields data R).temperature y t := by
  simp only [reconstructedFields, R.reflectTimeZero_temperature ht]

/-! ### Norms of the reconstructed fields -/

/-- A positive dilation permutes the upper half-plane, so it does not change a supremum over it. -/
theorem iSup_upperHalfPlane_smul (g : ℝ^2 → ℝ≥0∞) {a : ℝ} (ha : 0 < a) :
    ⨆ y ∈ upperHalfPlane, g (a • y) = ⨆ x ∈ upperHalfPlane, g x := by
  have hmem {b : ℝ} (hb : 0 < b) {y : ℝ^2} (hy : y ∈ upperHalfPlane) :
      b • y ∈ upperHalfPlane := by
    change 0 < (b • y) 1
    simpa using mul_pos hb hy
  apply le_antisymm
  · exact iSup₂_le fun y hy ↦ le_iSup₂_of_le (a • y) (hmem ha hy) le_rfl
  · refine iSup₂_le fun x hx ↦ le_iSup₂_of_le (a⁻¹ • x) (hmem (inv_pos.2 ha) hx) ?_
    rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]

/-- The physical sup norm of the reconstructed vorticity over the upper half-plane is
`C_ω(τ)⁻¹` times the rescaled sup norm at `τ = t⁻¹(t)`, for positive scales. -/
theorem iSup_reconstructedFields_vorticity (data : DynamicRescalingData)
    (R : VorticityStreamFields) (t : ℝ) (hA : 0 < data.vorticityScale (data.rescaledTime t))
    (hL : 0 < data.spatialScale (data.rescaledTime t)) :
    ⨆ y ∈ upperHalfPlane, ‖(reconstructedFields data R).vorticity y t‖ₑ =
      ENNReal.ofReal (data.vorticityScale (data.rescaledTime t))⁻¹ *
        ⨆ x ∈ upperHalfPlane, ‖R.vorticity x (data.rescaledTime t)‖ₑ := by
  simp only [reconstructedFields, enorm_mul]
  rw [Real.enorm_eq_ofReal (inv_pos.2 hA).le, ENNReal.mul_iSup]
  simp_rw [ENNReal.mul_iSup]
  exact iSup_upperHalfPlane_smul
    (fun x ↦ ENNReal.ofReal (data.vorticityScale (data.rescaledTime t))⁻¹ *
      ‖R.vorticity x (data.rescaledTime t)‖ₑ) (inv_pos.2 hL)

/-- The reconstructed vorticity slice inherits the regularity of the rescaled slice on the closed
upper half-plane, which the dilation preserves. -/
theorem contDiffOn_reconstructedFields_vorticity (data : DynamicRescalingData)
    (R : VorticityStreamFields) {n : WithTop ℕ∞} (t : ℝ)
    (hL : 0 < data.spatialScale (data.rescaledTime t))
    (h : ContDiffOn ℝ n (fun x ↦ R.vorticity x (data.rescaledTime t)) {x | 0 ≤ x 1}) :
    ContDiffOn ℝ n (fun y ↦ (reconstructedFields data R).vorticity y t) {x | 0 ≤ x 1} := by
  refine contDiffOn_const.mul (h.comp (contDiff_const_smul _).contDiffOn fun y hy ↦ ?_)
  change 0 ≤ ((data.spatialScale (data.rescaledTime t))⁻¹ • y) 1
  simpa using mul_nonneg (inv_pos.2 hL).le hy

/-- The reconstructed temperature slice inherits the regularity of the rescaled slice on the
closed upper half-plane. -/
theorem contDiffOn_reconstructedFields_temperature (data : DynamicRescalingData)
    (R : VorticityStreamFields) {n : WithTop ℕ∞} (t : ℝ)
    (hL : 0 < data.spatialScale (data.rescaledTime t))
    (h : ContDiffOn ℝ n (fun x ↦ R.temperature x (data.rescaledTime t)) {x | 0 ≤ x 1}) :
    ContDiffOn ℝ n (fun y ↦ (reconstructedFields data R).temperature y t) {x | 0 ≤ x 1} := by
  refine contDiffOn_const.mul (h.comp (contDiff_const_smul _).contDiffOn fun y hy ↦ ?_)
  change 0 ≤ ((data.spatialScale (data.rescaledTime t))⁻¹ • y) 1
  simpa using mul_nonneg (inv_pos.2 hL).le hy

/-- The reconstructed velocity is `C_l C_ω⁻¹` times the rescaled velocity at the rescaled point. -/
theorem vorticityStreamVelocity_reconstructedFields (data : DynamicRescalingData)
    (R : VorticityStreamFields) (y : ℝ^2) (t : ℝ)
    (hL : data.spatialScale (data.rescaledTime t) ≠ 0)
    (hψ : DifferentiableAt ℝ (fun x ↦ R.streamFunction x (data.rescaledTime t))
      ((data.spatialScale (data.rescaledTime t))⁻¹ • y)) :
    vorticityStreamVelocity (reconstructedFields data R) y t =
      (data.spatialScale (data.rescaledTime t) / data.vorticityScale (data.rescaledTime t)) •
        vorticityStreamVelocity R ((data.spatialScale (data.rescaledTime t))⁻¹ • y)
          (data.rescaledTime t) := by
  change planarStreamVelocity (fun y ↦ _ * R.streamFunction (_ • y) _) y = _
  rw [planarStreamVelocity_const_smul_comp_smul _ _ _ y hψ]
  congr 1
  field_simp

/-- Square integrability of the velocity over the upper half-plane transfers from the rescaled
fields to the reconstructed fields, for `C¹` rescaled stream slices and positive scales. -/
theorem memLp_vorticityStreamVelocity_reconstructedFields (data : DynamicRescalingData)
    (R : VorticityStreamFields) (t : ℝ) (hL : 0 < data.spatialScale (data.rescaledTime t))
    (hψ : ContDiff ℝ 2 (fun x ↦ R.streamFunction x (data.rescaledTime t)))
    (hR : MemLp (fun x ↦ vorticityStreamVelocity R x (data.rescaledTime t)) 2
      (volume.restrict upperHalfPlane)) :
    MemLp (fun y ↦ vorticityStreamVelocity (reconstructedFields data R) y t) 2
      (volume.restrict upperHalfPlane) := by
  set a := (data.spatialScale (data.rescaledTime t))⁻¹
  set c := data.spatialScale (data.rescaledTime t) / data.vorticityScale (data.rescaledTime t)
  set u := fun x ↦ vorticityStreamVelocity R x (data.rescaledTime t)
  have hu : Continuous u := (contDiff_planarStreamVelocity _ hψ).continuous
  have heq : (fun y ↦ vorticityStreamVelocity (reconstructedFields data R) y t) =
      fun y ↦ c • u (a • y) := funext fun y ↦
    vorticityStreamVelocity_reconstructedFields data R y t hL.ne'
      ((hψ.differentiable (by norm_num)) _)
  rw [heq]
  have hcont : Continuous fun y : ℝ^2 ↦ c • u (a • y) :=
    (hu.comp (continuous_const_smul a)).const_smul c
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  rw [memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable] at hR
  have hmem (x : ℝ^2) : a • x ∈ upperHalfPlane ↔ x ∈ upperHalfPlane := by
    change 0 < (a • x) 1 ↔ 0 < x 1
    simp only [PiLp.smul_apply, smul_eq_mul]
    exact mul_pos_iff_of_pos_left (inv_pos.2 hL)
  have hind : upperHalfPlane.indicator (fun y ↦ ‖u (a • y)‖ ^ 2) =
      fun y ↦ upperHalfPlane.indicator (fun x ↦ ‖u x‖ ^ 2) (a • y) := by
    funext y
    by_cases hy : y ∈ upperHalfPlane
    · rw [indicator_of_mem hy, indicator_of_mem ((hmem y).2 hy)]
    · rw [indicator_of_notMem hy, indicator_of_notMem (fun h ↦ hy ((hmem y).1 h))]
  have hmeas : MeasurableSet upperHalfPlane := isOpen_upperHalfPlane.measurableSet
  have hcomp : Integrable (fun y ↦ ‖u (a • y)‖ ^ 2) (volume.restrict upperHalfPlane) := by
    change IntegrableOn _ upperHalfPlane
    rw [← integrable_indicator_iff hmeas, hind]
    exact ((integrable_indicator_iff hmeas).2 hR).comp_smul (inv_pos.2 hL).ne'
  simpa only [norm_smul, mul_pow] using hcomp.const_mul (‖c‖ ^ 2)

end Boussinesq
