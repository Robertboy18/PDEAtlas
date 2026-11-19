/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.VorticityStream.DynamicRescaling.Basic
public import PDE.Analysis.Evolution.ODE.ReciprocalClock
import PDE.Analysis.Evolution.Core.FiniteTimeBlowup

/-!
# The scales and the clock of a dynamic rescaling from its rates

Given continuous rates `c_l` and `c_ω` on `ℝ`, the scales of the dynamic rescaling are

```text
C_ω(τ) = exp ∫₀^τ c_ω,   C_l(τ) = l₀ exp(-∫₀^τ c_l),
C_θ(τ) = l₀⁻¹ exp ∫₀^τ (c_l + 2 c_ω),
t(τ) = ∫₀^τ C_ω,
```

with `c_θ = c_l + 2 c_ω` and an initial spatial scale `l₀ > 0`. `ofRates l₀ cl cω` is this
rescaling; the Boussinesq argument uses `l₀ = 1`, the Euler wall rescaling a small
`l₀ = C_l(0)`. The fundamental theorem of calculus gives the scale laws
`SatisfiesDynamicRescalingLawsAt` at every rescaled time, including the source compatibility
`C_θ C_l = C_ω²`. All scales are positive, so the clock `t` is strictly
increasing; `rescaledTime` is its inverse, differentiable on the range of the clock with
derivative `1 / C_ω`, and continuously differentiable there.

If `c_ω ≤ -γ < 0` on `[0, ∞)`, the amplitude `C_ω` decays exponentially, the lifetime
`T = ∫₀^∞ C_ω` is finite and positive, the clock maps `[0, ∞)` onto `[0, T)`, and
`C_ω(t⁻¹(s))⁻¹ → ∞` as `s → T⁻`. These are the scales (2.6) of Chen and Hou, Part I, and the
blowup time `T = t(∞)` of their Section 2.2; Section 5.9.4 passes from stability of the rescaled
solution to finite time blowup through them. Only rates on `[0, ∞)` are meaningful for a
solution; continuous rates on `[0, ∞)` extend to continuous rates on `ℝ` by `τ ↦ c(max τ 0)`.

## Main results

* `satisfiesDynamicRescalingLawsAt_ofRates`: the scale laws at every time.
* `rescaledTime_ofRates_physicalTime`, `physicalTime_rescaledTime`: the clock and its
  inverse.
* `rescaledTime_ofRates_hasStrictDerivAt`, `contDiffOn_rescaledTime_ofRates`: regularity of the
  inverse clock on the open range of the clock.
* `lifetime_ofRates_pos`, `physicalTime_ofRates_image_Ici`,
  `tendsto_inv_vorticityScale_rescaledTime_ofRates`: the finite lifetime and the growth of the
  physical amplitude.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 2.1, (2.6)-(2.7),
  Section 2.2, pp. 6-7, and Section 5.9.4, p. 93.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open Filter Set MeasureTheory
open scoped Topology

namespace Boussinesq.DynamicRescalingData

set_option linter.missingDocs true

/-- The dynamic rescaling with initial spatial scale `l₀`, unit initial vorticity scale,
initial temperature scale `l₀⁻¹` (so that `C_θ C_l = C_ω²`), zero initial physical time and the
rates `c_l`, `c_ω` and `c_θ = c_l + 2 c_ω`. -/
def ofRates (l₀ : ℝ) (cl cω : ℝ → ℝ) : DynamicRescalingData where
  vorticityScale τ := Real.exp (∫ s in (0 : ℝ)..τ, cω s)
  spatialScale τ := l₀ * Real.exp (-∫ s in (0 : ℝ)..τ, cl s)
  temperatureScale τ := Real.exp (∫ s in (0 : ℝ)..τ, (cl s + 2 * cω s)) / l₀
  physicalTime τ := ∫ s in (0 : ℝ)..τ, Real.exp (∫ r in (0 : ℝ)..s, cω r)
  vorticityRate := cω
  spatialRate := cl
  temperatureRate τ := cl τ + 2 * cω τ

/-- The vorticity scale of `ofRates` is `exp ∫₀^τ c_ω`. -/
theorem ofRates_vorticityScale (l₀ : ℝ) (cl cω : ℝ → ℝ) (τ : ℝ) :
    (ofRates l₀ cl cω).vorticityScale τ = Real.exp (∫ s in (0 : ℝ)..τ, cω s) := rfl

/-- The spatial scale of `ofRates` is `l₀ exp(-∫₀^τ c_l)`. -/
theorem ofRates_spatialScale (l₀ : ℝ) (cl cω : ℝ → ℝ) (τ : ℝ) :
    (ofRates l₀ cl cω).spatialScale τ = l₀ * Real.exp (-∫ s in (0 : ℝ)..τ, cl s) := rfl

/-- The temperature scale of `ofRates` is `l₀⁻¹ exp ∫₀^τ (c_l + 2 c_ω)`. -/
theorem ofRates_temperatureScale (l₀ : ℝ) (cl cω : ℝ → ℝ) (τ : ℝ) :
    (ofRates l₀ cl cω).temperatureScale τ =
      Real.exp (∫ s in (0 : ℝ)..τ, (cl s + 2 * cω s)) / l₀ := rfl

/-- The vorticity rate of `ofRates` is `c_ω`. -/
theorem ofRates_vorticityRate (l₀ : ℝ) (cl cω : ℝ → ℝ) :
    (ofRates l₀ cl cω).vorticityRate = cω := rfl

/-- The spatial rate of `ofRates` is `c_l`. -/
theorem ofRates_spatialRate (l₀ : ℝ) (cl cω : ℝ → ℝ) :
    (ofRates l₀ cl cω).spatialRate = cl := rfl

/-- The temperature rate of `ofRates` is `c_l + 2 c_ω`. -/
theorem ofRates_temperatureRate (l₀ : ℝ) (cl cω : ℝ → ℝ) (τ : ℝ) :
    (ofRates l₀ cl cω).temperatureRate τ = cl τ + 2 * cω τ := rfl

/-- The vorticity scale of `ofRates` is positive. -/
theorem vorticityScale_ofRates_pos {l₀ : ℝ} (cl cω : ℝ → ℝ) (τ : ℝ) :
    0 < (ofRates l₀ cl cω).vorticityScale τ :=
  Real.exp_pos _

/-- The spatial scale of `ofRates` is positive. -/
theorem spatialScale_ofRates_pos {l₀ : ℝ} (hl₀ : 0 < l₀) (cl cω : ℝ → ℝ) (τ : ℝ) :
    0 < (ofRates l₀ cl cω).spatialScale τ :=
  mul_pos hl₀ (Real.exp_pos _)

/-- The temperature scale of `ofRates` is positive. -/
theorem temperatureScale_ofRates_pos {l₀ : ℝ} (hl₀ : 0 < l₀) (cl cω : ℝ → ℝ) (τ : ℝ) :
    0 < (ofRates l₀ cl cω).temperatureScale τ :=
  div_pos (Real.exp_pos _) hl₀

/-- The initial vorticity scale is one. -/
@[simp]
theorem vorticityScale_ofRates_zero (l₀ : ℝ) (cl cω : ℝ → ℝ) :
    (ofRates l₀ cl cω).vorticityScale 0 = 1 := by
  simp [ofRates]

/-- The initial spatial scale is `l₀`. -/
@[simp]
theorem spatialScale_ofRates_zero (l₀ : ℝ) (cl cω : ℝ → ℝ) :
    (ofRates l₀ cl cω).spatialScale 0 = l₀ := by
  simp [ofRates]

/-- The initial temperature scale is `l₀⁻¹`. -/
@[simp]
theorem temperatureScale_ofRates_zero (l₀ : ℝ) (cl cω : ℝ → ℝ) :
    (ofRates l₀ cl cω).temperatureScale 0 = l₀⁻¹ := by
  simp [ofRates]

/-- The clock starts at zero. -/
@[simp]
theorem physicalTime_ofRates_zero (l₀ : ℝ) (cl cω : ℝ → ℝ) :
    (ofRates l₀ cl cω).physicalTime 0 = 0 := by
  simp [ofRates]

variable {l₀ : ℝ}

/-- The vorticity scale of `ofRates` is continuous for continuous `c_ω`. -/
theorem continuous_vorticityScale_ofRates (cl : ℝ → ℝ) {cω : ℝ → ℝ} (hcω : Continuous cω) :
    Continuous (ofRates l₀ cl cω).vorticityScale :=
  Real.continuous_exp.comp (intervalIntegral.differentiable_integral_of_continuous hcω).continuous

/-- The clock has strict derivative `C_ω(τ)` at every time. -/
theorem physicalTime_ofRates_hasStrictDerivAt (cl : ℝ → ℝ) {cω : ℝ → ℝ} (hcω : Continuous cω)
    (τ : ℝ) :
    HasStrictDerivAt (ofRates l₀ cl cω).physicalTime ((ofRates l₀ cl cω).vorticityScale τ) τ := by
  have hscale := continuous_vorticityScale_ofRates (l₀ := l₀) cl hcω
  exact hscale.integral_hasStrictDerivAt 0 τ

/-- The vorticity scale obeys `C_ω' = c_ω C_ω`. -/
theorem hasDerivAt_vorticityScale_ofRates (cl : ℝ → ℝ) {cω : ℝ → ℝ} (hcω : Continuous cω)
    (τ : ℝ) :
    HasDerivAt (ofRates l₀ cl cω).vorticityScale
      (cω τ * (ofRates l₀ cl cω).vorticityScale τ) τ := by
  simpa only [ofRates, mul_comm] using (hcω.integral_hasStrictDerivAt 0 τ).hasDerivAt.exp

/-- The spatial scale obeys `C_l' = -c_l C_l`. -/
theorem hasDerivAt_spatialScale_ofRates {cl : ℝ → ℝ} (cω : ℝ → ℝ) (hcl : Continuous cl)
    (τ : ℝ) :
    HasDerivAt (ofRates l₀ cl cω).spatialScale
      (-cl τ * (ofRates l₀ cl cω).spatialScale τ) τ := by
  have h : HasDerivAt (fun u ↦ -∫ s in (0 : ℝ)..u, cl s) (-cl τ) τ :=
    (hcl.integral_hasStrictDerivAt 0 τ).hasDerivAt.neg
  exact (h.exp.const_mul l₀).congr_deriv (by
    simp only [ofRates_spatialScale]
    ring)

/-- The temperature scale obeys `C_θ' = (c_l + 2 c_ω) C_θ`. -/
theorem hasDerivAt_temperatureScale_ofRates {cl cω : ℝ → ℝ} (hcl : Continuous cl)
    (hcω : Continuous cω) (τ : ℝ) :
    HasDerivAt (ofRates l₀ cl cω).temperatureScale
      ((cl τ + 2 * cω τ) * (ofRates l₀ cl cω).temperatureScale τ) τ := by
  have h := (Continuous.integral_hasStrictDerivAt (f := fun s ↦ cl s + 2 * cω s)
    (hcl.add (continuous_const.mul hcω)) 0 τ).hasDerivAt
  exact (h.exp.div_const l₀).congr_deriv (by
    simp only [ofRates_temperatureScale]
    ring)

/-- Continuous rates and a positive initial spatial scale give the scale laws of the dynamic
rescaling at every time: the three scale ODEs, the clock ODE `t' = C_ω`, a positive spatial
scale, `C_θ C_l = C_ω²` and `c_θ = c_l + 2 c_ω`. -/
theorem satisfiesDynamicRescalingLawsAt_ofRates (hl₀ : 0 < l₀) {cl cω : ℝ → ℝ}
    (hcl : Continuous cl) (hcω : Continuous cω) (τ : ℝ) :
    SatisfiesDynamicRescalingLawsAt (ofRates l₀ cl cω) τ where
  vorticityScale_hasDerivAt := hasDerivAt_vorticityScale_ofRates cl hcω τ
  spatialScale_hasDerivAt := hasDerivAt_spatialScale_ofRates cω hcl τ
  temperatureScale_hasDerivAt := hasDerivAt_temperatureScale_ofRates hcl hcω τ
  physicalTime_hasDerivAt := (physicalTime_ofRates_hasStrictDerivAt cl hcω τ).hasDerivAt
  spatialScale_pos := spatialScale_ofRates_pos hl₀ cl cω τ
  sourceScale_eq := by
    rw [ofRates_temperatureScale, ofRates_spatialScale, ofRates_vorticityScale,
      show ∀ a b : ℝ, a / l₀ * (l₀ * b) = a * b from fun a b ↦ by field_simp,
      ← Real.exp_add, ← Real.exp_nat_mul, intervalIntegral.integral_add (f := cl)
      (g := fun s ↦ 2 * cω s) (hcl.intervalIntegrable _ _)
      ((continuous_const.mul hcω).intervalIntegrable _ _), intervalIntegral.integral_const_mul]
    congr 1
    push_cast
    ring
  temperatureRate_eq := rfl

/-- The clock of `ofRates` is strictly increasing. -/
theorem physicalTime_ofRates_strictMono (cl : ℝ → ℝ) {cω : ℝ → ℝ} (hcω : Continuous cω) :
    StrictMono (ofRates l₀ cl cω).physicalTime :=
  strictMono_of_hasDerivAt_pos (fun τ ↦ (physicalTime_ofRates_hasStrictDerivAt cl hcω τ).hasDerivAt)
    (vorticityScale_ofRates_pos cl cω)

/-- The range of the clock of `ofRates` is open. -/
theorem isOpen_range_physicalTime_ofRates (cl : ℝ → ℝ) {cω : ℝ → ℝ} (hcω : Continuous cω) :
    IsOpen (range (ofRates l₀ cl cω).physicalTime) :=
  PDE.Analysis.Evolution.ODE.isOpen_range_of_hasStrictDerivAt_pos
    (physicalTime_ofRates_hasStrictDerivAt cl hcω) (vorticityScale_ofRates_pos cl cω)

/-- Rescaled time as a function of physical time: the inverse of the clock. Its values off the
range of the clock are unspecified. -/
def rescaledTime (data : DynamicRescalingData) : ℝ → ℝ :=
  Function.invFun data.physicalTime

/-- The inverse clock recovers every rescaled time. -/
@[simp]
theorem rescaledTime_ofRates_physicalTime (cl : ℝ → ℝ) {cω : ℝ → ℝ} (hcω : Continuous cω)
    (τ : ℝ) : (ofRates l₀ cl cω).rescaledTime ((ofRates l₀ cl cω).physicalTime τ) = τ :=
  PDE.Analysis.Evolution.ODE.leftInverse_invFun_of_hasDerivAt_pos
    (fun s ↦ (physicalTime_ofRates_hasStrictDerivAt cl hcω s).hasDerivAt)
    (vorticityScale_ofRates_pos cl cω) τ

/-- On the range of the clock, the clock of the inverse clock is the identity. -/
theorem physicalTime_rescaledTime {data : DynamicRescalingData} {t : ℝ}
    (ht : t ∈ range data.physicalTime) : data.physicalTime (data.rescaledTime t) = t :=
  Function.invFun_eq ht

/-- The inverse clock starts at zero. -/
@[simp]
theorem rescaledTime_ofRates_zero (cl : ℝ → ℝ) {cω : ℝ → ℝ} (hcω : Continuous cω) :
    (ofRates l₀ cl cω).rescaledTime 0 = 0 := by
  simpa only [physicalTime_ofRates_zero] using rescaledTime_ofRates_physicalTime cl hcω 0

/-- The inverse clock has strict derivative `C_ω(τ)⁻¹` at `t(τ)`. -/
theorem rescaledTime_ofRates_hasStrictDerivAt (cl : ℝ → ℝ) {cω : ℝ → ℝ} (hcω : Continuous cω)
    (τ : ℝ) :
    HasStrictDerivAt (ofRates l₀ cl cω).rescaledTime ((ofRates l₀ cl cω).vorticityScale τ)⁻¹
      ((ofRates l₀ cl cω).physicalTime τ) :=
  PDE.Analysis.Evolution.ODE.hasStrictDerivAt_invFun_of_hasStrictDerivAt_pos
    (physicalTime_ofRates_hasStrictDerivAt cl hcω) (vorticityScale_ofRates_pos cl cω) τ

/-- The inverse clock is differentiable on the range of the clock. -/
theorem differentiableOn_rescaledTime_ofRates (cl : ℝ → ℝ) {cω : ℝ → ℝ} (hcω : Continuous cω) :
    DifferentiableOn ℝ (ofRates l₀ cl cω).rescaledTime (range (ofRates l₀ cl cω).physicalTime) := by
  rintro _ ⟨τ, rfl⟩
  exact (rescaledTime_ofRates_hasStrictDerivAt cl hcω τ).hasDerivAt.differentiableAt
    |>.differentiableWithinAt

/-- The inverse clock is continuously differentiable on the range of the clock. -/
theorem contDiffOn_rescaledTime_ofRates (cl : ℝ → ℝ) {cω : ℝ → ℝ} (hcω : Continuous cω) :
    ContDiffOn ℝ 1 (ofRates l₀ cl cω).rescaledTime (range (ofRates l₀ cl cω).physicalTime) :=
  PDE.Analysis.Evolution.ODE.contDiffOn_invFun_of_hasStrictDerivAt_pos
    (physicalTime_ofRates_hasStrictDerivAt cl hcω) (vorticityScale_ofRates_pos cl cω)
    (continuous_vorticityScale_ofRates cl hcω)

/-- The spatial scale of `ofRates` is continuously differentiable for a continuous rate. -/
theorem contDiff_spatialScale_ofRates {cl : ℝ → ℝ} (cω : ℝ → ℝ) (hcl : Continuous cl) :
    ContDiff ℝ 1 (ofRates l₀ cl cω).spatialScale := by
  rw [contDiff_one_iff_deriv]
  have hd := hasDerivAt_spatialScale_ofRates (l₀ := l₀) cω hcl
  refine ⟨fun τ ↦ (hd τ).differentiableAt, ?_⟩
  rw [show deriv (ofRates l₀ cl cω).spatialScale =
      fun τ ↦ -cl τ * (ofRates l₀ cl cω).spatialScale τ from funext fun τ ↦ (hd τ).deriv]
  exact (hcl.neg).mul (continuous_iff_continuousAt.2 fun τ ↦ (hd τ).continuousAt)

/-- The vorticity scale of `ofRates` is continuously differentiable for a continuous rate. -/
theorem contDiff_vorticityScale_ofRates (cl : ℝ → ℝ) {cω : ℝ → ℝ} (hcω : Continuous cω) :
    ContDiff ℝ 1 (ofRates l₀ cl cω).vorticityScale := by
  rw [contDiff_one_iff_deriv]
  have hd := hasDerivAt_vorticityScale_ofRates (l₀ := l₀) cl hcω
  refine ⟨fun τ ↦ (hd τ).differentiableAt, ?_⟩
  rw [show deriv (ofRates l₀ cl cω).vorticityScale =
      fun τ ↦ cω τ * (ofRates l₀ cl cω).vorticityScale τ from funext fun τ ↦ (hd τ).deriv]
  exact hcω.mul (continuous_vorticityScale_ofRates cl hcω)

/-- The temperature scale of `ofRates` is continuously differentiable for continuous rates. -/
theorem contDiff_temperatureScale_ofRates {cl cω : ℝ → ℝ} (hcl : Continuous cl)
    (hcω : Continuous cω) : ContDiff ℝ 1 (ofRates l₀ cl cω).temperatureScale := by
  rw [contDiff_one_iff_deriv]
  have hd := hasDerivAt_temperatureScale_ofRates (l₀ := l₀) hcl hcω
  refine ⟨fun τ ↦ (hd τ).differentiableAt, ?_⟩
  rw [show deriv (ofRates l₀ cl cω).temperatureScale =
      fun τ ↦ (cl τ + 2 * cω τ) * (ofRates l₀ cl cω).temperatureScale τ from
    funext fun τ ↦ (hd τ).deriv]
  exact (hcl.add (continuous_const.mul hcω)).mul
    (continuous_iff_continuousAt.2 fun τ ↦ (hd τ).continuousAt)

/-! ### The lifetime -/

/-- The physical lifetime `T = ∫₀^∞ C_ω` of the forward rescaled trajectory. -/
def lifetime (data : DynamicRescalingData) : ℝ :=
  ∫ τ in Ioi (0 : ℝ), data.vorticityScale τ

section Lifetime

variable {cl cω : ℝ → ℝ} {γ : ℝ}

/-- The reciprocal `C_ω⁻¹` obeys `(C_ω⁻¹)' = -c_ω C_ω⁻¹`, the sign convention of the general
reciprocal clock. -/
private theorem hasDerivAt_inv_vorticityScale (hcω : Continuous cω) (τ : ℝ) :
    HasDerivAt (fun s ↦ ((ofRates l₀ cl cω).vorticityScale s)⁻¹)
      (-cω τ * ((ofRates l₀ cl cω).vorticityScale τ)⁻¹) τ := by
  have h := hasDerivAt_vorticityScale_ofRates (l₀ := l₀) cl hcω τ
  have hne := (vorticityScale_ofRates_pos (l₀ := l₀) cl cω τ).ne'
  convert h.inv hne using 1
  field_simp

variable (hcω : Continuous cω) (hγ : 0 < γ) (hrate : ∀ τ ∈ Ici (0 : ℝ), cω τ ≤ -γ)
include hcω hγ hrate

/-- A uniformly negative vorticity rate makes the amplitude `C_ω` integrable on `(0, ∞)`. -/
theorem integrableOn_vorticityScale_ofRates :
    IntegrableOn (ofRates l₀ cl cω).vorticityScale (Ioi (0 : ℝ)) := by
  simpa only [inv_inv] using PDE.Analysis.Evolution.ODE.integrableOn_reciprocal_amplitude
    (fun s ↦ ((ofRates l₀ cl cω).vorticityScale s)⁻¹) cω γ (by simp)
    (fun τ _ ↦ hasDerivAt_inv_vorticityScale hcω τ) hrate hγ

/-- The lifetime is positive. -/
theorem lifetime_ofRates_pos : 0 < (ofRates l₀ cl cω).lifetime := by
  simpa only [lifetime, inv_inv] using PDE.Analysis.Evolution.ODE.reciprocal_amplitude_tail_pos
    (fun s ↦ ((ofRates l₀ cl cω).vorticityScale s)⁻¹) cω γ (by simp)
    (fun τ _ ↦ hasDerivAt_inv_vorticityScale hcω τ) hrate hγ le_rfl

/-- The clock maps `[0, ∞)` onto `[0, T)`. -/
theorem physicalTime_ofRates_image_Ici :
    (ofRates l₀ cl cω).physicalTime '' Ici 0 = Ico 0 (ofRates l₀ cl cω).lifetime := by
  have h := PDE.Analysis.Evolution.ODE.image_reciprocal_clock_Ici
    (fun s ↦ ((ofRates l₀ cl cω).vorticityScale s)⁻¹) cω γ (by simp)
    (fun τ _ ↦ hasDerivAt_inv_vorticityScale hcω τ) hrate hγ
  simp only [inv_inv] at h
  exact h

/-- The physical amplitude `C_ω⁻¹` tends to infinity along the forward rescaled times. -/
theorem tendsto_inv_vorticityScale_ofRates :
    Tendsto (fun τ ↦ ((ofRates l₀ cl cω).vorticityScale τ)⁻¹) atTop atTop :=
  PDE.Analysis.Evolution.ODE.amplitude_scale_tendsto_atTop
    (fun s ↦ ((ofRates l₀ cl cω).vorticityScale s)⁻¹) cω γ (by simp)
    (fun τ _ ↦ hasDerivAt_inv_vorticityScale hcω τ) hrate hγ

/-- A limit along the forward rescaled times is a left limit at the lifetime: if `u (t(τ)) → l`
as `τ → ∞`, then `u s → l` as `s → T⁻`. -/
theorem tendsto_nhdsLT_lifetime_ofRates {E : Type*} {l : Filter E} {u : ℝ → E}
    (hu : Tendsto (fun τ ↦ u ((ofRates l₀ cl cω).physicalTime τ)) atTop l) :
    Tendsto u (𝓝[<] (ofRates l₀ cl cω).lifetime) l :=
  PDE.Analysis.Evolution.tendsto_nhdsWithin_of_monotone_clock (initialTime := 0)
    ((physicalTime_ofRates_strictMono cl hcω).monotone.monotoneOn _)
    (by simpa only [physicalTime_ofRates_zero] using
      physicalTime_ofRates_image_Ici hcω hγ hrate) hu

/-- The physical amplitude `C_ω(t⁻¹(s))⁻¹` tends to infinity as `s → T⁻`. -/
theorem tendsto_inv_vorticityScale_rescaledTime_ofRates :
    Tendsto (fun s ↦ ((ofRates l₀ cl cω).vorticityScale ((ofRates l₀ cl cω).rescaledTime s))⁻¹)
      (𝓝[<] (ofRates l₀ cl cω).lifetime) atTop := by
  apply tendsto_nhdsLT_lifetime_ofRates hcω hγ hrate
  simpa only [rescaledTime_ofRates_physicalTime cl hcω] using
    tendsto_inv_vorticityScale_ofRates hcω hγ hrate

end Lifetime

end Boussinesq.DynamicRescalingData
